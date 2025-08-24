# app.py
"""
Geo-Tagged Photo Taker (optimized capture)
- Keeps all features: signing, QR, EXIF, strip overlay, DB fallback, verification.
- Optimizations:
  * Geocode caching (SQLite + in-memory)
  * Reverse-geocode runs in background thread while CPU work (pHash) runs concurrently
  * Faster QR compression (zlib level reduced) and smaller QR box_size/border
  * pHash resize reduced (32->16) to speed DCT
  * requests.Session reuse, font caching
"""
from flask import Flask, render_template, request, jsonify, url_for, send_from_directory
from datetime import datetime, timezone, timedelta
import io, os, requests, base64, json, hashlib, zlib, sqlite3, threading, time
from PIL import Image, ImageDraw, ImageFont
import piexif
from piexif.helper import UserComment
from fractions import Fraction
from openlocationcode import openlocationcode as olc

# QR
import qrcode
from qrcode.constants import ERROR_CORRECT_M  # moderate error correction for smaller QR & speed

# OpenCV + numpy
import cv2
import numpy as np

# crypto
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, rsa, padding as asym_padding
from cryptography.exceptions import InvalidSignature

# ------------------ Config ------------------
app = Flask(__name__, static_folder="static", template_folder="templates")
OUTPUT_DIR = os.path.join(app.static_folder, "outputs")
DB_DIR = os.path.join(app.root_path, "data")
DB_FILE = os.path.join(DB_DIR, "geosig.db")
KEY_DIR = os.path.join(app.root_path, "keys")
PRIVATE_KEY_FILE = os.path.join(KEY_DIR, "private_key.pem")
PUBLIC_KEY_FILE = os.path.join(KEY_DIR, "public_key.pem")

os.makedirs(OUTPUT_DIR, exist_ok=True)
os.makedirs(DB_DIR, exist_ok=True)
os.makedirs(KEY_DIR, exist_ok=True)

NOMINATIM_EMAIL = os.environ.get("NOMINATIM_EMAIL", "youremail@example.com")

# Single requests session (reuses connections)
SESSION = requests.Session()

# ------------------ Key handling (auto: prefer ECDSA P-256) ------------------
def generate_and_store_keys():
    priv = ec.generate_private_key(ec.SECP256R1())
    priv_pem = priv.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption()
    )
    pub_pem = priv.public_key().public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    )
    with open(PRIVATE_KEY_FILE, "wb") as f:
        f.write(priv_pem)
    with open(PUBLIC_KEY_FILE, "wb") as f:
        f.write(pub_pem)
    return priv

def load_keys():
    if not (os.path.exists(PRIVATE_KEY_FILE) and os.path.exists(PUBLIC_KEY_FILE)):
        return generate_and_store_keys()
    with open(PRIVATE_KEY_FILE, "rb") as f:
        return serialization.load_pem_private_key(f.read(), password=None)

private_key = load_keys()
public_key = private_key.public_key()
PUB_DER = public_key.public_bytes(encoding=serialization.Encoding.DER,
                                  format=serialization.PublicFormat.SubjectPublicKeyInfo)
KID = hashlib.sha256(PUB_DER).hexdigest()[:16]

@app.get("/public_key.pem")
def public_key_route():
    if not os.path.exists(PUBLIC_KEY_FILE):
        pub_pem = public_key.public_bytes(encoding=serialization.Encoding.PEM,
                                          format=serialization.PublicFormat.SubjectPublicKeyInfo)
        with open(PUBLIC_KEY_FILE, "wb") as f:
            f.write(pub_pem)
    return send_from_directory(os.path.dirname(PUBLIC_KEY_FILE), os.path.basename(PUBLIC_KEY_FILE), as_attachment=True)

# ------------------ DB (sqlite) with geocode cache + migration ------------------
def init_db():
    con = sqlite3.connect(DB_FILE)
    cur = con.cursor()
    cur.execute("""
      CREATE TABLE IF NOT EXISTS images (
        id INTEGER PRIMARY KEY,
        filename TEXT,
        phash TEXT,
        strip_phash TEXT,
        payload TEXT,
        signature TEXT,
        ts TEXT
      )
    """)
    cur.execute("""
      CREATE TABLE IF NOT EXISTS geocode_cache (
        id INTEGER PRIMARY KEY,
        lat_r REAL,
        lon_r REAL,
        display TEXT,
        address_json TEXT,
        ts TEXT
      )
    """)
    cur.execute("CREATE INDEX IF NOT EXISTS idx_geo_latlon ON geocode_cache(lat_r, lon_r)")
    con.commit()
    con.close()

init_db()

# in-memory LRU-ish simple cache for small speed boost
_GEOCACHE_MEM = {}
_GEOCACHE_MEM_LOCK = threading.Lock()
_GEOCACHE_PRECISION = 5  # number of decimals to round for caching (≈1.1m at equator)

def _round_coords(lat, lon, precision=_GEOCACHE_PRECISION):
    return round(float(lat), precision), round(float(lon), precision)

def get_geocode_cache_db(lat, lon, precision=_GEOCACHE_PRECISION):
    lat_r, lon_r = _round_coords(lat, lon, precision)
    # check in-memory first
    key = (lat_r, lon_r)
    with _GEOCACHE_MEM_LOCK:
        if key in _GEOCACHE_MEM:
            return _GEOCACHE_MEM[key]
    # check SQLite
    con = sqlite3.connect(DB_FILE)
    cur = con.cursor()
    cur.execute("SELECT display, address_json FROM geocode_cache WHERE lat_r=? AND lon_r=? LIMIT 1", (lat_r, lon_r))
    row = cur.fetchone()
    con.close()
    if row:
        try:
            display = row[0]
            addr = json.loads(row[1]) if row[1] else {}
            with _GEOCACHE_MEM_LOCK:
                _GEOCACHE_MEM[key] = (display, addr)
            return display, addr
        except Exception:
            return None
    return None

def set_geocode_cache_db(lat, lon, display, address, precision=_GEOCACHE_PRECISION):
    lat_r, lon_r = _round_coords(lat, lon, precision)
    con = sqlite3.connect(DB_FILE)
    cur = con.cursor()
    cur.execute("INSERT INTO geocode_cache (lat_r, lon_r, display, address_json, ts) VALUES (?, ?, ?, ?, ?)",
                (lat_r, lon_r, display, json.dumps(address, separators=(",", ":")), datetime.utcnow().isoformat()))
    con.commit()
    con.close()
    with _GEOCACHE_MEM_LOCK:
        _GEOCACHE_MEM[(lat_r, lon_r)] = (display, address)

# ------------------ helpers: geocoding + exif ------------------
def _rat(x):
    f = Fraction(x).limit_denominator(1000000)
    return (f.numerator, f.denominator)

def _to_dms_rationals(dec):
    dec = float(dec)
    sign = 1 if dec >= 0 else -1
    dec = abs(dec)
    deg = int(dec)
    minutes_full = (dec - deg) * 60
    minute = int(minutes_full)
    second = (minutes_full - minute) * 60
    return [_rat(deg), _rat(minute), _rat(second)], sign

def make_gps_ifd(lat, lon, ts_utc):
    lat_dms, lat_sign = _to_dms_rationals(lat)
    lon_dms, lon_sign = _to_dms_rationals(lon)
    gps = {
        piexif.GPSIFD.GPSLatitudeRef: b"N" if lat_sign >= 0 else b"S",
        piexif.GPSIFD.GPSLatitude: lat_dms,
        piexif.GPSIFD.GPSLongitudeRef: b"E" if lon_sign >= 0 else b"W",
        piexif.GPSIFD.GPSLongitude: lon_dms,
    }
    ts = ts_utc.astimezone(timezone.utc)
    gps[piexif.GPSIFD.GPSTimeStamp] = [(ts.hour,1),(ts.minute,1),(int(ts.second),1)]
    gps[piexif.GPSIFD.GPSDateStamp] = ts.strftime("%Y:%m:%d")
    return gps

def format_offset(minutes_east):
    sign = "+" if minutes_east >= 0 else "-"
    m = abs(int(minutes_east))
    return f"GMT {sign}{m//60:02d}:{m%60:02d}"

def reverse_geocode(lat, lon, use_cache=True, precision=_GEOCACHE_PRECISION):
    """
    Return (display_name, address_dict) by querying Nominatim.
    If use_cache is True, attempt quick DB/in-memory cache first.
    """
    if use_cache:
        cached = get_geocode_cache_db(lat, lon, precision=precision)
        if cached:
            return cached

    try:
        headers = {"User-Agent": f"GeoTagPhotoApp/1.0 ({NOMINATIM_EMAIL})"}
        params = {"format": "jsonv2", "lat": lat, "lon": lon, "zoom": 18, "addressdetails": 1}
        # small timeout — this is the main latency source; caching avoids repeated calls
        r = SESSION.get("https://nominatim.openstreetmap.org/reverse", params=params, headers=headers, timeout=4)
        if r.ok:
            j = r.json()
            display = j.get("display_name")
            address = j.get("address", {})
            # store in cache for later (small DB write)
            try:
                set_geocode_cache_db(lat, lon, display or "", address, precision=precision)
            except Exception:
                pass
            return display, address
    except Exception:
        pass
    return None, {}

def pick_first(address, keys):
    for k in keys:
        v = address.get(k)
        if v:
            return v
    return None

def build_label_lines(lat, lon, tz_offset_min, ts_ms, address_override=None):
    """
    Build the label text lines. If address_override provided, use it (dict display_name, address)
    """
    if address_override:
        display_name, address = address_override
    else:
        display_name, address = reverse_geocode(lat, lon)

    city = pick_first(address, ["city","town","village"]) or ""
    state = address.get("state") or ""
    country = address.get("country") or ""
    title_line = ", ".join([x for x in [city, state, country] if x])

    house_num = address.get("house_number")
    sub_parts = []
    for k in ["suburb","neighbourhood","quarter","residential","borough","city_district","district","hamlet","locality"]:
        v = address.get(k)
        if v and v not in sub_parts and v != city:
            sub_parts.append(v)
    postcode = address.get("postcode") or ""
    plus_full = olc.encode(lat, lon, codeLength=10)
    plus_short = olc.shorten(plus_full, lat, lon).upper()

    parts = []
    if house_num:
        parts.append(str(house_num))
    parts.append(plus_short)
    parts.extend(sub_parts)
    city_state_pin_country = ", ".join([x for x in [city, state, postcode, country] if x])
    if city_state_pin_country:
        parts.append(city_state_pin_country)
    detail_line = ", ".join(parts)

    latlon_line = f"Lat {lat:.6f}° Long {lon:.6f}°"
    tz = timezone(timedelta(minutes=tz_offset_min))
    dt_local = datetime.fromtimestamp(ts_ms/1000.0, tz=tz) if ts_ms else datetime.now(tz)
    time_line = f"{dt_local.strftime('%d/%m/%Y %I:%M %p')} {format_offset(tz_offset_min)}"

    single_line = f"{title_line} {detail_line} {latlon_line} {time_line}".strip()
    return {
        "title_line": title_line,
        "detail_line": detail_line,
        "latlon_line": latlon_line,
        "time_line": time_line,
        "single_line": single_line,
        "plus_full": plus_full,
        "plus_short": plus_short,
        "display_name": display_name
    }

# ------------------ canonical signing utilities (self-describing signatures) ------------------
def payload_from_label(lat, lon, tz_offset_min, ts_ms, label_dict):
    tz = timezone(timedelta(minutes=tz_offset_min))
    dt_local = datetime.fromtimestamp(ts_ms/1000.0, tz=tz)
    iso_local = dt_local.isoformat()
    payload = {
        "v": 1,
        "kid": KID,
        "lat": round(float(lat), 6),
        "lon": round(float(lon), 6),
        "tz": int(tz_offset_min),
        "ts_iso": iso_local,
        "plus": label_dict["plus_short"],
        "title": label_dict["title_line"],
        "detail": label_dict["detail_line"],
    }
    return payload

def canonical_bytes_for_payload(payload: dict) -> bytes:
    txt = json.dumps(payload, separators=(",", ":"), sort_keys=True, ensure_ascii=False)
    return txt.encode("utf-8")

def sign_payload(payload: dict) -> str:
    data = canonical_bytes_for_payload(payload)
    # RSA key
    if isinstance(private_key, rsa.RSAPrivateKey):
        sig = private_key.sign(
            data,
            asym_padding.PSS(mgf=asym_padding.MGF1(hashes.SHA256()), salt_length=asym_padding.PSS.MAX_LENGTH),
            hashes.SHA256()
        )
        return f"rsa-pss-sha256|{base64.b64encode(sig).decode('ascii')}"
    # EC key
    try:
        der_sig = private_key.sign(data, ec.ECDSA(hashes.SHA256()))
        return f"ecdsa-p256-sha256|{base64.b64encode(der_sig).decode('ascii')}"
    except Exception as e:
        raise RuntimeError(f"Unsupported private key type for signing: {e}")

def verify_payload_sig(payload: dict, sig_field: str) -> tuple[bool, str]:
    data = canonical_bytes_for_payload(payload)
    # parse alg|b64
    if isinstance(sig_field, str) and "|" in sig_field:
        alg, b64 = sig_field.split("|", 1)
        try:
            raw = base64.b64decode(b64)
        except Exception:
            return False, "Malformed base64 signature"
        try:
            if alg == "ecdsa-p256-sha256":
                public_key.verify(raw, data, ec.ECDSA(hashes.SHA256()))
                return True, "Signature valid (ECDSA P-256 SHA-256)."
            if alg == "rsa-pss-sha256":
                public_key.verify(raw, data, asym_padding.PSS(mgf=asym_padding.MGF1(hashes.SHA256()), salt_length=asym_padding.PSS.MAX_LENGTH), hashes.SHA256())
                return True, "Signature valid (RSA-PSS SHA-256)."
            if alg == "rsa-pkcs1v15-sha256":
                public_key.verify(raw, data, asym_padding.PKCS1v15(), hashes.SHA256())
                return True, "Signature valid (RSA PKCS1v15 SHA-256)."
            return False, f"Unknown signature algorithm '{alg}'."
        except InvalidSignature:
            return False, "Invalid signature for geo-details."
        except Exception as e:
            return False, f"Verification error: {e}"

    # legacy plain base64: try plausible verifies
    try:
        raw = base64.b64decode(sig_field)
    except Exception:
        return False, "Malformed base64 signature"
    # EC try
    try:
        public_key.verify(raw, data, ec.ECDSA(hashes.SHA256()))
        return True, "Signature valid (detected ECDSA legacy)."
    except Exception:
        pass
    # RSA-PSS try
    try:
        public_key.verify(raw, data, asym_padding.PSS(mgf=asym_padding.MGF1(hashes.SHA256()), salt_length=asym_padding.PSS.MAX_LENGTH), hashes.SHA256())
        return True, "Signature valid (detected RSA-PSS legacy)."
    except Exception:
        pass
    # RSA PKCS1v15
    try:
        public_key.verify(raw, data, asym_padding.PKCS1v15(), hashes.SHA256())
        return True, "Signature valid (detected RSA PKCS1v15 legacy)."
    except InvalidSignature:
        return False, "Invalid signature for geo-details."
    except Exception as e:
        return False, f"Verification error: {e}"

# ------------------ QR helpers (faster compression / smaller QR) ------------------
_ZLIB_LEVEL = 3            # faster than 9, still compresses
_QR_BOX_SIZE = 6           # smaller than 10 -> faster
_QR_BORDER = 2

def b64url_encode(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).decode("ascii").rstrip("=")

def b64url_decode(s: str) -> bytes:
    pad = "=" * (-len(s) % 4)
    return base64.urlsafe_b64decode(s + pad)

def make_geosig_qr(sig_object: dict) -> Image.Image:
    js = json.dumps(sig_object, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    packed = zlib.compress(js, level=_ZLIB_LEVEL)
    qr_text = "GSIG1:" + b64url_encode(packed)
    qr = qrcode.QRCode(version=None, error_correction=ERROR_CORRECT_M, box_size=_QR_BOX_SIZE, border=_QR_BORDER)
    qr.add_data(qr_text)
    qr.make(fit=True)
    return qr.make_image(fill_color="black", back_color="white").convert("RGBA")

# ------------------ font caching ------------------
_FONT_CACHE = {}
def get_font(size):
    # try common locations and cache by size
    key = size
    if key in _FONT_CACHE:
        return _FONT_CACHE[key]
    font_paths = ["/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
                  "/Library/Fonts/Arial.ttf",
                  "C:\\Windows\\Fonts\\arial.ttf"]
    f = None
    for path in font_paths:
        if os.path.exists(path):
            try:
                f = ImageFont.truetype(path, size)
                break
            except Exception:
                pass
    if f is None:
        f = ImageFont.load_default()
    _FONT_CACHE[key] = f
    return f

# ------------------ render bottom strip (re-usable and deterministic) ------------------
def build_lines_from_payload(payload: dict) -> dict:
    title = payload.get("title", "")
    detail = payload.get("detail", "")
    lat = payload.get("lat")
    lon = payload.get("lon")
    tz_minutes = int(payload.get("tz", 0)) if payload.get("tz") is not None else 0
    latlon_line = f"Lat {float(lat):.6f}° Long {float(lon):.6f}°" if (lat is not None and lon is not None) else ""
    ts_iso = payload.get("ts_iso")
    try:
        dt_local = datetime.fromisoformat(ts_iso)
    except Exception:
        dt_local = datetime.now(tz=timezone(timedelta(minutes=tz_minutes)))
    time_line = f"{dt_local.strftime('%d/%m/%Y %I:%M %p')} {format_offset(tz_minutes)}"
    return {
        "title_line": title,
        "detail_line": detail,
        "latlon_line": latlon_line,
        "time_line": time_line,
        "single_line": " ".join([title, detail, latlon_line, time_line]).strip()
    }

def render_strip_from_sigobject(sig_object: dict, width: int) -> Image.Image:
    payload = sig_object.get("payload", {})
    lines = build_lines_from_payload(payload)
    W = width
    title_font_size = max(12, int(W * 0.028))
    body_font_size  = max(10, int(W * 0.018))
    font_title = get_font(title_font_size)
    font_body  = get_font(body_font_size)

    pad_x = int(W * 0.02)
    pad_y = max(6, int(W * 0.012))
    gap   = int(W * 0.006)

    qr_side = max(120, min(180, int(W * 0.14)))
    qr_img = make_geosig_qr(sig_object).resize((qr_side, qr_side), Image.NEAREST)

    text_w = W - (qr_side + 3*pad_x)
    dummy = Image.new("RGB",(W,100),(255,255,255))
    draw_dummy = ImageDraw.Draw(dummy)

    def wrap(draw, text, font, max_w):
        if not text: return []
        words, out, line = text.split(), [], ""
        for w in words:
            t = (line + " " + w).strip()
            bbox = draw.textbbox((0,0), t, font=font)
            if (bbox[2]-bbox[0]) <= max_w:
                line = t
            else:
                if line:
                    out.append(line)
                line = w
        if line:
            out.append(line)
        return out

    title_lines  = wrap(draw_dummy, lines.get("title_line",""),  font_title, text_w)
    detail_lines = wrap(draw_dummy, lines.get("detail_line",""), font_body,  text_w)
    latlon_lines = wrap(draw_dummy, lines.get("latlon_line",""), font_body,  text_w)
    time_lines   = wrap(draw_dummy, lines.get("time_line",""),   font_body,  text_w)

    def lh(font):
        b = draw_dummy.textbbox((0,0), "Ag", font=font)
        return b[3] - b[1]
    title_h, body_h = lh(font_title), lh(font_body)

    text_block_h = (pad_y + len(title_lines)*title_h + gap +
                    len(detail_lines)*body_h + gap +
                    len(latlon_lines)*body_h + gap +
                    len(time_lines)*body_h + pad_y)

    strip_h = max(qr_side + 2*pad_y, text_block_h)
    strip_h = max(strip_h, 120)
    strip_h = min(strip_h, int((W/16)*9))

    strip = Image.new("RGBA", (W, strip_h), (255,255,255,255))
    draw = ImageDraw.Draw(strip)

    qr_x = pad_x
    qr_y = (strip_h - qr_side)//2
    strip.paste(qr_img, (qr_x, qr_y), qr_img)

    tx = qr_x + qr_side + pad_x
    ty = pad_y
    black = (20,20,20)
    gray = (80,80,80)
    for ln in title_lines:
        draw.text((tx, ty), ln, font=font_title, fill=black)
        ty += title_h
    ty += gap
    for ln in detail_lines:
        draw.text((tx, ty), ln, font=font_body, fill=gray)
        ty += body_h
    ty += gap
    for ln in latlon_lines:
        draw.text((tx, ty), ln, font=font_body, fill=gray)
        ty += body_h
    ty += gap
    for ln in time_lines:
        draw.text((tx, ty), ln, font=font_body, fill=gray)
        ty += body_h

    draw.text((qr_x, qr_y + qr_side + 4), f"Sig {KID}", font=font_body, fill=(120,120,120))
    return strip.convert("RGB")

# ------------------ full-image composition ------------------
def draw_bottom_strip(img: Image.Image, lines: dict, sig_object: dict) -> Image.Image:
    strip = render_strip_from_sigobject(sig_object, img.width)
    W, H = img.size
    strip_w, strip_h = strip.size
    out = Image.new("RGB", (W, H + strip_h), (255,255,255))
    out.paste(img, (0,0))
    out.paste(strip, (0, H))
    draw = ImageDraw.Draw(out)
    draw.rectangle([(0,H), (W, H+1)], fill=(220,220,220))
    return out

# ------------------ pHash utilities (faster: resize 16 -> lower CPU) ------------------
_PHASH_RESIZE = 16  # previously 32; 16 speeds DCT substantially but still uses 8x8 block
def phash_pil(img: Image.Image) -> str:
    size = _PHASH_RESIZE
    small = 8
    gray = np.array(img.convert("L"), dtype=np.float32)
    if gray.size == 0:
        return "0"*16
    resized = cv2.resize(gray, (size, size), interpolation=cv2.INTER_AREA)
    dct = cv2.dct(resized)
    block = dct[:small, :small]
    med = np.median(block.flatten())
    bits = (block.flatten() > med).astype(np.uint8)
    val = 0
    for b in bits:
        val = (val << 1) | int(b)
    return "{:016x}".format(val)

def hamming_hex(a_hex: str, b_hex: str) -> int:
    try:
        a = int(a_hex, 16)
        b = int(b_hex, 16)
        return (a ^ b).bit_count()
    except Exception:
        return 999

# ------------------ QR decode (robust) / EXIF extraction ------------------
def decode_geosig_from_qr(raw_bytes: bytes):
    np_arr = np.frombuffer(raw_bytes, np.uint8)
    img_color = cv2.imdecode(np_arr, cv2.IMREAD_COLOR)
    if img_color is None:
        return None
    detector = cv2.QRCodeDetector()
    candidates = []

    def try_decode(img_gray):
        data, pts, _ = detector.detectAndDecode(img_gray)
        if data:
            candidates.append(data)
        try:
            retval, decoded_info, points, _ = detector.detectAndDecodeMulti(img_gray)
            if retval and decoded_info:
                for d in decoded_info:
                    if d:
                        candidates.append(d)
        except Exception:
            pass

    gray = cv2.cvtColor(img_color, cv2.COLOR_BGR2GRAY)
    variations = [gray]
    try:
        thr = cv2.adaptiveThreshold(gray,255,cv2.ADAPTIVE_THRESH_GAUSSIAN_C,cv2.THRESH_BINARY,31,2)
        variations.append(thr)
    except Exception:
        pass
    try:
        _, otsu = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY+cv2.THRESH_OTSU)
        variations.append(otsu)
    except Exception:
        pass

    scales = [1.0, 1.5, 2.0, 0.75]
    for img in variations:
        for s in scales:
            if s != 1.0:
                h, w = img.shape[:2]
                img_s = cv2.resize(img, (int(w*s), int(h*s)), interpolation=cv2.INTER_LINEAR)
            else:
                img_s = img
            try_decode(img_s)

    for s in candidates:
        try:
            if s.startswith("GSIG1:"):
                packed = s.split("GSIG1:",1)[1].strip()
                js = zlib.decompress(b64url_decode(packed)).decode("utf-8", errors="ignore")
                obj = json.loads(js)
                if isinstance(obj, dict) and obj.get("v")==1 and "payload" in obj and "sig" in obj:
                    return obj
        except Exception:
            continue
    return None

def extract_geosig_from_exif(raw_bytes: bytes):
    try:
        exif = piexif.load(raw_bytes)
        desc = exif.get("0th", {}).get(piexif.ImageIFD.ImageDescription)
        if not desc:
            return None
        if isinstance(desc, bytes):
            desc = desc.decode("utf-8", errors="ignore")
        obj = json.loads(desc)
        if isinstance(obj, dict) and "GEOSIG" in obj:
            return obj["GEOSIG"]
    except Exception:
        return None
    return None

# ------------------ DB helpers ------------------
def store_capture_record(filename: str, phash_hex: str, strip_phash: str, payload: dict, signature_b64: str):
    con = sqlite3.connect(DB_FILE)
    cur = con.cursor()
    cur.execute("INSERT INTO images (filename, phash, strip_phash, payload, signature, ts) VALUES (?, ?, ?, ?, ?, ?)",
                (filename, phash_hex, strip_phash, json.dumps(payload, separators=(",", ":")), signature_b64, datetime.utcnow().isoformat()))
    con.commit()
    con.close()

def find_best_phash_match(phash_hex: str, max_hamming=10):
    con = sqlite3.connect(DB_FILE)
    cur = con.cursor()
    cur.execute("SELECT id, filename, phash, strip_phash, payload, signature, ts FROM images")
    rows = cur.fetchall()
    con.close()
    best = None
    best_dist = 999
    for r in rows:
        try:
            dist = hamming_hex(phash_hex, r[2])
        except Exception:
            continue
        if dist < best_dist:
            best_dist = dist
            best = r
    if best and best_dist <= max_hamming:
        id_, filename, phash, strip_phash, payload_json, signature_b64, ts = best
        try:
            payload = json.loads(payload_json)
        except Exception:
            payload = None
        return {"id": id_, "filename": filename, "phash": phash, "strip_phash": strip_phash,
                "payload": payload, "signature": signature_b64, "dist": best_dist}
    return None

# ------------------ ROUTES ------------------
@app.get("/")
def index():
    return render_template("index.html")

@app.post("/capture")
def capture():
    # Expect: photo file, lat, lon, tz_offset_min, ts_ms
    if "photo" not in request.files:
        return jsonify({"error":"No photo uploaded"}), 400
    photo = request.files["photo"]
    try:
        lat = float(request.form.get("lat"))
        lon = float(request.form.get("lon"))
        tz_offset_min = int(request.form.get("tz_offset_min"))
        ts_ms = int(request.form.get("ts_ms"))
    except Exception as e:
        return jsonify({"error": f"Bad form data: {e}"}), 400

    # Start geocoding in a background thread so we overlap I/O with CPU work
    geocode_result = {}
    def _geocode_worker():
        display, addr = reverse_geocode(lat, lon, use_cache=True, precision=_GEOCACHE_PRECISION)
        geocode_result['display'] = display
        geocode_result['addr'] = addr

    t = threading.Thread(target=_geocode_worker, daemon=True)
    t.start()

    # Load image and compute main pHash immediately (CPU-bound) while geocode runs
    img = Image.open(photo.stream).convert("RGB")
    ph = phash_pil(img)

    # Wait for geocode thread to finish but we allow a short max wait (to avoid indefinite block).
    # Usually Nominatim responds quickly; in worst case we wait a small extra time to allow QR/strip generation
    t.join(timeout=4.0)  # join but don't block forever; caching helps repeated captures

    # Build label lines (use geocode results if available)
    address_override = None
    if 'display' in geocode_result:
        address_override = (geocode_result.get('display'), geocode_result.get('addr') or {})
    else:
        # fallback: try a quick cached lookup without network (very fast)
        c = get_geocode_cache_db(lat, lon)
        if c:
            address_override = c
        else:
            # as a last resort, do a synchronous geocode with a short timeout (rare)
            display, addr = reverse_geocode(lat, lon, use_cache=True, precision=_GEOCACHE_PRECISION)
            address_override = (display, addr)

    label = build_label_lines(lat, lon, tz_offset_min, ts_ms, address_override=address_override)
    payload = payload_from_label(lat, lon, tz_offset_min, ts_ms, label)
    sig_b64 = sign_payload(payload)
    sig_object = {"v": 1, "kid": KID, "payload": payload, "sig": sig_b64}

    # render strip + compute strip phash (these are relatively fast now)
    strip_img = render_strip_from_sigobject(sig_object, img.width)
    strip_ph = phash_pil(strip_img)

    # compose final image with bottom strip
    final_img = Image.new("RGB", (img.width, img.height + strip_img.height), (255,255,255))
    final_img.paste(img, (0,0))
    final_img.paste(strip_img, (0, img.height))

    # EXIF embedding (same as before)
    tz = timezone(timedelta(minutes=tz_offset_min))
    dt_local = datetime.fromtimestamp(ts_ms/1000.0, tz=tz)
    exif_local_str = dt_local.strftime("%Y:%m:%d %H:%M:%S")
    exif_dict = {"0th":{}, "Exif":{}, "GPS":{}, "1st":{}, "Interop":{}}
    exif_dict["0th"][piexif.ImageIFD.DateTime] = exif_local_str
    exif_dict["Exif"][piexif.ExifIFD.DateTimeOriginal] = exif_local_str
    exif_dict["Exif"][0x9011] = (f"{'+' if tz_offset_min >= 0 else '-'}{abs(tz_offset_min)//60:02d}:{abs(tz_offset_min)%60:02d}").encode("ascii", errors="ignore")
    exif_dict["GPS"] = make_gps_ifd(lat, lon, dt_local.astimezone(timezone.utc))
    exif_dict["Exif"][piexif.ExifIFD.UserComment] = UserComment.dump(label["single_line"], encoding="unicode")
    exif_dict["0th"][piexif.ImageIFD.ImageDescription] = json.dumps({"GEOSIG": sig_object}, separators=(",", ":")).encode("utf-8", errors="ignore")

    # Save final image (lowered JPEG quality for speed + smaller file)
    safe_ts = dt_local.strftime("%Y%m%d_%H%M%S")
    filename = f"geotag_{safe_ts}.jpg"
    out_path = os.path.join(OUTPUT_DIR, filename)
    bio = io.BytesIO()
    exif_bytes = piexif.dump(exif_dict)
    # quality=85 is a good speed/size tradeoff; optimize=False to avoid extra processing
    final_img.save(bio, format="JPEG", quality=85, exif=exif_bytes, optimize=False)
    with open(out_path, "wb") as f:
        f.write(bio.getvalue())

    # store DB mapping phash -> payload + signature + strip_phash
    store_capture_record(filename, ph, strip_ph, payload, sig_b64)

    file_url = url_for("static", filename=f"outputs/{filename}", _external=True)
    return jsonify({"ok": True, "file": file_url, "label_lines": label, "kid": KID})

@app.post("/verify")
def verify():
    if "file" not in request.files:
        return jsonify({"error":"No file uploaded"}), 400
    raw = request.files["file"].read()

    sigobj = extract_geosig_from_exif(raw)
    source = None
    if sigobj:
        source = "exif"
    else:
        sigobj = decode_geosig_from_qr(raw)
        if sigobj:
            source = "qr"

    if sigobj:
        payload = sigobj.get("payload")
        sig_field = sigobj.get("sig")
        if isinstance(payload, dict) and isinstance(sig_field, str):
            valid, vmsg = verify_payload_sig(payload, sig_field)
            details = {
                "title": payload.get("title",""),
                "detail": payload.get("detail",""),
                "lat": payload.get("lat"),
                "lon": payload.get("lon"),
                "time_iso": payload.get("ts_iso"),
                "tz_minutes": payload.get("tz"),
                "plus": payload.get("plus"),
                "kid": payload.get("kid")
            }
            try:
                img = Image.open(io.BytesIO(raw)).convert("RGB")
                W, H = img.size
                expected_strip = render_strip_from_sigobject(sigobj, W)
                strip_h = expected_strip.height
                if strip_h >= H:
                    overlay_match = False
                    overlay_dist = None
                else:
                    crop = img.crop((0, H - strip_h, W, H))
                    expected_ph = phash_pil(expected_strip)
                    actual_ph = phash_pil(crop)
                    overlay_dist = hamming_hex(expected_ph, actual_ph)
                    OVERLAY_THRESHOLD = 8
                    overlay_match = (overlay_dist <= OVERLAY_THRESHOLD)
            except Exception:
                overlay_match = False
                overlay_dist = None

            if valid:
                if overlay_match:
                    return jsonify({"ok": True, "verifiable": True, "valid": True,
                                    "message": f"VALID — ORIGINAL — {vmsg}",
                                    "overlay_match": True, "overlay_hamming": overlay_dist,
                                    "details": details}), 200
                else:
                    return jsonify({"ok": True, "verifiable": True, "valid": False,
                                    "message": f"TAMPERED — Signature valid but visible label does not match signed payload. {vmsg}",
                                    "overlay_match": False, "overlay_hamming": overlay_dist,
                                    "details_signed": details}), 200
            else:
                return jsonify({"ok": True, "verifiable": True, "valid": False,
                                "message": "TAMPERED — " + vmsg}), 200

    # DB fallback (phash)
    try:
        img = Image.open(io.BytesIO(raw)).convert("RGB")
    except Exception as e:
        return jsonify({"error": f"Invalid image: {e}"}), 400

    full_ph = phash_pil(img)
    w, h = img.size
    crop_h = int(h * 0.80)
    top_crop = img.crop((0, 0, w, crop_h))
    crop_ph = phash_pil(top_crop)

    MAX_DIST = 10
    candidate = find_best_phash_match(full_ph, max_hamming=MAX_DIST)
    if not candidate:
        candidate = find_best_phash_match(crop_ph, max_hamming=MAX_DIST)

    if candidate:
        payload = candidate.get("payload")
        sig_field = candidate.get("signature")
        if isinstance(payload, dict) and isinstance(sig_field, str):
            valid, vmsg = verify_payload_sig(payload, sig_field)
            details = {
                "title": payload.get("title",""),
                "detail": payload.get("detail",""),
                "lat": payload.get("lat"),
                "lon": payload.get("lon"),
                "time_iso": payload.get("ts_iso"),
                "tz_minutes": payload.get("tz"),
                "plus": payload.get("plus"),
                "kid": payload.get("kid")
            }
            try:
                expected_strip = render_strip_from_sigobject({"payload": payload, "sig": sig_field}, img.width)
                strip_h = expected_strip.height
                if strip_h >= img.height:
                    overlay_match = False
                    overlay_dist = None
                else:
                    crop = img.crop((0, img.height - strip_h, img.width, img.height))
                    overlay_dist = hamming_hex(phash_pil(expected_strip), phash_pil(crop))
                    OVERLAY_THRESHOLD = 8
                    overlay_match = (overlay_dist <= OVERLAY_THRESHOLD)
            except Exception:
                overlay_match = False
                overlay_dist = None

            if valid:
                if overlay_match:
                    return jsonify({"ok": True, "verifiable": True, "valid": True,
                                    "message": f"VALID — ORIGINAL — {vmsg} (matched DB entry id {candidate.get('id')})",
                                    "overlay_match": True, "overlay_hamming": overlay_dist,
                                    "details": details}), 200
                else:
                    return jsonify({"ok": True, "verifiable": True, "valid": False,
                                    "message": f"TAMPERED — Stored signature valid but visible label mismatch (phash dist {overlay_dist}).",
                                    "overlay_match": False, "overlay_hamming": overlay_dist,
                                    "details_signed": details}), 200
            else:
                return jsonify({"ok": True, "verifiable": True, "valid": False,
                                "message": "TAMPERED — Stored signature invalid."}), 200

    return jsonify({"ok": True, "verifiable": False, "valid": False,
                    "message": "UNVERIFIABLE — No GeoSig found and no perceptual match in local store."}), 200

@app.get("/download/<path:filename>")
def download(filename):
    return send_from_directory(OUTPUT_DIR, filename, as_attachment=True)

if __name__ == "__main__":
    app.run(debug=True, host="0.0.0.0", port=5000)
