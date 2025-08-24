# app.py
"""
Geo-Tagged Photo App (robust across social sharing)
- Strong QR (ERROR_CORRECT_H, larger modules, better decoder)
- Survivable verification without EXIF/QR via multi-hash fallback (pHash/aHash/dHash, full + top region)
- Returns full geotag details on valid results
- Detects label tampering by comparing reconstructed strip to the bottom region
- Reliable downloads in production (/view vs /download)
"""
from flask import Flask, render_template, request, jsonify, url_for, send_from_directory
from datetime import datetime, timezone, timedelta
import io, os, requests, base64, json, hashlib, zlib, sqlite3, threading
from PIL import Image, ImageDraw, ImageFont
import piexif
from piexif.helper import UserComment
from fractions import Fraction
from openlocationcode import openlocationcode as olc

# QR
import qrcode
from qrcode.constants import ERROR_CORRECT_H  # <-- robust again

# OpenCV + numpy
import cv2
import numpy as np

# crypto
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, rsa, padding as asym_padding
from cryptography.exceptions import InvalidSignature

from werkzeug.utils import secure_filename

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
SESSION = requests.Session()

# ------------------ Key handling ------------------
def generate_and_store_keys():
    # Generate ECDSA P-256 by default; supports RSA too if keys already exist
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
    return send_from_directory(os.path.dirname(PUBLIC_KEY_FILE),
                               os.path.basename(PUBLIC_KEY_FILE),
                               as_attachment=True)

# ------------------ DB + schema migration ------------------
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
    con.commit()

    # schema migration for new hash columns
    cur.execute("PRAGMA table_info(images)")
    cols = {row[1] for row in cur.fetchall()}
    alters = []
    if "photo_phash_top" not in cols:
        alters.append("ALTER TABLE images ADD COLUMN photo_phash_top TEXT")
    if "ahash_full" not in cols:
        alters.append("ALTER TABLE images ADD COLUMN ahash_full TEXT")
    if "ahash_top" not in cols:
        alters.append("ALTER TABLE images ADD COLUMN ahash_top TEXT")
    if "dhash_full" not in cols:
        alters.append("ALTER TABLE images ADD COLUMN dhash_full TEXT")
    if "dhash_top" not in cols:
        alters.append("ALTER TABLE images ADD COLUMN dhash_top TEXT")
    for stmt in alters:
        cur.execute(stmt)
    if alters:
        con.commit()
    cur.close()
    con.close()

init_db()

# --------------- in-memory geocode cache ----------------
_GEOCACHE_MEM = {}
_GEOCACHE_MEM_LOCK = threading.Lock()
_GEOCACHE_PRECISION = 5

def _round_coords(lat, lon, precision=_GEOCACHE_PRECISION):
    return round(float(lat), precision), round(float(lon), precision)

def get_geocode_cache_db(lat, lon, precision=_GEOCACHE_PRECISION):
    lat_r, lon_r = _round_coords(lat, lon, precision)
    key = (lat_r, lon_r)
    with _GEOCACHE_MEM_LOCK:
        if key in _GEOCACHE_MEM:
            return _GEOCACHE_MEM[key]
    con = sqlite3.connect(DB_FILE)
    cur = con.cursor()
    cur.execute("SELECT display, address_json FROM geocode_cache WHERE lat_r=? AND lon_r=? LIMIT 1", (lat_r, lon_r))
    row = cur.fetchone()
    con.close()
    if row:
        display = row[0]
        addr = json.loads(row[1]) if row[1] else {}
        with _GEOCACHE_MEM_LOCK:
            _GEOCACHE_MEM[key] = (display, addr)
        return display, addr
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
    cached = get_geocode_cache_db(lat, lon, precision=precision) if use_cache else None
    if cached:
        return cached
    try:
        headers = {"User-Agent": f"GeoTagPhotoApp/1.0 ({NOMINATIM_EMAIL})"}
        params = {"format": "jsonv2", "lat": lat, "lon": lon, "zoom": 18, "addressdetails": 1}
        r = SESSION.get("https://nominatim.openstreetmap.org/reverse", params=params, headers=headers, timeout=5)
        if r.ok:
            j = r.json()
            display = j.get("display_name")
            address = j.get("address", {})
            set_geocode_cache_db(lat, lon, display or "", address, precision=precision)
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

# ------------------ signing ------------------
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
    if isinstance(private_key, rsa.RSAPrivateKey):
        sig = private_key.sign(
            data,
            asym_padding.PSS(mgf=asym_padding.MGF1(hashes.SHA256()), salt_length=asym_padding.PSS.MAX_LENGTH),
            hashes.SHA256()
        )
        return f"rsa-pss-sha256|{base64.b64encode(sig).decode('ascii')}"
    try:
        der_sig = private_key.sign(data, ec.ECDSA(hashes.SHA256()))
        return f"ecdsa-p256-sha256|{base64.b64encode(der_sig).decode('ascii')}"
    except Exception as e:
        raise RuntimeError(f"Unsupported private key: {e}")

def verify_payload_sig(payload: dict, sig_field: str) -> tuple[bool, str]:
    data = canonical_bytes_for_payload(payload)
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
                public_key.verify(raw, data,
                                  asym_padding.PSS(mgf=asym_padding.MGF1(hashes.SHA256()),
                                                   salt_length=asym_padding.PSS.MAX_LENGTH),
                                  hashes.SHA256())
                return True, "Signature valid (RSA-PSS SHA-256)."
            if alg == "rsa-pkcs1v15-sha256":
                public_key.verify(raw, data, asym_padding.PKCS1v15(), hashes.SHA256())
                return True, "Signature valid (RSA PKCS1v15 SHA-256)."
            return False, f"Unknown signature algorithm '{alg}'."
        except InvalidSignature:
            return False, "Invalid signature for geo-details."
        except Exception as e:
            return False, f"Verification error: {e}"
    # legacy attempt(s)
    try:
        raw = base64.b64decode(sig_field)
    except Exception:
        return False, "Malformed base64 signature"
    for scheme in (
        lambda: public_key.verify(raw, data, ec.ECDSA(hashes.SHA256())),
        lambda: public_key.verify(raw, data, asym_padding.PSS(mgf=asym_padding.MGF1(hashes.SHA256()),
                                                              salt_length=asym_padding.PSS.MAX_LENGTH), hashes.SHA256()),
        lambda: public_key.verify(raw, data, asym_padding.PKCS1v15(), hashes.SHA256())
    ):
        try:
            scheme()
            return True, "Signature valid (legacy)."
        except Exception:
            pass
    return False, "Invalid signature for geo-details."

# ------------------ QR helpers ------------------
_ZLIB_LEVEL = 6
_QR_BOX_SIZE = 10
_QR_BORDER = 4

def b64url_encode(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).decode("ascii").rstrip("=")

def b64url_decode(s: str) -> bytes:
    pad = "=" * (-len(s) % 4)
    return base64.urlsafe_b64decode(s + pad)

def make_geosig_qr(sig_object: dict) -> Image.Image:
    js = json.dumps(sig_object, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    packed = zlib.compress(js, level=_ZLIB_LEVEL)
    qr_text = "GSIG1:" + b64url_encode(packed)
    qr = qrcode.QRCode(version=None, error_correction=ERROR_CORRECT_H, box_size=_QR_BOX_SIZE, border=_QR_BORDER)
    qr.add_data(qr_text)
    qr.make(fit=True)
    return qr.make_image(fill_color="black", back_color="white").convert("RGBA")

# ------------------ font cache ------------------
_FONT_CACHE = {}
def get_font(size):
    if size in _FONT_CACHE:
        return _FONT_CACHE[size]
    for path in ["/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
                 "/Library/Fonts/Arial.ttf",
                 "C:\\Windows\\Fonts\\arial.ttf"]:
        if os.path.exists(path):
            try:
                f = ImageFont.truetype(path, size)
                _FONT_CACHE[size] = f
                return f
            except Exception:
                pass
    f = ImageFont.load_default()
    _FONT_CACHE[size] = f
    return f

# ------------------ strip rendering ------------------
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
    title_font_size = max(14, int(W * 0.030))
    body_font_size  = max(12, int(W * 0.020))
    font_title = get_font(title_font_size)
    font_body  = get_font(body_font_size)

    pad_x = int(W * 0.02)
    pad_y = max(8, int(W * 0.012))
    gap   = int(W * 0.006)

    # Larger QR to survive mobile recompression
    qr_side = max(220, min(260, int(W * 0.17)))
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
                if line: out.append(line)
                line = w
        if line: out.append(line)
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
    strip_h = max(strip_h, 140)
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
        draw.text((tx, ty), ln, font=font_title, fill=black); ty += title_h
    ty += gap
    for ln in detail_lines:
        draw.text((tx, ty), ln, font=font_body, fill=gray); ty += body_h
    ty += gap
    for ln in latlon_lines:
        draw.text((tx, ty), ln, font=font_body, fill=gray); ty += body_h
    ty += gap
    for ln in time_lines:
        draw.text((tx, ty), ln, font=font_body, fill=gray); ty += body_h

    draw.text((qr_x, qr_y + qr_side + 4), f"Sig {KID}", font=font_body, fill=(120,120,120))
    return strip.convert("RGB")

def draw_bottom_strip(img: Image.Image, sig_object: dict) -> Image.Image:
    strip = render_strip_from_sigobject(sig_object, img.width)
    W, H = img.size
    out = Image.new("RGB", (W, H + strip.height), (255,255,255))
    out.paste(img, (0,0))
    out.paste(strip, (0, H))
    draw = ImageDraw.Draw(out)
    draw.rectangle([(0,H), (W, H+1)], fill=(220,220,220))
    return out

# ------------------ perceptual hashes ------------------
_PHASH_RESIZE = 16

def phash(img: Image.Image) -> str:
    size = _PHASH_RESIZE
    gray = np.array(img.convert("L"), dtype=np.float32)
    if gray.size == 0:
        return "0"*16
    resized = cv2.resize(gray, (size, size), interpolation=cv2.INTER_AREA)
    dct = cv2.dct(resized)
    block = dct[:8, :8]
    med = np.median(block.flatten())
    bits = (block.flatten() > med).astype(np.uint8)
    val = 0
    for b in bits:
        val = (val << 1) | int(b)
    return "{:016x}".format(val)

def ahash(img: Image.Image) -> str:
    gray = np.array(img.convert("L").resize((8,8), Image.BILINEAR), dtype=np.float32)
    avg = gray.mean()
    bits = (gray >= avg).astype(np.uint8).flatten()
    val = 0
    for b in bits:
        val = (val << 1) | int(b)
    return "{:016x}".format(val)

def dhash(img: Image.Image) -> str:
    gray = np.array(img.convert("L").resize((9,8), Image.BILINEAR), dtype=np.float32)
    diff = gray[:,1:] > gray[:,:-1]
    bits = diff.astype(np.uint8).flatten()
    val = 0
    for b in bits:
        val = (val << 1) | int(b)
    return "{:016x}".format(val)

def hamming_hex(a_hex: str, b_hex: str) -> int:
    try:
        a = int(a_hex or "0", 16)
        b = int(b_hex or "0", 16)
        return (a ^ b).bit_count()
    except Exception:
        return 999

def compute_hashes_for(img: Image.Image):
    w, h = img.size
    top_crop = img.crop((0, 0, w, int(h * 0.80)))
    return {
        "ph_full": phash(img),
        "ph_top": phash(top_crop),
        "ah_full": ahash(img),
        "ah_top": ahash(top_crop),
        "dh_full": dhash(img),
        "dh_top": dhash(top_crop)
    }

# ------------------ QR/EXIF decode ------------------
def decode_geosig_from_qr(raw_bytes: bytes):
    np_arr = np.frombuffer(raw_bytes, np.uint8)
    img_color = cv2.imdecode(np_arr, cv2.IMREAD_COLOR)
    if img_color is None:
        return None
    detector = cv2.QRCodeDetector()
    candidates = []

    def try_decode_img(img):
        # Single
        data, pts, _ = detector.detectAndDecode(img)
        if data:
            candidates.append(data)
        # Multi
        try:
            retval, decoded_info, points, _ = detector.detectAndDecodeMulti(img)
            if retval and decoded_info:
                for d in decoded_info:
                    if d:
                        candidates.append(d)
        except Exception:
            pass

    gray = cv2.cvtColor(img_color, cv2.COLOR_BGR2GRAY)
    H, W = gray.shape[:2]
    variations = []

    # base + processed variants
    variations.append(gray)
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
    try:
        blurred = cv2.GaussianBlur(gray, (3,3), 0)
        variations.append(blurred)
    except Exception:
        pass
    try:
        med = cv2.medianBlur(gray, 3)
        variations.append(med)
    except Exception:
        pass

    # also try likely strip region(s) near bottom
    bands = [(int(H*0.55), H), (int(H*0.65), H), (int(H*0.75), H)]
    for y0, y1 in bands:
        crop = gray[y0:y1, :]
        if crop.size > 0:
            variations.append(crop)

    scales = [0.6, 0.8, 1.0, 1.25, 1.5, 2.0]
    for img in variations:
        for s in scales:
            if s != 1.0:
                h, w = img.shape[:2]
                img_s = cv2.resize(img, (max(32, int(w*s)), max(32, int(h*s))), interpolation=cv2.INTER_LINEAR)
            else:
                img_s = img
            try_decode_img(img_s)

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
def store_capture_record(filename: str, hashes: dict, strip_phash: str, payload: dict, signature_b64: str):
    con = sqlite3.connect(DB_FILE)
    cur = con.cursor()
    cur.execute("""
        INSERT INTO images
            (filename, phash, strip_phash, payload, signature, ts,
             photo_phash_top, ahash_full, ahash_top, dhash_full, dhash_top)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        filename,
        hashes.get("ph_full"),
        strip_phash,
        json.dumps(payload, separators=(",", ":")),
        signature_b64,
        datetime.utcnow().isoformat(),
        hashes.get("ph_top"),
        hashes.get("ah_full"),
        hashes.get("ah_top"),
        hashes.get("dh_full"),
        hashes.get("dh_top"),
    ))
    con.commit()
    con.close()

def find_best_hash_match(hashes: dict):
    """Return best candidate row using combined hash distances and adaptive thresholds."""
    con = sqlite3.connect(DB_FILE)
    cur = con.cursor()
    cur.execute("SELECT id, filename, phash, strip_phash, payload, signature, ts, photo_phash_top, ahash_full, ahash_top, dhash_full, dhash_top FROM images")
    rows = cur.fetchall()
    con.close()

    if not rows:
        return None

    # Thresholds tuned for social-media recompression/resizing
    PH_TIGHT = 12    # excellent match
    PH_LOOSE = 20    # good enough after heavy compression
    AD_THR   = 18    # for aHash/dHash

    best = None
    best_score = (999, 999, 999)  # (primary, secondary, tertiary)

    for r in rows:
        id_, filename, ph_full_db, strip_ph, payload_json, sig, ts, ph_top_db, ah_full_db, ah_top_db, dh_full_db, dh_top_db = r
        # compute distances
        d_ph_full = hamming_hex(hashes["ph_full"], ph_full_db or "")
        d_ph_top  = hamming_hex(hashes["ph_top"],  ph_top_db  or "")
        d_ah_full = hamming_hex(hashes["ah_full"], ah_full_db or "")
        d_ah_top  = hamming_hex(hashes["ah_top"],  ah_top_db  or "")
        d_dh_full = hamming_hex(hashes["dh_full"], dh_full_db or "")
        d_dh_top  = hamming_hex(hashes["dh_top"],  dh_top_db  or "")

        ph_best = min(d_ph_full, d_ph_top)
        ah_best = min(d_ah_full, d_ah_top)
        dh_best = min(d_dh_full, d_dh_top)

        # quick accept window
        acceptable = (
            ph_best <= PH_TIGHT or
            (ph_best <= PH_LOOSE and (ah_best <= AD_THR or dh_best <= AD_THR))
        )
        if not acceptable:
            continue

        score = (ph_best, ah_best, dh_best)
        if score < best_score:
            best_score = score
            try:
                payload = json.loads(payload_json)
            except Exception:
                payload = None
            best = {
                "id": id_,
                "filename": filename,
                "payload": payload,
                "signature": sig,
                "score": score
            }

    return best

# ------------------ ROUTES ------------------
@app.get("/")
def index():
    return render_template("index.html")

@app.post("/capture")
def capture():
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

    # reverse geocode in background
    geocode_result = {}
    def _geocode_worker():
        display, addr = reverse_geocode(lat, lon, use_cache=True, precision=_GEOCACHE_PRECISION)
        geocode_result['display'] = display
        geocode_result['addr'] = addr
    t = threading.Thread(target=_geocode_worker, daemon=True)
    t.start()

    # original photo
    img = Image.open(photo.stream).convert("RGB")
    hashes = compute_hashes_for(img)

    t.join(timeout=5.0)
    address_override = (geocode_result.get('display'), geocode_result.get('addr') or {}) if 'display' in geocode_result else (get_geocode_cache_db(lat, lon) or reverse_geocode(lat, lon, use_cache=True))
    if isinstance(address_override, tuple):
        label = build_label_lines(lat, lon, tz_offset_min, ts_ms, address_override=address_override)
    else:
        label = build_label_lines(lat, lon, tz_offset_min, ts_ms)

    payload = payload_from_label(lat, lon, tz_offset_min, ts_ms, label)
    sig_field = sign_payload(payload)
    sig_object = {"v": 1, "kid": KID, "payload": payload, "sig": sig_field}

    # strip and composite
    strip_img = render_strip_from_sigobject(sig_object, img.width)
    strip_ph = phash(strip_img)
    final_img = Image.new("RGB", (img.width, img.height + strip_img.height), (255,255,255))
    final_img.paste(img, (0,0))
    final_img.paste(strip_img, (0, img.height))
    draw = ImageDraw.Draw(final_img)
    draw.rectangle([(0,img.height), (img.width, img.height+1)], fill=(220,220,220))

    # EXIF (will be stripped by social apps, but preserved for direct downloads)
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

    safe_ts = dt_local.strftime("%Y%m%d_%H%M%S")
    filename = f"geotag_{safe_ts}.jpg"
    out_path = os.path.join(OUTPUT_DIR, filename)
    bio = io.BytesIO()
    exif_bytes = piexif.dump(exif_dict)
    # modest quality keeps QR robust after re-compression
    final_img.save(bio, format="JPEG", quality=88, exif=exif_bytes, optimize=False)
    with open(out_path, "wb") as f:
        f.write(bio.getvalue())

    store_capture_record(filename, hashes, strip_ph, payload, sig_field)

    view_url = url_for("view_image", filename=filename, _external=True)
    download_url = url_for("download", filename=filename, _external=True)
    return jsonify({"ok": True,
                    "file": view_url,          # preview
                    "view_url": view_url,
                    "download_url": download_url,
                    "label_lines": label,
                    "kid": KID})

@app.post("/verify")
def verify():
    if "file" not in request.files:
        return jsonify({"error":"No file uploaded"}), 400
    raw = request.files["file"].read()

    # 1) Try EXIF
    sigobj = extract_geosig_from_exif(raw)

    # 2) Try QR (robust decoder)
    if not sigobj:
        sigobj = decode_geosig_from_qr(raw)

    if sigobj:
        payload = sigobj.get("payload")
        sig_field = sigobj.get("sig")
        if isinstance(payload, dict) and isinstance(sig_field, str):
            valid, vmsg = verify_payload_sig(payload, sig_field)

            # details to return on success
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

            # Check visible label vs signed payload (detect edited text)
            try:
                img = Image.open(io.BytesIO(raw)).convert("RGB")
                W, H = img.size
                expected_strip = render_strip_from_sigobject(sigobj, W)
                sh = expected_strip.height
                if sh < H:
                    crop = img.crop((0, H - sh, W, H))
                    dist = hamming_hex(phash(expected_strip), phash(crop))
                    overlay_match = dist <= 10
                    overlay_dist = dist
                else:
                    overlay_match = False
                    overlay_dist = None
            except Exception:
                overlay_match = False
                overlay_dist = None

            if valid:
                if overlay_match:
                    return jsonify({
                        "ok": True, "verifiable": True, "valid": True,
                        "message": f"VALID — ORIGINAL — {vmsg}",
                        "overlay_match": True, "overlay_hamming": overlay_dist,
                        "details": details
                    }), 200
                else:
                    return jsonify({
                        "ok": True, "verifiable": True, "valid": False,
                        "message": f"TAMPERED — Signature valid but visible label does not match signed payload. {vmsg}",
                        "overlay_match": False, "overlay_hamming": overlay_dist,
                        "details_signed": details
                    }), 200
            else:
                return jsonify({"ok": True, "verifiable": True, "valid": False,
                                "message": "TAMPERED — " + vmsg}), 200

    # 3) Perceptual-hash DB fallback (survives EXIF strip, QR blur/crop)
    try:
        img = Image.open(io.BytesIO(raw)).convert("RGB")
    except Exception as e:
        return jsonify({"error": f"Invalid image: {e}"}), 400

    hashes_in = compute_hashes_for(img)
    candidate = find_best_hash_match(hashes_in)

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

            # Try label match too (if bottom strip exists)
            try:
                W, H = img.size
                expected_strip = render_strip_from_sigobject({"payload": payload, "sig": sig_field}, W)
                sh = expected_strip.height
                if sh < H:
                    crop = img.crop((0, H - sh, W, H))
                    dist = hamming_hex(phash(expected_strip), phash(crop))
                    overlay_match = dist <= 10
                    overlay_dist = dist
                else:
                    overlay_match = False
                    overlay_dist = None
            except Exception:
                overlay_match = False
                overlay_dist = None

            if valid:
                if overlay_match:
                    return jsonify({
                        "ok": True, "verifiable": True, "valid": True,
                        "message": f"VALID — ORIGINAL — {vmsg} (matched DB entry id {candidate.get('id')})",
                        "overlay_match": True, "overlay_hamming": overlay_dist,
                        "details": details
                    }), 200
                else:
                    # Still mark valid? We choose to flag as tampered-visible-label to detect edits.
                    return jsonify({
                        "ok": True, "verifiable": True, "valid": False,
                        "message": f"TAMPERED — Stored signature valid but visible label mismatch.",
                        "overlay_match": False, "overlay_hamming": overlay_dist,
                        "details_signed": details
                    }), 200
            else:
                return jsonify({"ok": True, "verifiable": True, "valid": False,
                                "message": "TAMPERED — Stored signature invalid."}), 200

    # 4) Nothing matched
    return jsonify({"ok": True, "verifiable": False, "valid": False,
                    "message": "UNVERIFIABLE — No GeoSig found and no perceptual match in local store."}), 200

# ---------- view (inline) ----------
@app.get("/view/<path:filename>")
def view_image(filename):
    safe = secure_filename(os.path.basename(filename))
    path = os.path.join(OUTPUT_DIR, safe)
    if not os.path.isfile(path):
        return jsonify({"error": "File not found"}), 404
    resp = send_from_directory(OUTPUT_DIR, safe, as_attachment=False, mimetype="image/jpeg")
    resp.headers["Content-Disposition"] = f'inline; filename="{safe}"'
    return resp

# ---------- download (force save) ----------
@app.route("/download/<path:filename>", methods=["GET", "HEAD"])
def download(filename):
    safe = secure_filename(os.path.basename(filename))
    path = os.path.join(OUTPUT_DIR, safe)
    if not os.path.isfile(path):
        return jsonify({"error": "File not found"}), 404
    resp = send_from_directory(
        OUTPUT_DIR,
        safe,
        as_attachment=True,
        download_name=safe,
        mimetype="application/octet-stream"
    )
    resp.headers["Content-Disposition"] = f'attachment; filename="{safe}"'
    resp.headers["X-Content-Type-Options"] = "nosniff"
    resp.headers["Cache-Control"] = "private, max-age=600"
    return resp

if __name__ == "__main__":
    app.run(debug=True, host="0.0.0.0", port=5000)
