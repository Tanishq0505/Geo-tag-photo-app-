// unchanged camera + capture logic plus small verify UI added
const video = document.getElementById('video');
const canvas = document.getElementById('canvas');
const deviceSelect = document.getElementById('deviceSelect');
const btnStart = document.getElementById('btnStart');
const btnCapture = document.getElementById('btnCapture');
const errorsEl = document.getElementById('errors');

const titleLine = document.getElementById('titleLine');
const detailLine = document.getElementById('detailLine');
const latlonLine = document.getElementById('latlonLine');
const timeLine = document.getElementById('timeLine');
const preview = document.getElementById('preview');
const resultSection = document.getElementById('result');
const downloadLink = document.getElementById('downloadLink');

const verifyInput = document.getElementById('verifyInput');
const verifyBtn = document.getElementById('verifyBtn');
const verifyResult = document.getElementById('verifyResult');

let stream = null;

function showError(msg) {
  console.error(msg);
  errorsEl.textContent = typeof msg === 'string' ? msg : (msg && msg.message) || 'Unknown error';
  errorsEl.classList.remove('hidden');
}
function clearError() {
  errorsEl.classList.add('hidden');
  errorsEl.textContent = '';
}

async function enumerateCameras() {
  if (!navigator.mediaDevices || !navigator.mediaDevices.enumerateDevices) {
    return;
  }
  try {
    const devices = await navigator.mediaDevices.enumerateDevices();
    deviceSelect.innerHTML = '';
    const videoInputs = devices.filter(d => d.kind === 'videoinput');
    if (videoInputs.length === 0) {
      const opt = document.createElement('option');
      opt.value = '';
      opt.textContent = 'No camera found';
      deviceSelect.appendChild(opt);
      return;
    }
    for (const dev of videoInputs) {
      const opt = document.createElement('option');
      opt.value = dev.deviceId;
      opt.textContent = dev.label || `Camera ${deviceSelect.length + 1}`;
      deviceSelect.appendChild(opt);
    }
  } catch (e) {
    console.warn('enumerateDevices error:', e);
  }
}

async function startCamera() {
  clearError();
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
    showError('Camera API not supported in this browser. Use Chrome/Edge/Firefox on http://127.0.0.1:5000');
    return;
  }
  try {
    if (stream) {
      stream.getTracks().forEach(t => t.stop());
      stream = null;
    }

    let constraints = { video: { width: { ideal: 1280 }, height: { ideal: 720 } }, audio: false };
    const selectedId = deviceSelect.value;
    if (selectedId) {
      constraints.video.deviceId = { exact: selectedId };
    } else {
      constraints.video.facingMode = "user";
    }

    video.muted = true;
    video.setAttribute('playsinline', 'true');

    stream = await navigator.mediaDevices.getUserMedia(constraints);
    video.srcObject = stream;
    await video.play().catch(() => { });
    btnCapture.disabled = false;
  } catch (err) {
    if (err && err.name === 'NotAllowedError') {
      showError('Permission denied for camera. Allow camera in site settings and retry.');
    } else if (err && err.name === 'NotFoundError') {
      showError('No camera found. Connect a webcam and retry.');
    } else {
      showError('Camera error: ' + err);
    }
  }
}

function stopCamera() {
  if (stream) {
    stream.getTracks().forEach(t => t.stop());
    stream = null;
  }
}

function getPosition() {
  return new Promise((resolve, reject) => {
    if (!('geolocation' in navigator)) {
      reject(new Error('Geolocation not supported.'));
      return;
    }
    navigator.geolocation.getCurrentPosition(
      pos => resolve(pos),
      err => reject(err),
      { enableHighAccuracy: true, timeout: 20000, maximumAge: 0 }
    );
  });
}

async function captureAndSend() {
  clearError();
  const vw = video.videoWidth, vh = video.videoHeight;
  if (!vw || !vh) return showError('Video not ready yet. Click "Enable Camera" and wait a moment.');

  canvas.width = vw; canvas.height = vh;
  const ctx = canvas.getContext('2d');
  ctx.drawImage(video, 0, 0, vw, vh);

  const blob = await new Promise(r => canvas.toBlob(r, 'image/jpeg', 0.95));
  if (!blob) return showError('Failed to capture image.');

  let pos;
  try {
    pos = await getPosition();
  } catch (e) {
    showError('Location error. Allow location in browser & OS settings and retry.');
    return;
  }

  const lat = pos.coords.latitude;
  const lon = pos.coords.longitude;
  const ts_ms = Date.now();
  const tz_offset_min = -new Date().getTimezoneOffset(); // minutes east of UTC

  const form = new FormData();
  form.append('photo', blob, 'capture.jpg');
  form.append('lat', String(lat));
  form.append('lon', String(lon));
  form.append('tz_offset_min', String(tz_offset_min));
  form.append('ts_ms', String(ts_ms));

  let res;
  try { res = await fetch('/capture', { method: 'POST', body: form }); }
  catch (e) { showError('Network error calling /capture. Is Flask running?'); return; }
  if (!res.ok) { showError('Server error: ' + (await res.text())); return; }
  const data = await res.json();

  preview.src = data.file;
  titleLine.textContent = data.label_lines.title_line || '';
  detailLine.textContent = data.label_lines.detail_line || '';
  latlonLine.textContent = data.label_lines.latlon_line || '';
  timeLine.textContent = data.label_lines.time_line || '';
  downloadLink.href = data.file;
  downloadLink.setAttribute('download', data.file.split('/').pop());
  resultSection.classList.remove('hidden');
}

// ---- verification UI
verifyBtn.addEventListener('click', async () => {
  verifyResult.textContent = '';
  const f = verifyInput.files[0];
  if (!f) { verifyResult.textContent = 'Choose a file to verify.'; return; }
  const form = new FormData();
  form.append('file', f);
  try {
    const res = await fetch('/verify', { method: 'POST', body: form });
    if (!res.ok) {
      verifyResult.textContent = 'Server error verifying file.';
      return;
    }
    const data = await res.json();
    if (data.error) {
      verifyResult.textContent = 'Error: ' + data.error;
      return;
    }
    if (data.valid) {
      verifyResult.innerHTML = '<strong style="color:#7ED957">VALID — ' + (data.message || '') + '</strong>';
    } else {
      verifyResult.innerHTML = '<strong style="color:#FF6B6B">TAMPERED — ' + (data.message || '') + '</strong>';
    }
    if (data.label) {
      verifyResult.innerHTML += '<div style="margin-top:8px;color:#bfc9d9">Label (embedded): ' + data.label + '</div>';
    }
  } catch (e) {
    verifyResult.textContent = 'Network error: ' + e;
  }
});

window.addEventListener('load', () => {
  enumerateCameras();
});
btnStart.addEventListener('click', startCamera);
btnCapture.addEventListener('click', captureAndSend);
window.addEventListener('beforeunload', stopCamera);
