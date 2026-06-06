'use strict';
/* ============================================================================
   TremorPause Collect — web app logic
   Pairs with the TremorPause_DAQ.ino firmware (Arduino Nano 33 BLE Sense Rev2).

   Pipeline: connect over Web Bluetooth -> for each motion task, tell the board
   to capture accel+gyro into its RAM at full ODR -> board bulk-transfers the raw
   buffer in small binary packets with a CRC32 -> we reassemble byte-perfect,
   re-requesting any dropped packets -> upload raw int16 + metadata to Firestore
   (collection `tremor_raw_v2`, same `tremorpauseweb` project as the old app).

   We store RAW int16 counts plus the range scale factors, so the analysis side
   converts to g / deg-per-sec losslessly. Nothing is inferred on-device.
   ========================================================================== */

/* ----------------------------- FIREBASE ---------------------------------- */
const FIREBASE_CONFIG = {
  apiKey: "AIzaSyAzMGMviZmrwthvTIPXlGk5VmrqQT2b5NM",
  authDomain: "tremorpauseweb.firebaseapp.com",
  projectId: "tremorpauseweb",
  storageBucket: "tremorpauseweb.firebasestorage.app",
  messagingSenderId: "553085922178",
  appId: "1:553085922178:web:e6f2ebdafddd9520b77d9b"
};
const RAW_COLLECTION = 'tremor_raw_v2';   // NEW collection — raw blobs, not feature windows
const SESSION_COLLECTION = 'sessions';
const APP_VERSION = 'collect-v1';

let db = null;
function initFirebase(cfg) {
  try {
    if (firebase.apps && firebase.apps.length) firebase.app();
    else firebase.initializeApp(cfg);
    db = firebase.firestore();
    setFbStatus('Firebase: ready (' + cfg.projectId + ')', false);
  } catch (e) {
    db = null;
    setFbStatus('Firebase init failed: ' + e.message, true);
  }
}

/* --------------------- BLE PROTOCOL (mirror of firmware) ------------------ */
const SERVICE_UUID = 'f1e10000-8c2a-4b9d-9b1e-2a7c0d5e1a01';
const CONTROL_UUID = 'f1e10001-8c2a-4b9d-9b1e-2a7c0d5e1a01';  // app -> board (write)
const DATA_UUID    = 'f1e10002-8c2a-4b9d-9b1e-2a7c0d5e1a01';  // board -> app (notify)

const CMD_START = 0x01, CMD_ABORT = 0x02, CMD_RESEND = 0x03;
const FRM_MANIFEST = 0x01, FRM_DATA = 0x02, FRM_DONE = 0x03, FRM_STATE = 0x04;
const ST_IDLE = 0, ST_CAPTURING = 1, ST_TRANSFER = 2, ST_DONE = 3,
      ST_ABORTED = 4, ST_ERROR = 5, ST_BUFFER_FULL = 6;

const PAYLOAD_BYTES = 16;     // raw bytes per FRM_DATA packet (must match firmware)
const BYTES_PER_SAMPLE = 12;  // 6 axes * int16
const MAX_RESENDS = 8;        // recovery attempts before a task is marked failed
const XFER_IDLE_MS = 1000;    // no packet for this long during transfer => link stalled

/* code -> human values (must match firmware register mapping) */
const ODR_HZ          = { 0:100, 1:200, 2:400, 3:800, 4:1600 };
const ACC_RANGE_G     = { 0:2, 1:4, 2:8, 3:16 };
const ACC_LSB_PER_G   = { 0:16384, 1:8192, 2:4096, 3:2048 };
const GYR_RANGE_DPS   = { 0:2000, 1:1000, 2:500, 3:250, 4:125 };
const GYR_LSB_PER_DPS = { 0:16.384, 1:32.768, 2:65.536, 3:131.072, 4:262.144 };

/* Firmware on-board buffer cap (TremorPause_DAQ.ino MAX_SAMPLES). Used only to
   warn the operator when a high rate + long task would overflow it. */
const FW_MAX_SAMPLES = 8000;

/* --------------------------- MOTION TASKS --------------------------------- */
/* Short battery covering static holds AND dynamic/voluntary movement, so a model
   can learn to isolate tremor even while the hand is doing something. */
const SEGMENTS = [
  { key:'rest', label:'Rest (supported)', dur:10000,
    howto:'Sit. Rest the forearm and hand fully on the table or armrest, palm down, completely relaxed. Do nothing.',
    why:'Resting tremor baseline with no voluntary motion.' },
  { key:'postural', label:'Postural hold', dur:10000,
    howto:'Hold the arm straight out in front, level with the shoulder, hand steady. Hold it there.',
    why:'Postural tremor — appears when holding against gravity.' },
  { key:'functional', label:'Spoon-to-mouth', dur:10000,
    howto:'Pretend to eat: bring an empty spoon (or just the hand) from the table up to the mouth and back down. Repeat smoothly.',
    why:'A real functional task — tremor that affects daily life.' },
  { key:'free', label:'Free movement', dur:10000,
    howto:'Move the hand naturally — wave, reach around, pick things up, gesture. Keep moving the whole time, no specific pattern.',
    why:'Mixed voluntary motion — teaches the model to separate movement from tremor.' }
];

/* ------------------------------ CRC32 ------------------------------------- */
/* Standard CRC-32 (poly 0xEDB88320, init 0xFFFFFFFF, final XOR). Bit-identical
   to crc32_buf() in the firmware. */
const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
    t[n] = c >>> 0;
  }
  return t;
})();
function crc32(bytes) {
  let crc = 0xFFFFFFFF;
  for (let i = 0; i < bytes.length; i++)
    crc = (crc >>> 8) ^ CRC_TABLE[(crc ^ bytes[i]) & 0xFF];
  return (crc ^ 0xFFFFFFFF) >>> 0;
}

/* ----------------------------- RUNTIME STATE ------------------------------ */
let device = null, server = null, controlChar = null, dataChar = null;
let connected = false;

let sessionId = null;
let participantCode = null;

let currentIndex = 0;
let singleMode = false;          // redo a single task from the review screen
let results = [];                // per-segment captured data + status
let pending = null;              // params we asked the board to use this capture
let cap = null;                  // active reassembly buffer
let xferTimer = null;            // transfer-stall watchdog
let countdownTimer = null;
let uploading = false;

/* --------------------------- DOM HELPERS ---------------------------------- */
const $ = (id) => document.getElementById(id);
const val = (id) => { const e = $(id); return e ? e.value : ''; };
function showScreen(id) {
  ['screen-setup','screen-segment','screen-capture','screen-transfer','screen-review']
    .forEach(s => $(s).classList.add('hidden'));
  $(id).classList.remove('hidden');
  window.scrollTo({ top: 0, behavior: 'smooth' });
}
let toastTimer = null;
function toast(msg) {
  const t = $('toast'); t.textContent = msg; t.style.opacity = '1';
  clearTimeout(toastTimer); toastTimer = setTimeout(() => t.style.opacity = '0', 2600);
}
function setConn(state, text) {
  const pill = $('conn-pill'); const dot = pill.querySelector('.dot');
  $('conn-text').textContent = text;
  const c = state === 'on' ? 'var(--green)' : state === 'busy' ? 'var(--orange)' : 'var(--red)';
  dot.style.background = c; pill.style.color = c;
}
function setFbStatus(msg, isErr) {
  const e = $('firebase-status'); if (!e) return;
  e.textContent = msg; e.style.color = isErr ? 'var(--red)' : 'var(--muted)';
}
function genId() {
  if (crypto && crypto.randomUUID) return crypto.randomUUID();
  return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, ch => {
    const r = Math.random() * 16 | 0; return (ch === 'x' ? r : (r & 0x3 | 0x8)).toString(16);
  });
}

/* ------------------------------ BLE WRITE --------------------------------- */
async function writeControl(arr) {
  const b = Uint8Array.from(arr);
  if (!controlChar) throw new Error('not connected');
  if (controlChar.writeValueWithResponse) await controlChar.writeValueWithResponse(b);
  else await controlChar.writeValue(b);
}

/* ------------------------------ CONNECT ----------------------------------- */
async function connect() {
  if (!navigator.bluetooth) {
    toast('Web Bluetooth unavailable. Use Chrome/Edge, or Bluefy on iPhone/iPad.');
    return;
  }
  const name = (val('set-name') || 'TremorPause-DAQ').trim();
  try {
    setConn('busy', 'Scanning…');
    device = await navigator.bluetooth.requestDevice({
      // match by advertised service OR exact name (tolerant of name edits)
      filters: [{ services: [SERVICE_UUID] }, { name }],
      optionalServices: [SERVICE_UUID]
    });
    device.addEventListener('gattserverdisconnected', onDisconnected);
    setConn('busy', 'Connecting…');
    server = await device.gatt.connect();
    const svc = await server.getPrimaryService(SERVICE_UUID);
    controlChar = await svc.getCharacteristic(CONTROL_UUID);
    dataChar = await svc.getCharacteristic(DATA_UUID);
    await dataChar.startNotifications();
    dataChar.addEventListener('characteristicvaluechanged', onData);
    connected = true;
    setConn('on', device.name || 'Connected');
    toast('Sensor connected');
    refreshBeginEnabled();
  } catch (e) {
    connected = false;
    setConn('off', 'Not connected');
    if (e && e.name !== 'NotFoundError') toast('Connect failed: ' + e.message);
  }
}
function onDisconnected() {
  connected = false; controlChar = null; dataChar = null;
  setConn('off', 'Disconnected');
  if (countdownTimer) { clearInterval(countdownTimer); countdownTimer = null; }
  clearXferWatchdog();
  toast('Sensor disconnected');
  refreshBeginEnabled();
}

/* ------------------------- INCOMING FRAME ROUTER -------------------------- */
function onData(e) {
  const dv = e.target.value;            // DataView
  if (dv.byteLength < 1) return;
  switch (dv.getUint8(0)) {
    case FRM_STATE:    handleState(dv.getUint8(1)); break;
    case FRM_MANIFEST: handleManifest(dv); break;
    case FRM_DATA:     handleDataPacket(dv); break;
    case FRM_DONE:     handleDone(dv); break;
  }
}

function handleState(st) {
  switch (st) {
    case ST_CAPTURING: /* capture screen already up */ break;
    case ST_TRANSFER:
      stopCountdown();
      resetTransferUI();
      showScreen('screen-transfer');
      break;
    case ST_BUFFER_FULL:
      toast('On-board buffer full — capture truncated. Lower the rate for full-length tasks.');
      break;
    case ST_ABORTED:
      stopCountdown(); clearXferWatchdog();
      toast('Recording cancelled');
      afterSegmentExit(false);
      break;
    case ST_ERROR:
      stopCountdown(); clearXferWatchdog();
      toast('Sensor error — try the task again.');
      afterSegmentExit(false);
      break;
    /* ST_DONE / ST_IDLE: confirmatory, handled by DONE frame */
  }
}

function handleManifest(dv) {
  const odr = dv.getUint8(1), acc = dv.getUint8(2), gyr = dv.getUint8(3);
  const n = dv.getUint32(4, true);
  const totalPkts = dv.getUint16(8, true);
  const captureMs = dv.getUint32(10, true);
  cap = {
    n, totalPkts, odr, acc, gyr, captureMs,
    buf: new Uint8Array(n * BYTES_PER_SAMPLE),
    got: new Uint8Array(totalPkts),
    received: 0, expectedCrc: 0, resends: 0
  };
  resetTransferUI();
  showScreen('screen-transfer');
  $('xfer-sub').textContent = n.toLocaleString() + ' samples · receiving';
  if ($('xfer-hold')) $('xfer-hold').textContent =
    'Recording done — rest your hand still for a few seconds while it saves.';
  armXferWatchdog();
}

function handleDataPacket(dv) {
  if (!cap) return;
  const seq = dv.getUint16(1, true);
  if (seq >= cap.totalPkts) return;
  if (cap.got[seq]) return;                         // duplicate (e.g. from a resend)
  const len = dv.byteLength - 3;
  const off = seq * PAYLOAD_BYTES;
  for (let i = 0; i < len && off + i < cap.buf.length; i++)
    cap.buf[off + i] = dv.getUint8(3 + i);
  cap.got[seq] = 1; cap.received++;
  updateTransferUI();
  armXferWatchdog();            // packets still flowing -> keep waiting
}

function handleDone(dv) {
  if (!cap) return;
  cap.expectedCrc = dv.getUint32(1, true);

  let missing = 0, min = -1, max = -1;
  for (let s = 0; s < cap.totalPkts; s++) {
    if (!cap.got[s]) { missing++; if (min < 0) min = s; max = s; }
  }

  if (missing === 0) {
    const got = crc32(cap.buf);
    if (got === cap.expectedCrc) { clearXferWatchdog(); finishSegment(); return; }
    // all packets present but CRC mismatch -> a payload was corrupted; resend all
  }
  if (cap.resends >= MAX_RESENDS) { failSegment(missing); return; }
  requestResend(min, max);
}

function requestResend(min, max) {
  if (min < 0) { min = 0; max = cap.totalPkts - 1; }   // CRC-only failure: redo all
  const count = max - min + 1;
  cap.resends++;
  $('xfer-sub').textContent = 'recovering ' + count + ' packet(s) · try ' + cap.resends + '/' + MAX_RESENDS;
  writeControl([CMD_RESEND, min & 0xFF, (min >> 8) & 0xFF, count & 0xFF, (count >> 8) & 0xFF])
    .then(armXferWatchdog)     // expect the re-sent packets + a fresh DONE
    .catch(err => { toast('Resend failed: ' + err.message); failSegment(count); });
}

/* ------------------------- TRANSFER WATCHDOG ------------------------------ */
/* The board can drop the tail of the notification stream (incl. the DONE frame)
   if the BLE link briefly can't keep up. Without this, the app would sit at
   e.g. 70% forever. On a stall we proactively re-request what's missing — and if
   everything actually arrived but DONE was lost, we nudge the last packet to make
   the board re-emit DONE so we can verify the CRC. */
function clearXferWatchdog() { if (xferTimer) { clearTimeout(xferTimer); xferTimer = null; } }
function armXferWatchdog() { clearXferWatchdog(); xferTimer = setTimeout(onXferStall, XFER_IDLE_MS); }
function onXferStall() {
  xferTimer = null;
  if (!cap) return;
  if (cap.resends >= MAX_RESENDS) { failSegment(cap.totalPkts - cap.received); return; }
  let missing = 0, min = -1, max = -1;
  for (let s = 0; s < cap.totalPkts; s++) {
    if (!cap.got[s]) { missing++; if (min < 0) min = s; max = s; }
  }
  if (missing === 0) { min = max = cap.totalPkts - 1; }   // all data here; coax a fresh DONE
  $('xfer-sub').textContent = 'link stalled — recovering ' + cap.received + '/' + cap.totalPkts;
  requestResend(min, max);
}

/* ----------------------------- TRANSFER UI -------------------------------- */
function resetTransferUI() { $('xfer-bar').style.width = '0%'; $('xfer-pct').textContent = '0%'; }
function updateTransferUI() {
  if (!cap || !cap.totalPkts) return;
  const pct = Math.round(100 * cap.received / cap.totalPkts);
  $('xfer-bar').style.width = pct + '%';
  $('xfer-pct').textContent = pct + '%';
}

/* --------------------------- SEGMENT FLOW --------------------------------- */
function buildDots() {
  const row = $('seg-dots'); row.innerHTML = '';
  for (let i = 0; i < SEGMENTS.length; i++) {
    const d = document.createElement('div');
    d.className = 'p-dot' + (i < currentIndex ? ' done' : i === currentIndex ? ' active' : '');
    if (results[i] && results[i].status === 'ok') d.className = 'p-dot done';
    row.appendChild(d);
  }
}
function showSegment(i) {
  currentIndex = i;
  const s = SEGMENTS[i];
  buildDots();
  $('seg-counter').textContent = 'Task ' + (i + 1) + ' of ' + SEGMENTS.length;
  $('seg-title').textContent = s.label;
  $('seg-howto').textContent = s.howto;
  $('seg-why').textContent = 'Why: ' + s.why;
  $('btn-skip-seg').textContent = singleMode ? 'Back to review' : 'Skip this task';
  showScreen('screen-segment');
}

async function startCapture() {
  if (!connected) { toast('Connect the sensor first'); return; }
  const odr = +val('set-odr'), acc = +val('set-acc'), gyr = +val('set-gyr');
  const durMs = SEGMENTS[currentIndex].dur;
  pending = { odr, acc, gyr, durMs };
  cap = null;
  clearXferWatchdog();
  const d = Math.min(65535, durMs);
  try {
    await writeControl([CMD_START, odr, acc, gyr, d & 0xFF, (d >> 8) & 0xFF]);
  } catch (e) { toast('Could not start: ' + e.message); return; }
  // capture screen + cosmetic countdown (board controls the real duration)
  $('cap-counter').textContent = 'Task ' + (currentIndex + 1) + ' of ' + SEGMENTS.length;
  $('cap-title').textContent = SEGMENTS[currentIndex].label;
  $('cap-howto').textContent = SEGMENTS[currentIndex].howto;
  showScreen('screen-capture');
  startCountdown(durMs);
}
function startCountdown(durMs) {
  stopCountdown();
  let remaining = Math.ceil(durMs / 1000);
  $('cap-countdown').textContent = remaining;
  countdownTimer = setInterval(() => {
    remaining--;
    $('cap-countdown').textContent = remaining > 0 ? remaining : 0;
    if (remaining <= 0) { $('cap-countdown').textContent = '✓'; stopCountdown(); }
  }, 1000);
}
function stopCountdown() { if (countdownTimer) { clearInterval(countdownTimer); countdownTimer = null; } }

async function abortCapture() {
  clearXferWatchdog();
  try { await writeControl([CMD_ABORT]); } catch (e) {}
  stopCountdown();
  // ST_ABORTED will route us out; also handle here in case it's missed
  setTimeout(() => { if (!$('screen-capture').classList.contains('hidden')) afterSegmentExit(false); }, 600);
}

function skipSegment() {
  if (!results[currentIndex] || results[currentIndex].status === 'ok') {
    // don't overwrite a good capture when "back to review"
    if (!singleMode) {
      results[currentIndex] = {
        key: SEGMENTS[currentIndex].key, label: SEGMENTS[currentIndex].label,
        index: currentIndex, status: 'skipped'
      };
    }
  }
  afterSegmentExit(true);
}

function finishSegment() {
  clearXferWatchdog();
  const s = SEGMENTS[currentIndex];
  results[currentIndex] = {
    key: s.key, label: s.label, index: currentIndex,
    n: cap.n, captureMs: cap.captureMs,
    fsEff: cap.captureMs > 0 ? (cap.n / (cap.captureMs / 1000)) : 0,
    odr: cap.odr, acc: cap.acc, gyr: cap.gyr,
    buf: cap.buf, crc: cap.expectedCrc, status: 'ok'
  };
  const fs = results[currentIndex].fsEff;
  cap = null;
  toast('Task saved ✓ · ' + fs.toFixed(0) + ' Hz effective');
  afterSegmentExit(true);
}
function failSegment(missing) {
  clearXferWatchdog();
  const s = SEGMENTS[currentIndex];
  results[currentIndex] = {
    key: s.key, label: s.label, index: currentIndex, status: 'failed', missing: missing || 0
  };
  cap = null;
  toast('Task didn’t transfer cleanly — you can redo it from the review screen.');
  afterSegmentExit(true);
}

/* advance through the battery, or return to review in single-redo mode */
function afterSegmentExit(completedOrSkipped) {
  if (singleMode) { singleMode = false; buildReview(); showScreen('screen-review'); return; }
  if (!completedOrSkipped) { showSegment(currentIndex); return; }   // aborted -> retry same
  const next = currentIndex + 1;
  if (next < SEGMENTS.length) showSegment(next);
  else { buildReview(); showScreen('screen-review'); }
}

/* ------------------------------- REVIEW ----------------------------------- */
function buildReview() {
  const list = $('review-list'); list.innerHTML = '';
  let okCount = 0;
  for (let i = 0; i < SEGMENTS.length; i++) {
    const r = results[i];
    const row = document.createElement('div');
    row.className = 'seg-row';
    let icoClass, icoText, statText, detail;
    if (r && r.status === 'ok') {
      okCount++; icoClass = 'ok'; icoText = '✓';
      statText = r.n.toLocaleString() + ' smp<br>' + r.fsEff.toFixed(0) + ' Hz';
      detail = ODR_HZ[r.odr] + ' Hz · ' + (r.captureMs / 1000).toFixed(1) + ' s · CRC ok';
    } else if (r && r.status === 'failed') {
      icoClass = 'bad'; icoText = '!'; statText = 'tap to<br>redo';
      detail = 'transfer incomplete';
    } else {
      icoClass = 'skip'; icoText = '–'; statText = 'tap to<br>record';
      detail = 'not recorded';
    }
    row.innerHTML =
      '<div class="seg-ico ' + icoClass + '">' + icoText + '</div>' +
      '<div><div class="seg-name">' + (i + 1) + '. ' + SEGMENTS[i].label + '</div>' +
      '<div class="seg-detail">' + detail + '</div></div>' +
      '<div class="seg-stat">' + statText + '</div>';
    row.addEventListener('click', () => { singleMode = true; showSegment(i); });
    list.appendChild(row);
  }
  refreshUploadEnabled(okCount);
}
function refreshUploadEnabled(okCount) {
  if (okCount === undefined) okCount = results.filter(r => r && r.status === 'ok').length;
  const consent = $('consent-check').checked;
  const btn = $('btn-upload');
  btn.disabled = uploading || !consent || okCount === 0 || !db;
  if (uploading) return;
  if (!db) $('upload-hint').textContent = 'Firebase not ready — check Advanced settings.';
  else if (okCount === 0) $('upload-hint').textContent = 'No tasks captured yet. Tap a row to record one.';
  else if (!consent) $('upload-hint').textContent = 'Tick the consent box to enable upload.';
  else $('upload-hint').textContent = okCount + ' task(s) ready · tap any row above to re-record.';
}

/* ------------------------------- UPLOAD ----------------------------------- */
function gatherMeta() {
  return {
    age_band: val('m-age') || null,
    sex: val('m-sex') || null,
    hand_tested: val('m-hand') || null,
    is_dominant: val('m-dominant') || null,
    diagnosed_tremor: val('m-diag') || null,
    tremor_type: val('m-type') || null,
    notes: (val('m-notes') || '').slice(0, 500) || null
  };
}

async function uploadAll() {
  if (uploading || !db) return;
  const ok = results.filter(r => r && r.status === 'ok');
  if (!ok.length) { toast('Nothing to upload'); return; }
  uploading = true;
  $('btn-upload').disabled = true;
  const meta = gatherMeta();
  const ts = firebase.firestore.FieldValue.serverTimestamp();
  const summarySegs = [];

  try {
    for (let i = 0; i < ok.length; i++) {
      const r = ok[i];
      $('upload-hint').textContent = 'Uploading task ' + (i + 1) + ' of ' + ok.length + '…';
      const doc = {
        session_id: sessionId,
        participant_code: participantCode,
        segment: r.key,
        segment_label: r.label,
        segment_index: r.index,
        created_at: ts,
        app_version: APP_VERSION,
        meta: meta,
        imu: {
          dtype: 'int16_le',
          axis_order: 'ax,ay,az,gx,gy,gz',
          n_samples: r.n,
          odr_nominal_hz: ODR_HZ[r.odr],
          fs_effective_hz: Math.round(r.fsEff * 100) / 100,
          capture_ms: r.captureMs,
          accel_range_g: ACC_RANGE_G[r.acc],
          gyro_range_dps: GYR_RANGE_DPS[r.gyr],
          accel_lsb_per_g: ACC_LSB_PER_G[r.acc],
          gyro_lsb_per_dps: GYR_LSB_PER_DPS[r.gyr],
          crc32: r.crc >>> 0,
          data: firebase.firestore.Blob.fromUint8Array(r.buf)
        }
      };
      await db.collection(RAW_COLLECTION).doc(sessionId + '_' + r.key).set(doc);
      summarySegs.push({
        segment: r.key, n_samples: r.n,
        fs_effective_hz: Math.round(r.fsEff * 100) / 100,
        capture_ms: r.captureMs, odr_nominal_hz: ODR_HZ[r.odr], status: 'ok'
      });
    }

    // session summary doc
    $('upload-hint').textContent = 'Finishing…';
    await db.collection(SESSION_COLLECTION).doc(sessionId).set({
      session_id: sessionId,
      participant_code: participantCode,
      created_at: ts,
      app_version: APP_VERSION,
      device_name: device ? (device.name || null) : null,
      meta: meta,
      n_segments_uploaded: ok.length,
      odr_nominal_hz: ODR_HZ[+val('set-odr')],
      accel_range_g: ACC_RANGE_G[+val('set-acc')],
      gyro_range_dps: GYR_RANGE_DPS[+val('set-gyr')],
      segments: summarySegs
    });

    toast('Uploaded ' + ok.length + ' task(s) ✓');
    $('upload-hint').textContent = 'Done. Tap “New Participant” for the next person.';
    $('btn-upload').textContent = 'Uploaded ✓';
  } catch (e) {
    toast('Upload error: ' + e.message);
    $('upload-hint').textContent = 'Upload failed: ' + e.message + ' — you can retry.';
  } finally {
    uploading = false;
    refreshUploadEnabled();
  }
}

/* --------------------------- SESSION LIFECYCLE ---------------------------- */
function newParticipant() {
  results = []; currentIndex = 0; singleMode = false; cap = null; pending = null;
  participantCode = genId();
  sessionId = genId();
  $('participant-code').textContent = 'TP-' + participantCode.slice(0, 8);
  $('consent-check').checked = false;
  $('btn-upload').textContent = 'Upload All to Cloud';
  ['m-age','m-sex','m-hand','m-dominant','m-diag','m-type','m-notes'].forEach(id => {
    const e = $(id); if (e) e.value = e.tagName === 'SELECT' ? e.options[0].value : '';
  });
  refreshBeginEnabled();
  showScreen('screen-setup');
}
function beginSession() {
  if (!connected) { toast('Connect the sensor first'); return; }
  if (!val('m-age')) { toast('Pick an age band'); return; }
  if (!sessionId) sessionId = genId();
  results = []; currentIndex = 0; singleMode = false;
  showSegment(0);
}
function refreshBeginEnabled() {
  const e = $('btn-begin'); if (!e) return;
  e.disabled = !(connected && val('m-age'));
}

/* ------------------------------ RATE NOTE --------------------------------- */
function updateRateNote() {
  const hz = ODR_HZ[+val('set-odr')];
  const longest = Math.max.apply(null, SEGMENTS.map(s => s.dur)) / 1000; // seconds
  const maxSecs = FW_MAX_SAMPLES / hz;
  const note = $('rate-note');
  if (maxSecs < longest) {
    note.textContent = 'At ' + hz + ' Hz the on-board buffer fills after ~' + maxSecs.toFixed(1) +
      ' s, so the ' + longest + ' s tasks will be truncated. 400 Hz keeps every task complete and is recommended for tremor.';
  } else {
    note.textContent = 'At ' + hz + ' Hz every task fits in the on-board buffer (~' +
      maxSecs.toFixed(0) + ' s capacity). Good for tremor (3–12 Hz) plus voluntary motion.';
  }
}

/* ------------------------------- WIRE UP ---------------------------------- */
function wire() {
  // prefill firebase inputs + init
  $('fb-project').value = FIREBASE_CONFIG.projectId;
  $('fb-apikey').value = FIREBASE_CONFIG.apiKey;
  $('fb-appid').value = FIREBASE_CONFIG.appId;
  initFirebase(FIREBASE_CONFIG);

  participantCode = genId();
  $('participant-code').textContent = 'TP-' + participantCode.slice(0, 8);

  $('btn-connect').addEventListener('click', connect);
  $('btn-begin').addEventListener('click', beginSession);
  $('btn-start-seg').addEventListener('click', startCapture);
  $('btn-skip-seg').addEventListener('click', skipSegment);
  $('btn-abort').addEventListener('click', abortCapture);
  $('btn-upload').addEventListener('click', uploadAll);
  $('btn-new').addEventListener('click', newParticipant);
  $('btn-redo').addEventListener('click', () => toast('Tap any task above to record it again.'));
  $('consent-check').addEventListener('change', () => refreshUploadEnabled());
  $('m-age').addEventListener('change', refreshBeginEnabled);

  $('settings-toggle').addEventListener('click', () => {
    const b = $('settings-body');
    const open = b.style.display === 'block';
    b.style.display = open ? 'none' : 'block';
    $('settings-toggle').textContent = open ? 'show ▾' : 'hide ▴';
  });
  $('set-odr').addEventListener('change', updateRateNote);

  // re-init firebase if operator edits config
  ['fb-project','fb-apikey','fb-appid'].forEach(id =>
    $(id).addEventListener('change', () => {
      initFirebase(Object.assign({}, FIREBASE_CONFIG, {
        projectId: val('fb-project'), apiKey: val('fb-apikey'), appId: val('fb-appid')
      }));
    }));

  updateRateNote();
  setConn('off', 'Not connected');
}
document.addEventListener('DOMContentLoaded', wire);
