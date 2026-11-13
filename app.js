const EARTH = 6378137;
const FEET = 0.3048;
const BASE_PPM = 8;
const ZOOM_MIN = 0.12;
const ZOOM_MAX = 3;
const ZOOM_START = 0.42;
const BUFFER = 2048;
const BUFFER_CENTER = BUFFER / 2;

const $ = (id) => document.getElementById(id);

const state = {
  mode: 'idle',
  running: false,
  boomM: 20 * FEET,
  audio: true,
  volume: 0.25,
  contourTracking: false,
  contourPoints: [],
  guide: 'ab',
  aHeading: null,
  nextPoints: [],
  rowPoints: [],
  turn: null,
  mount: 0,
  deadbandM: 10 * FEET,
  tally: true,
  appliedM2: 0,
  passes: {},
  zoom: ZOOM_START,
  nudgeM: 0,
  passLock: null,
  applying: false,
  awake: false,
  wakeNote: '',
  origin: null,
  a: null,
  b: null,
  aGeo: null,
  bGeo: null,
  segments: [],
  lastPaint: null,
  stable: null,
  fix: null,
  gpsError: '',
  sensorGps: 'off',
  sensorCompass: 'off',
  sensorMotion: 'off',
  compass: null,
  compassTs: 0,
  compassAcc: null,
  compassBias: 0,
  compassRejects: 0,
  eventCompassTs: 0,
  heading: null,
  headingTarget: null,
  headingSource: 'No heading',
  gyroZ: 0,
  yawRate: 0,
  yawTs: 0,
  up: null,
  biasDirty: false,
  biasSaved: 0,
  biasSavedAt: 0,
  accelTs: 0,
  steerView: 0,
  steerBand: 'none',
  beepFlash: 0,
  beepCount: 0,
  rough: false
};

const demo = { x: 0, y: 0, heading: 0, speed: 3.15 };
const gpsTrail = [];
const coverage = { canvas: null, ctx: null, ox: 0, oy: 0 };
const sensors = {
  watchId: null,
  orientationOn: false,
  motionOn: false,
  absSensor: null
};

let liveHold = null;
let wakeLock = null;
let wantWake = false;
let audioCtx = null;
let lastBeep = 0;
let gpsRestartAt = 0;
let courseSmooth = null;
let wakeToken = 0;
let rafId = 0;
let lastFrame = 0;
let barSig = '';
let saveTimer = 0;
let pendingConfirm = null;
let deferredInstall = null;
let dbPromise = null;

const els = {};

function normDeg(value) {
  value %= 360;
  if (value < 0) value += 360;
  return value;
}

function angleDelta(from, to) {
  return ((to - from + 540) % 360) - 180;
}

function lerpAngle(from, to, t) {
  return normDeg(from + angleDelta(from, to) * t);
}

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function toLocal(lat, lon, origin) {
  const lat0 = origin.lat * Math.PI / 180;
  const x = (lon - origin.lon) * Math.PI / 180 * Math.cos(lat0) * EARTH;
  const y = (lat - origin.lat) * Math.PI / 180 * EARTH;
  return { x, y };
}

function lineFrame(a, b) {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  const len = Math.hypot(dx, dy);
  if (len < 0.5) return null;
  return { ux: dx / len, uy: dy / len, lx: -dy / len, ly: dx / len, len };
}

function computeSteer(veh, headingDeg, a, b, boomM, nudgeM, passLock) {
  const frame = lineFrame(a, b);
  if (!frame || !veh || headingDeg == null || !Number.isFinite(headingDeg)) return null;
  const signedLeft = (veh.x - a.x) * frame.lx + (veh.y - a.y) * frame.ly;
  const nearest = passLock == null ? Math.round((signedLeft - nudgeM) / boomM) : passLock;
  const lineOffset = nearest * boomM + nudgeM;
  const px = a.x + frame.lx * lineOffset;
  const py = a.y + frame.ly * lineOffset;
  const along = (veh.x - px) * frame.ux + (veh.y - py) * frame.uy;
  const closestX = px + frame.ux * along;
  const closestY = py + frame.uy * along;
  const heading = headingDeg * Math.PI / 180;
  const rightX = Math.cos(heading);
  const rightY = -Math.sin(heading);
  const steer = (closestX - veh.x) * rightX + (closestY - veh.y) * rightY;
  return { steer, pass: nearest, frame, lineOffset };
}

function runSelfTest() {
  const north = computeSteer({ x: 2, y: 50 }, 0, { x: 0, y: 0 }, { x: 0, y: 100 }, 10, 0, null);
  const south = computeSteer({ x: 2, y: 50 }, 180, { x: 0, y: 0 }, { x: 0, y: 100 }, 10, 0, null);
  const origin = { lat: 41, lon: -93 };
  const back = toLocal(origin.lat + 0.001, origin.lon, origin);
  return Boolean(
    north && Math.abs(north.steer + 2) < 0.02 && north.pass === 0 &&
    south && Math.abs(south.steer - 2) < 0.02 &&
    Math.abs(back.y - 111.2) < 2
  );
}

function formatDistance(meters) {
  const feet = meters * 3.280839895;
  if (feet < 30) return `${feet.toFixed(0)} ft`;
  return `${Math.round(feet)} ft`;
}

function shownFeet(meters) {
  const feet = meters * 3.280839895;
  return feet < 30 ? Number(feet.toFixed(0)) : Math.round(feet);
}

function formatSpeed(mps) {
  if (mps == null || !Number.isFinite(mps)) return '— mph';
  return `${(mps * 2.2369362921).toFixed(1)} mph`;
}

function formatAcres(squareMeters) {
  const acres = squareMeters / 4046.8564224;
  if (acres < 10) return `${acres.toFixed(1)} ac`;
  return `${Math.round(acres)} ac`;
}

function boomFeet() {
  return Math.round(state.boomM / FEET);
}

function formatPass(pass) {
  if (pass === 0) return 'AB pass';
  const sign = pass > 0 ? '+' : '−';
  return `Pass ${sign}${Math.abs(pass)}`;
}

function setText(el, text) {
  if (el && el.textContent !== text) el.textContent = text;
}

function toast(message) {
  const el = els.toast;
  el.textContent = message;
  el.hidden = false;
  clearTimeout(toast.timer);
  toast.timer = setTimeout(() => { el.hidden = true; }, 2800);
}

function askConfirm(message, yesLabel, action) {
  pendingConfirm = action;
  setText(els.confirmText, message);
  setText(els.confirmYes, yesLabel);
  if (!els.confirm.open) els.confirm.showModal();
}

function loadSettings() {
  try {
    const saved = JSON.parse(localStorage.getItem('fieldnav-settings-v2') || 'null');
    if (!saved) return;
    if (Number.isFinite(saved.boomM)) state.boomM = clamp(saved.boomM, 4 * FEET, 200 * FEET);
    if (Number.isFinite(saved.volume)) {
      const volume = Math.abs(saved.volume - 0.75) < 0.011 ? 0.25 : saved.volume;
      state.volume = clamp(volume, 0, 1);
    }
    state.audio = state.volume > 0;
    if (saved.mount === 0 || saved.mount === 90 || saved.mount === 270) state.mount = saved.mount;
    if (Number.isFinite(saved.deadbandM)) {
      const savedFeet = saved.deadbandM / FEET;
      const feet = Math.abs(savedFeet - 5) < 0.25 ? 10 : savedFeet;
      state.deadbandM = clamp(feet, 1, 20) * FEET;
    }
    if (Number.isFinite(saved.zoom)) {
      const zoom = Math.abs(saved.zoom - 0.78) < 0.02 ? ZOOM_START : saved.zoom;
      state.zoom = clamp(zoom, ZOOM_MIN, ZOOM_MAX);
    }
    if (saved.tally === false) state.tally = false;
    if (Number.isFinite(saved.compassBias)) state.compassBias = clamp(saved.compassBias, -40, 40);
    state.biasSaved = state.compassBias;
  } catch (error) {
    // Keep defaults if storage is blocked.
  }
}

function saveSettings() {
  const payload = {
    boomM: state.boomM,
    audio: state.audio,
    volume: state.volume,
    mount: state.mount,
    deadbandM: state.deadbandM,
    zoom: state.zoom,
    tally: state.tally,
    compassBias: state.compassBias
  };
  try { localStorage.setItem('fieldnav-settings-v2', JSON.stringify(payload)); } catch (error) {}
}

function openDb() {
  if (!dbPromise) {
    dbPromise = new Promise((resolve, reject) => {
      const request = indexedDB.open('fieldnav', 1);
      request.onupgradeneeded = () => request.result.createObjectStore('kv');
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error);
    });
  }
  return dbPromise;
}

async function idbGet(key) {
  const db = await openDb();
  return new Promise((resolve, reject) => {
    const request = db.transaction('kv', 'readonly').objectStore('kv').get(key);
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
}

async function idbSet(key, value) {
  const db = await openDb();
  return new Promise((resolve, reject) => {
    const request = db.transaction('kv', 'readwrite').objectStore('kv').put(value, key);
    request.onsuccess = () => resolve();
    request.onerror = () => reject(request.error);
  });
}

function fieldRecord() {
  return {
    origin: state.origin,
    aGeo: state.aGeo,
    bGeo: state.bGeo,
    nudgeM: state.nudgeM,
    segments: state.segments,
    appliedM2: state.appliedM2,
    passes: state.passes,
    contourPoints: state.contourPoints,
    contourTracking: false,
    guide: state.guide,
    aHeading: state.aHeading,
    nextPoints: state.nextPoints
  };
}

function saveFieldSoon() {
  if (state.mode !== 'live') return;
  clearTimeout(saveTimer);
  saveTimer = setTimeout(saveFieldNow, 2000);
}

async function saveFieldNow() {
  if (state.mode === 'demo') return;
  clearTimeout(saveTimer);
  try { await idbSet('field', fieldRecord()); } catch (error) {}
}

async function loadField() {
  try {
    const field = await idbGet('field');
    if (!field) return;
    state.origin = field.origin || null;
    state.aGeo = field.aGeo || null;
    state.bGeo = field.bGeo || null;
    state.nudgeM = Number.isFinite(field.nudgeM) ? field.nudgeM : 0;
    state.segments = Array.isArray(field.segments) ? field.segments : [];
    state.appliedM2 = Number.isFinite(field.appliedM2) ? field.appliedM2 : 0;
    state.passes = field.passes && typeof field.passes === 'object' ? field.passes : {};
    state.contourPoints = Array.isArray(field.contourPoints) ? field.contourPoints.map((point) => ({ x: point.x, y: point.y })) : [];
    state.contourTracking = false;
    state.nextPoints = Array.isArray(field.nextPoints) ? field.nextPoints.map((point) => ({ x: point.x, y: point.y })) : [];
    state.aHeading = Number.isFinite(field.aHeading) ? field.aHeading : null;
    state.guide = field.guide === 'next' || field.guide === 'saved' ? field.guide : (state.contourPoints.length >= 2 && !field.guide ? 'saved' : 'ab');
    state.rowPoints = [];
    state.turn = null;
    if (state.origin && state.aGeo) state.a = toLocal(state.aGeo.lat, state.aGeo.lon, state.origin);
    if (state.origin && state.bGeo) state.b = toLocal(state.bGeo.lat, state.bGeo.lon, state.origin);
    rebuildCoverage();
  } catch (error) {
    // The cab still runs if storage is unavailable.
  }
}

function snapshotLive() {
  return {
    origin: state.origin,
    a: state.a ? { ...state.a } : null,
    b: state.b ? { ...state.b } : null,
    aGeo: state.aGeo ? { ...state.aGeo } : null,
    bGeo: state.bGeo ? { ...state.bGeo } : null,
    segments: state.segments.slice(),
    nudgeM: state.nudgeM,
    passLock: state.passLock,
    appliedM2: state.appliedM2,
    passes: { ...state.passes },
    contourPoints: state.contourPoints.map((point) => ({ x: point.x, y: point.y })),
    contourTracking: false,
    guide: state.guide,
    aHeading: state.aHeading,
    nextPoints: state.nextPoints.map((point) => ({ x: point.x, y: point.y })),
    rowPoints: [],
    turn: null,
    lastPaint: state.lastPaint ? { ...state.lastPaint } : null
  };
}

function ensureBuffer() {
  if (coverage.canvas) return;
  const canvas = document.createElement('canvas');
  canvas.width = BUFFER;
  canvas.height = BUFFER;
  coverage.canvas = canvas;
  coverage.ctx = canvas.getContext('2d');
}

function bufferPoint(x, y) {
  return { x: BUFFER_CENTER + (x - coverage.ox), y: BUFFER_CENTER - (y - coverage.oy) };
}

function recenterCoverage(pos) {
  if (!pos) return;
  const dx = Math.abs(pos.x - coverage.ox);
  const dy = Math.abs(pos.y - coverage.oy);
  if (dx < BUFFER_CENTER - 220 && dy < BUFFER_CENTER - 220) return;
  coverage.ox = pos.x;
  coverage.oy = pos.y;
  rebuildCoverage();
}

function strokeSegment(x1, y1, x2, y2) {
  ensureBuffer();
  const start = bufferPoint(x1, y1);
  const end = bufferPoint(x2, y2);
  const inside = (point) => point.x > -80 && point.y > -80 && point.x < BUFFER + 80 && point.y < BUFFER + 80;
  if (!inside(start) && !inside(end)) return;
  const ctx = coverage.ctx;
  ctx.lineCap = 'round';
  ctx.lineJoin = 'round';
  ctx.lineWidth = Math.max(1, state.boomM);
  ctx.strokeStyle = 'rgba(214, 255, 74, 0.42)';
  ctx.globalCompositeOperation = 'lighter';
  ctx.beginPath();
  ctx.moveTo(start.x, start.y);
  ctx.lineTo(end.x, end.y);
  ctx.stroke();
}

function rebuildCoverage() {
  ensureBuffer();
  coverage.ctx.clearRect(0, 0, BUFFER, BUFFER);
  state.segments.forEach((segment) => strokeSegment(segment.x1, segment.y1, segment.x2, segment.y2));
}

function maybePaint(pos) {
  if (!state.applying || !pos) return;
  if (state.mode === 'live' && state.fix && shownFeet(state.fix.acc) > 40) return;
  if (state.mode === 'live') {
    const speed = state.fix && state.fix.speed;
    const moving = (speed != null && speed > 0.45) || performance.now() - state.accelTs < 1500;
    if (!moving) return;
  }
  if (!state.lastPaint) {
    state.lastPaint = { x: pos.x, y: pos.y };
    return;
  }
  const dist = Math.hypot(pos.x - state.lastPaint.x, pos.y - state.lastPaint.y);
  if (dist < 0.7) return;
  if (dist > 12) {
    state.lastPaint = { x: pos.x, y: pos.y };
    return;
  }
  const segment = { x1: state.lastPaint.x, y1: state.lastPaint.y, x2: pos.x, y2: pos.y };
  state.segments.push(segment);
  if (state.segments.length > 8000) state.segments.splice(0, state.segments.length - 8000);
  state.appliedM2 += dist * state.boomM;
  const guide = guidanceNow();
  if (guide) state.passes[guide.pass] = 1;
  strokeSegment(segment.x1, segment.y1, segment.x2, segment.y2);
  state.lastPaint = { x: pos.x, y: pos.y };
  saveFieldSoon();
}

function vehicle() {
  if (state.mode === 'demo') return { x: demo.x, y: demo.y };
  return state.stable;
}

function currentHeading() {
  if (state.mode === 'demo') return demo.heading;
  return state.heading;
}

function contourReady() {
  return state.contourPoints.length >= 2;
}

function abPair() {
  if (state.a && state.b) return { a: state.a, b: state.b };
  if (state.a && state.aHeading != null) {
    const rad = state.aHeading * Math.PI / 180;
    return {
      a: state.a,
      b: { x: state.a.x + Math.sin(rad) * 100, y: state.a.y + Math.cos(rad) * 100 }
    };
  }
  return null;
}

function lineAccuracyM() {
  if (state.mode === 'live' && state.fix && Number.isFinite(state.fix.acc)) return state.fix.acc;
  return 4;
}

function lineReady(distance) {
  return distance >= Math.max(55, lineAccuracyM() * 12);
}

function courseReady() {
  if (state.mode === 'demo') return demo.speed > 1.3;
  const fix = state.fix;
  if (!fix || state.heading == null || turningNow()) return false;
  if (fix.speed == null || fix.speed < 1.3) return false;
  const fresh = Number.isFinite(fix.course) && performance.now() - fix.localTs < 2500;
  return fresh || state.headingSource === 'GPS course' || state.headingSource === 'GPS + compass';
}

function courseHeading() {
  if (state.mode === 'demo') return demo.heading;
  const fix = state.fix;
  if (fix && Number.isFinite(fix.course) && performance.now() - fix.localTs < 2500) return fix.course;
  return state.heading;
}

function activeCurve() {
  if (state.guide === 'saved' && contourReady()) return state.contourPoints;
  if (state.guide === 'next' && state.nextPoints.length >= 2) return state.nextPoints;
  return null;
}

function tightBend(points) {
  for (let i = 1; i < points.length - 1; i += 1) {
    const a = points[i - 1];
    const b = points[i];
    const c = points[i + 1];
    const h1 = Math.atan2(b.x - a.x, b.y - a.y) * 180 / Math.PI;
    const h2 = Math.atan2(c.x - b.x, c.y - b.y) * 180 / Math.PI;
    const turn = Math.abs(angleDelta(h1, h2)) * Math.PI / 180;
    const span = Math.hypot(c.x - a.x, c.y - a.y) / 2;
    if (turn > 0.35 && span / turn < state.boomM) return true;
  }
  return false;
}

function polylineLength(points) {
  let length = 0;
  for (let i = 1; i < points.length; i += 1) {
    length += Math.hypot(points[i].x - points[i - 1].x, points[i].y - points[i - 1].y);
  }
  return length;
}

function smoothContour(points) {
  const spaced = [];
  points.forEach((point) => {
    const prev = spaced[spaced.length - 1];
    if (!prev || Math.hypot(point.x - prev.x, point.y - prev.y) >= 4) spaced.push({ x: point.x, y: point.y });
  });
  const last = points[points.length - 1];
  const tail = spaced[spaced.length - 1];
  if (last && tail && Math.hypot(last.x - tail.x, last.y - tail.y) > 1) spaced.push({ x: last.x, y: last.y });
  if (spaced.length < 3) return spaced;
  let current = spaced;
  for (let pass = 0; pass < 2; pass += 1) {
    const next = [current[0]];
    for (let i = 1; i < current.length - 1; i += 1) {
      next.push({
        x: current[i - 1].x * 0.2 + current[i].x * 0.6 + current[i + 1].x * 0.2,
        y: current[i - 1].y * 0.2 + current[i].y * 0.6 + current[i + 1].y * 0.2
      });
    }
    next.push(current[current.length - 1]);
    current = next;
  }
  return current;
}

function pathHeading(points, fromEnd, meters) {
  if (!points || points.length < 2) return null;
  const origin = fromEnd ? points[points.length - 1] : points[0];
  let reached = origin;
  let walked = 0;
  if (fromEnd) {
    for (let i = points.length - 1; i > 0; i -= 1) {
      walked += Math.hypot(points[i].x - points[i - 1].x, points[i].y - points[i - 1].y);
      reached = points[i - 1];
      if (walked >= meters) break;
    }
    const len = Math.hypot(origin.x - reached.x, origin.y - reached.y);
    if (len < 1) return null;
    return { x: origin.x, y: origin.y, ux: (origin.x - reached.x) / len, uy: (origin.y - reached.y) / len };
  }
  for (let i = 0; i < points.length - 1; i += 1) {
    walked += Math.hypot(points[i + 1].x - points[i].x, points[i + 1].y - points[i].y);
    reached = points[i + 1];
    if (walked >= meters) break;
  }
  const len = Math.hypot(reached.x - origin.x, reached.y - origin.y);
  if (len < 1) return null;
  return { x: origin.x, y: origin.y, ux: (reached.x - origin.x) / len, uy: (reached.y - origin.y) / len };
}

function closestOnPolyline(points, veh) {
  let best = null;
  const consider = (start, end, t) => {
    const dx = end.x - start.x;
    const dy = end.y - start.y;
    const len = Math.hypot(dx, dy);
    if (len < 1e-6) return;
    const px = start.x + dx * t;
    const py = start.y + dy * t;
    const dist2 = (veh.x - px) ** 2 + (veh.y - py) ** 2;
    if (best && dist2 >= best.dist2) return;
    const lx = -dy / len;
    const ly = dx / len;
    best = {
      dist2,
      px,
      py,
      lx,
      ly,
      ux: dx / len,
      uy: dy / len,
      signedLeft: (veh.x - px) * lx + (veh.y - py) * ly
    };
  };
  const last = points.length - 2;
  for (let i = 0; i <= last; i += 1) {
    const start = points[i];
    const end = points[i + 1];
    const dx = end.x - start.x;
    const dy = end.y - start.y;
    const len2 = dx * dx + dy * dy;
    if (len2 < 1e-6) continue;
    const t = ((veh.x - start.x) * dx + (veh.y - start.y) * dy) / len2;
    if (t >= 0 && t <= 1) consider(start, end, t);
  }
  const projectRay = (ray, sign) => {
    if (!ray) return;
    const along = ((veh.x - ray.x) * ray.ux + (veh.y - ray.y) * ray.uy) * sign;
    if (along <= 0) return;
    const px = ray.x + ray.ux * sign * along;
    const py = ray.y + ray.uy * sign * along;
    const end = { x: ray.x + ray.ux * sign, y: ray.y + ray.uy * sign };
    consider(ray, end, along);
  };
  projectRay(pathHeading(points, false, 25), -1);
  projectRay(pathHeading(points, true, 25), 1);
  return best;
}

function computeContourSteer(veh, headingDeg, points, boomM, nudgeM, passLock) {
  const hit = closestOnPolyline(points, veh);
  if (!hit || headingDeg == null || !Number.isFinite(headingDeg)) return null;
  const nearest = passLock == null ? Math.round((hit.signedLeft - nudgeM) / boomM) : passLock;
  const lineOffset = nearest * boomM + nudgeM;
  const heading = headingDeg * Math.PI / 180;
  const rightX = Math.cos(heading);
  const rightY = -Math.sin(heading);
  const steer = (hit.px + hit.lx * lineOffset - veh.x) * rightX + (hit.py + hit.ly * lineOffset - veh.y) * rightY;
  return { steer, pass: nearest, frame: { ux: hit.ux, uy: hit.uy, lx: hit.lx, ly: hit.ly }, lineOffset, contour: true };
}

function guidanceNow() {
  const pos = vehicle();
  const heading = currentHeading();
  if (!pos || heading == null) return null;
  const curve = activeCurve();
  if (curve) return computeContourSteer(pos, heading, curve, state.boomM, state.nudgeM, state.passLock);
  if (state.guide !== 'ab') return null;
  const pair = abPair();
  if (!pair) return null;
  return computeSteer(pos, heading, pair.a, pair.b, state.boomM, state.nudgeM, state.passLock);
}

function sampleRow() {
  if (state.guide !== 'next' || !state.applying) return;
  if (state.turn && state.turn.phase === 'turning') return;
  if (turningNow()) return;
  if (state.mode === 'live') {
    if (!state.fix || shownFeet(state.fix.acc) > 40) return;
    if (state.fix.speed != null && state.fix.speed < 0.45) return;
  }
  const pos = vehicle();
  if (!pos) return;
  const last = state.rowPoints[state.rowPoints.length - 1];
  if (last) {
    const gap = Math.hypot(pos.x - last.x, pos.y - last.y);
    if (gap < 2) return;
    if (gap > 30) {
      state.rowHold = (state.rowHold || 0) + 1;
      if (state.rowHold < 3) return;
    } else state.rowHold = 0;
  }
  state.rowPoints.push({ x: pos.x, y: pos.y });
  if (state.rowPoints.length > 2400) {
    const thinned = smoothContour(state.rowPoints);
    if (thinned.length >= 2) state.rowPoints = thinned;
  }
}

function trimTurnTail(points) {
  const cut = points.slice();
  while (cut.length >= 4) {
    const n = cut.length;
    const h1 = Math.atan2(cut[n - 2].x - cut[n - 3].x, cut[n - 2].y - cut[n - 3].y) * 180 / Math.PI;
    const h2 = Math.atan2(cut[n - 1].x - cut[n - 2].x, cut[n - 1].y - cut[n - 2].y) * 180 / Math.PI;
    if (Math.abs(angleDelta(h1, h2)) < 35) break;
    cut.pop();
  }
  return cut;
}

function finishRow(side) {
  const points = trimTurnTail(state.rowPoints);
  if (points.length < 2 || polylineLength(points) < 8) {
    state.rowPoints = [];
    return false;
  }
  const smoothed = smoothContour(points);
  state.nextPoints = smoothed;
  state.rowPoints = [];
  state.passLock = side || null;
  state.turn = null;
  saveFieldSoon();
  toast(tightBend(smoothed)
    ? 'Contour set. A bend is tighter than the boom, so the next pass may pinch.'
    : 'Contour set. The return pass is one boom over.');
  paintToggles();
  return true;
}

function travelSpeed() {
  if (state.mode === 'demo') return demo.speed;
  return state.fix && state.fix.speed;
}

function watchTurn() {
  const speed = travelSpeed();
  if (speed == null || speed < 0.8) return;
  const heading = currentHeading();
  if (heading == null) return;
  let frame = null;
  if (state.guide === 'next' && state.rowPoints.length >= 2) {
    const n = state.rowPoints.length;
    frame = lineFrame(state.rowPoints[n - 2], state.rowPoints[n - 1]);
  }
  if (!frame) {
    const guide = guidanceNow();
    frame = guide && guide.frame;
  }
  if (!frame) return;
  const rad = heading * Math.PI / 180;
  const dot = Math.sin(rad) * frame.ux + Math.cos(rad) * frame.uy;
  if (!state.turn) state.turn = { phase: 'seek', sign: 1, accum: 0, last: heading, since: 0 };
  const turn = state.turn;
  if (turn.phase === 'turning' && performance.now() - turn.since > 20000) {
    turn.phase = 'seek';
    return;
  }
  if (turn.phase === 'seek') {
    if (Math.abs(dot) > 0.75) {
      turn.phase = 'straight';
      turn.sign = dot > 0 ? 1 : -1;
      turn.last = heading;
    }
    return;
  }
  if (turn.phase === 'straight') {
    if (Math.abs(dot) < 0.45) {
      turn.phase = 'turning';
      turn.accum = 0;
      turn.last = heading;
      turn.since = performance.now();
    } else {
      turn.sign = dot > 0 ? 1 : -1;
      turn.last = heading;
    }
    return;
  }
  const step = angleDelta(turn.last, heading);
  if (Math.abs(step) > 40) {
    turn.last = heading;
    return;
  }
  turn.accum += step;
  turn.last = heading;
  if (Math.abs(dot) > 0.75 && Math.sign(dot) === -turn.sign && Math.abs(turn.accum) > 150 && performance.now() - turn.since > 1800) {
    const right = turn.accum > 0;
    const guide = guidanceNow();
    const base = state.passLock == null && guide ? guide.pass : (state.passLock || 0);
    turn.phase = 'seek';
    if (state.guide === 'next' && state.rowPoints.length >= 2) finishRow(right ? -1 : 1);
    else state.passLock = base + (right ? -1 : 1) * turn.sign;
    paintPass();
    return;
  }
  if (Math.abs(dot) > 0.85 && Math.sign(dot) === turn.sign) turn.phase = 'straight';
}

function stepDemo(dt) {
  const previousX = demo.x;
  const previousY = demo.y;
  demo.y += demo.speed * dt;
  demo.x = 2.6 * Math.sin(demo.y / 24);
  const dx = demo.x - previousX;
  const dy = demo.y - previousY;
  if (dx || dy) {
    let heading = Math.atan2(dx, dy) * 180 / Math.PI;
    if (heading < 0) heading += 360;
    demo.heading = heading;
  }
}

function resetDemoPath() {
  state.a = { x: 0, y: 0 };
  state.b = { x: 0, y: 420 };
  state.aGeo = null;
  state.bGeo = null;
  state.nudgeM = 0;
  state.passLock = null;
  state.segments = [];
  state.lastPaint = null;
  state.appliedM2 = 0;
  state.passes = {};
  state.contourTracking = false;
  state.contourPoints = [];
  state.nextPoints = [];
  state.rowPoints = [];
  state.aHeading = null;
  state.guide = 'ab';
  state.turn = null;
  state.applying = true;
  demo.x = 0;
  demo.y = 0;
  demo.heading = 0;
  rebuildCoverage();
  for (let i = 0; i < 460; i += 1) {
    stepDemo(0.1);
    maybePaint(vehicle());
  }
}

function turningNow() {
  return Math.abs(state.yawRate) > 8 && performance.now() - state.yawTs < 500;
}

function updateHeadingTarget() {
  const now = performance.now();
  const compassFresh = state.compass != null && now - state.compassTs < 1200;
  const compass = compassFresh ? normDeg(state.compass + state.compassBias) : null;
  const fix = state.fix;
  const course = fix && Number.isFinite(fix.course) ? fix.course : null;
  const speed = fix && fix.speed != null ? fix.speed : 0;
  const courseFresh = course != null && now - fix.localTs < 2500;
  const turning = turningNow();
  if (compass != null && (!courseFresh || speed < 1.3 || turning)) {
    state.headingTarget = compass;
    state.headingSource = turning ? 'Compass + gyro' : 'Compass';
    return;
  }
  if (compass != null && courseFresh) {
    let trust = clamp((speed - 1.3) / 4.5, 0, 0.86);
    if (state.compassAcc != null && state.compassAcc > 20) {
      trust = clamp(trust + (state.compassAcc - 20) / 80, 0, 0.92);
    }
    state.headingTarget = lerpAngle(compass, course, trust);
    state.headingSource = trust >= 0.45 ? 'GPS + compass' : 'Compass + GPS';
    return;
  }
  if (courseFresh && speed >= 1.3) {
    state.headingTarget = course;
    state.headingSource = 'GPS course';
    return;
  }
  if (!compassFresh && state.headingTarget == null) state.headingSource = 'No heading';
}

function learnCompassBias(dt) {
  if (state.compass == null || !state.fix) return;
  const course = state.fix.course;
  const speed = state.fix.speed;
  const now = performance.now();
  if (course == null || speed == null || speed < 2) return;
  if (now - state.compassTs > 1200 || now - state.fix.localTs > 2000) return;
  if (turningNow()) return;
  const err = angleDelta(state.compass, course);
  if (Math.abs(err) > 35) return;
  const next = state.compassBias + angleDelta(state.compassBias, err) * (1 - Math.exp(-0.12 * dt));
  state.compassBias = clamp(next, -40, 40);
  if (Math.abs(state.compassBias - state.biasSaved) >= 0.4) state.biasDirty = true;
}

function rememberBias() {
  if (!state.biasDirty) return;
  const now = performance.now();
  if (now - state.biasSavedAt < 5000) return;
  state.biasSaved = state.compassBias;
  state.biasSavedAt = now;
  state.biasDirty = false;
  saveSettings();
}

function noteCompass(degrees, accuracy, via) {
  if (!Number.isFinite(degrees)) return;
  if (accuracy != null && accuracy < 0 && via !== 'quaternion') return;
  const adjusted = normDeg(degrees - state.mount);
  if (state.compass != null) {
    const jump = Math.abs(angleDelta(state.compass, adjusted));
    if (jump > 45 && !turningNow()) {
      state.compassRejects += 1;
      if (state.compassRejects < 3) return;
    }
  }
  state.compassRejects = 0;
  state.compassRaw = degrees;
  state.compass = adjusted;
  state.compassTs = performance.now();
  if (via !== 'quaternion') state.eventCompassTs = state.compassTs;
  if (accuracy != null && accuracy >= 0) state.compassAcc = accuracy;
  state.sensorCompass = 'live';
  updateHeadingTarget();
}

function fuseFromGps() {
  updateHeadingTarget();
}

function smoothHeading(dt) {
  if (state.mode === 'demo') {
    state.heading = demo.heading;
    state.headingSource = 'Demo path';
    return;
  }
  const yawFresh = performance.now() - state.yawTs < 400 && Number.isFinite(state.yawRate);
  if (state.heading != null && yawFresh) state.heading = normDeg(state.heading + state.yawRate * dt);
  learnCompassBias(dt);
  if (state.headingTarget == null) {
    state.headingSource = state.heading == null ? 'No heading' : (yawFresh ? 'Gyro' : 'No heading');
    return;
  }
  if (state.heading == null) {
    state.heading = state.headingTarget;
    return;
  }
  const gpsLed = state.headingSource === 'GPS + compass' || state.headingSource === 'GPS course';
  const rate = turningNow() ? 0.85 : gpsLed ? 2.4 : 1.15;
  state.heading = lerpAngle(state.heading, state.headingTarget, 1 - Math.exp(-rate * dt));
}

function headingFromOrientationEvent(event) {
  if (typeof event.webkitCompassHeading === 'number' && Number.isFinite(event.webkitCompassHeading)) {
    return event.webkitCompassHeading;
  }
  if (event.absolute === true && typeof event.alpha === 'number' && Number.isFinite(event.alpha)) {
    return (360 - event.alpha) % 360;
  }
  return null;
}

function rotateVector(q, v) {
  const [x, y, z, w] = q;
  const [vx, vy, vz] = v;
  const ix = w * vx + y * vz - z * vy;
  const iy = w * vy + z * vx - x * vz;
  const iz = w * vz + x * vy - y * vx;
  const iw = -x * vx - y * vy - z * vz;
  return [
    ix * w + iw * -x + iy * -z - iz * -y,
    iy * w + iw * -y + iz * -x - ix * -z,
    iz * w + iw * -z + ix * -y - iy * -x
  ];
}

function headingFromQuaternion(q) {
  if (!q || q.length < 4) return null;
  const top = rotateVector(q, [0, 1, 0]);
  if (Math.hypot(top[0], top[1]) < 0.2) return null;
  let heading = Math.atan2(top[0], top[1]) * 180 / Math.PI;
  if (heading < 0) heading += 360;
  return heading;
}

function onOrientation(event) {
  const heading = headingFromOrientationEvent(event);
  if (heading == null) return;
  const accuracy = typeof event.webkitCompassAccuracy === 'number' ? event.webkitCompassAccuracy : null;
  noteCompass(heading, accuracy, 'event');
}

function yawFromMotion(event) {
  const rate = event.rotationRate;
  if (!rate) return null;
  const gx = rate.beta;
  const gy = rate.gamma;
  const gz = rate.alpha;
  if (!Number.isFinite(gx) || !Number.isFinite(gy) || !Number.isFinite(gz)) return null;
  const gravity = event.accelerationIncludingGravity;
  if (gravity && Number.isFinite(gravity.x) && Number.isFinite(gravity.y) && Number.isFinite(gravity.z)) {
    const mag = Math.hypot(gravity.x, gravity.y, gravity.z);
    if (mag > 6 && mag < 14) state.up = { x: -gravity.x / mag, y: -gravity.y / mag, z: -gravity.z / mag };
  }
  if (!state.up) return -gz;
  return -(gx * state.up.x + gy * state.up.y + gz * state.up.z);
}

function onMotion(event) {
  state.sensorMotion = 'live';
  const yaw = yawFromMotion(event);
  if (yaw != null) {
    state.yawRate = yaw;
    state.gyroZ = yaw;
    state.yawTs = performance.now();
  }
  const linear = event.acceleration;
  if (linear && linear.x != null) {
    const magnitude = Math.hypot(linear.x || 0, linear.y || 0, linear.z || 0);
    if (magnitude > 0.55) state.accelTs = performance.now();
    return;
  }
  const gravity = event.accelerationIncludingGravity;
  if (!gravity || gravity.x == null) return;
  if (!onMotion.grav) onMotion.grav = { x: gravity.x, y: gravity.y, z: gravity.z };
  const grav = onMotion.grav;
  grav.x = grav.x * 0.9 + gravity.x * 0.1;
  grav.y = grav.y * 0.9 + gravity.y * 0.1;
  grav.z = grav.z * 0.9 + gravity.z * 0.1;
  const magnitude = Math.hypot(gravity.x - grav.x, gravity.y - grav.y, gravity.z - grav.z);
  if (magnitude > 0.45) state.accelTs = performance.now();
}

function onFix(position) {
  const coords = position.coords;
  const accuracy = Number.isFinite(coords.accuracy) ? coords.accuracy : 30;
  state.gpsError = '';
  const timestamp = position.timestamp || Date.now();
  const gap = state.fix ? (timestamp - state.fix.ts) / 1000 : 0;
  const interrupted = gap > 6;
  if (accuracy > 45 && state.stable && !interrupted) {
    state.sensorGps = 'weak';
    return;
  }
  if (!state.origin) state.origin = { lat: coords.latitude, lon: coords.longitude };
  const local = toLocal(coords.latitude, coords.longitude, state.origin);
  const previous = state.stable ? { x: state.stable.x, y: state.stable.y } : null;
  const speed = coords.speed == null || coords.speed < 0 ? null : coords.speed;
  let travel = speed;
  if (travel == null && state.fix && state.stable && !interrupted) {
    const step = Math.max(0.3, (timestamp - state.fix.ts) / 1000);
    const derived = Math.hypot(local.x - state.stable.x, local.y - state.stable.y) / step;
    if (derived >= 0.3 && derived < 12) travel = derived;
  }
  if (interrupted) {
    state.stable = { x: local.x, y: local.y };
    state.lastPaint = null;
    state.turn = null;
  } else if (state.stable && state.fix) {
    const dist = Math.hypot(local.x - state.stable.x, local.y - state.stable.y);
    const dt = Math.max(0.2, (timestamp - state.fix.ts) / 1000);
    const limit = Math.max(12, (travel || 0) * dt * 4 + accuracy);
    if (dist > limit && dist > 8) {
      state.sensorGps = 'reject';
      return;
    }
  }
  const moving = (travel != null && travel > 0.45) || performance.now() - state.accelTs < 1500;
  const feet = shownFeet(accuracy);
  if (!state.stable) state.stable = { x: local.x, y: local.y };
  else if (moving || feet <= 40) absorbFix(local, feet, moving);
  gpsTrail.push({ x: local.x, y: local.y, acc: accuracy, ts: performance.now() });
  const trailCutoff = performance.now() - 2500;
  while (gpsTrail.length && gpsTrail[0].ts < trailCutoff) gpsTrail.shift();
  if (gpsTrail.length > 12) gpsTrail.splice(0, gpsTrail.length - 12);
  state.rough = feet > 40;
  let course = Number.isFinite(coords.heading) ? coords.heading : null;
  if (course == null && previous && travel != null && travel > 0.8) {
    const dx = local.x - previous.x;
    const dy = local.y - previous.y;
    if (Math.hypot(dx, dy) > 1) {
      let bearing = Math.atan2(dx, dy) * 180 / Math.PI;
      if (bearing < 0) bearing += 360;
      course = bearing;
    }
  }
  if (interrupted) courseSmooth = course;
  else if (course != null) courseSmooth = courseSmooth == null ? course : lerpAngle(courseSmooth, course, (travel || 0) > 2 ? 0.4 : 0.18);
  state.fix = {
    acc: accuracy,
    speed: travel,
    course: courseSmooth,
    ts: timestamp,
    localTs: performance.now(),
    held: !moving
  };
  state.sensorGps = feet <= 20 ? 'good' : feet <= 40 ? 'fair' : 'poor';
  fuseFromGps();
}

function absorbFix(local, feet, moving) {
  let crossGain = feet <= 8 ? 0.22 : feet <= 20 ? 0.14 : feet <= 40 ? 0.07 : 0.03;
  let alongGain = feet <= 20 ? 0.72 : feet <= 40 ? 0.42 : 0.18;
  if (!moving) {
    crossGain *= 0.45;
    alongGain *= 0.45;
  }
  const dx = local.x - state.stable.x;
  const dy = local.y - state.stable.y;
  const frame = state.a && state.b ? lineFrame(state.a, state.b) : null;
  if (!frame) {
    const gain = Math.max(crossGain, alongGain * 0.85);
    state.stable.x += dx * gain;
    state.stable.y += dy * gain;
    return;
  }
  const along = dx * frame.ux + dy * frame.uy;
  const cross = dx * frame.lx + dy * frame.ly;
  state.stable.x += frame.ux * along * alongGain + frame.lx * cross * crossGain;
  state.stable.y += frame.uy * along * alongGain + frame.ly * cross * crossGain;
}

function coastPosition(dt) {
  if (state.mode !== 'live' || !state.stable || !state.fix || state.fix.held) return;
  const age = (performance.now() - state.fix.localTs) / 1000;
  if (age < 0.05 || age > 6) return;
  const speed = state.fix.speed;
  const heading = state.heading;
  if (speed == null || speed < 0.6 || heading == null) return;
  const radians = heading * Math.PI / 180;
  const vx = Math.sin(radians) * speed;
  const vy = Math.cos(radians) * speed;
  let frame = null;
  const curve = activeCurve();
  if (curve) {
    const hit = closestOnPolyline(curve, state.stable);
    if (hit) frame = { ux: hit.ux, uy: hit.uy };
  }
  if (!frame && state.a && state.b) frame = lineFrame(state.a, state.b);
  if (frame) {
    const along = vx * frame.ux + vy * frame.uy;
    state.stable.x += frame.ux * along * dt;
    state.stable.y += frame.uy * along * dt;
    return;
  }
  state.stable.x += vx * dt;
  state.stable.y += vy * dt;
}

function markFix() {
  if (state.mode !== 'live') return vehicle();
  const now = performance.now();
  const fresh = gpsTrail.filter((point) => now - point.ts < 2000 && shownFeet(point.acc) <= 40);
  if (fresh.length < 2) return vehicle();
  let weightSum = 0;
  let x = 0;
  let y = 0;
  fresh.forEach((point) => {
    const weight = 1 / Math.max(20 * FEET, point.acc);
    weightSum += weight;
    x += point.x * weight;
    y += point.y * weight;
  });
  return { x: x / weightSum, y: y / weightSum };
}

function onFixError(error) {
  state.sensorGps = 'error';
  state.gpsError = error && error.code === 1 ? 'Location permission denied' : 'GPS unavailable';
}

function startLiveSensors() {
  if (state.mode !== 'live' || document.visibilityState !== 'visible') return;
  gpsRestartAt = performance.now();
  if (navigator.geolocation && sensors.watchId == null) {
    sensors.watchId = navigator.geolocation.watchPosition(onFix, onFixError, {
      enableHighAccuracy: true,
      maximumAge: 0,
      timeout: 15000
    });
    state.sensorGps = 'searching';
  } else if (!navigator.geolocation) {
    state.sensorGps = 'unavailable';
  }
  if (!sensors.orientationOn) {
    window.addEventListener('deviceorientationabsolute', onOrientation, true);
    window.addEventListener('deviceorientation', onOrientation, true);
    sensors.orientationOn = true;
  }
  if (!sensors.motionOn) {
    window.addEventListener('devicemotion', onMotion);
    sensors.motionOn = true;
  }
  startAbsoluteSensor();
}

function stopLiveSensors() {
  if (sensors.watchId != null && navigator.geolocation) {
    navigator.geolocation.clearWatch(sensors.watchId);
    sensors.watchId = null;
  }
  if (sensors.orientationOn) {
    window.removeEventListener('deviceorientationabsolute', onOrientation, true);
    window.removeEventListener('deviceorientation', onOrientation, true);
    sensors.orientationOn = false;
  }
  if (sensors.motionOn) {
    window.removeEventListener('devicemotion', onMotion);
    sensors.motionOn = false;
  }
  if (sensors.absSensor) {
    try { sensors.absSensor.stop(); } catch (error) {}
    sensors.absSensor = null;
  }
  if (state.mode === 'live' && document.visibilityState === 'hidden') {
    state.sensorGps = 'paused';
    state.sensorCompass = 'paused';
    state.sensorMotion = 'paused';
  }
}

function startAbsoluteSensor() {
  if (sensors.absSensor || typeof AbsoluteOrientationSensor !== 'function') return;
  try {
    const sensor = new AbsoluteOrientationSensor({ frequency: 20 });
    sensor.onreading = () => {
      if (performance.now() - state.eventCompassTs < 400) return;
      const heading = headingFromQuaternion(sensor.quaternion);
      if (heading == null) return;
      noteCompass(heading, null, 'quaternion');
    };
    sensor.onerror = () => {
      if (state.sensorCompass !== 'live') state.sensorCompass = 'blocked';
    };
    sensor.start();
    sensors.absSensor = sensor;
  } catch (error) {
    if (state.sensorCompass !== 'live') state.sensorCompass = 'unavailable';
  }
}

async function requestSensorPermissions() {
  const jobs = [];
  try {
    if (typeof DeviceOrientationEvent !== 'undefined' && typeof DeviceOrientationEvent.requestPermission === 'function') {
      jobs.push(DeviceOrientationEvent.requestPermission());
    }
    if (typeof DeviceMotionEvent !== 'undefined' && typeof DeviceMotionEvent.requestPermission === 'function') {
      jobs.push(DeviceMotionEvent.requestPermission());
    }
    if (!jobs.length) return true;
    const results = await Promise.all(jobs);
    const granted = results.every((result) => result === 'granted');
    if (!granted) state.sensorCompass = 'denied';
    return granted;
  } catch (error) {
    state.sensorCompass = 'denied';
    return false;
  }
}

function onWakeRelease(event) {
  if (event && event.target && event.target !== wakeLock) return;
  wakeLock = null;
  state.awake = false;
  paintWake();
  if (wantWake && document.visibilityState === 'visible') holdWake(true);
}

async function holdWake(on) {
  const token = ++wakeToken;
  wantWake = on && document.visibilityState === 'visible';
  if (!wantWake) {
    const lock = wakeLock;
    wakeLock = null;
    if (lock) {
      try { await lock.release(); } catch (error) {}
    }
    if (token !== wakeToken) return;
    state.awake = false;
    paintWake();
    return;
  }
  if (wakeLock) {
    state.awake = true;
    paintWake();
    return;
  }
  if (!navigator.wakeLock) {
    state.awake = false;
    state.wakeNote = 'This browser cannot hold the screen on';
    paintWake();
    return;
  }
  try {
    const lock = await navigator.wakeLock.request('screen');
    if (token !== wakeToken || !wantWake) {
      try { await lock.release(); } catch (error) {}
      return;
    }
    wakeLock = lock;
    wakeLock.addEventListener('release', onWakeRelease);
    state.awake = true;
    state.wakeNote = '';
  } catch (error) {
    if (token !== wakeToken) return;
    state.awake = false;
    state.wakeNote = 'Tap the screen once to keep it awake';
  }
  paintWake();
}

function paintWake() {
  document.documentElement.dataset.awake = state.awake ? 'yes' : 'no';
  if (els.wakeDot) els.wakeDot.classList.toggle('on', state.awake);
  if (els.wakeState) {
    const text = document.visibilityState !== 'visible'
      ? 'Resting while Field Nav is in the background'
      : state.awake
        ? 'Screen awake while Field Nav is open'
        : (state.wakeNote || 'Requesting screen wake');
    setText(els.wakeState, text);
  }
}

function audioNeedsResume() {
  return audioCtx && audioCtx.state !== 'running' && audioCtx.state !== 'closed';
}

function ensureAudio() {
  const Context = window.AudioContext || window.webkitAudioContext;
  if (!Context) return null;
  if (!audioCtx) {
    audioCtx = new Context();
    audioCtx.addEventListener('statechange', () => {
      if (document.visibilityState === 'visible' && state.running && state.audio && audioNeedsResume()) {
        audioCtx.resume().catch(() => {});
      }
    });
  }
  if (audioNeedsResume()) audioCtx.resume().catch(() => {});
  return audioCtx;
}

function tone(frequency, panValue) {
  const ctx = audioCtx;
  if (!ctx || ctx.state !== 'running') return;
  const now = ctx.currentTime;
  const osc = ctx.createOscillator();
  const gain = ctx.createGain();
  osc.type = 'square';
  osc.frequency.value = frequency;
  gain.gain.setValueAtTime(0.0001, now);
  gain.gain.exponentialRampToValueAtTime(Math.max(0.001, 0.2 * state.volume), now + 0.012);
  gain.gain.exponentialRampToValueAtTime(0.0001, now + 0.12);
  let node = gain;
  if (ctx.createStereoPanner) {
    const pan = ctx.createStereoPanner();
    pan.pan.value = panValue;
    gain.connect(pan);
    node = pan;
  }
  osc.connect(gain);
  node.connect(ctx.destination);
  osc.start(now);
  osc.stop(now + 0.13);
  state.beepFlash = performance.now();
  state.beepCount += 1;
}

function serviceAudio(steer) {
  if (!state.audio || !state.running || document.visibilityState !== 'visible') return;
  if (!steer || steer.steer == null) return;
  const magnitude = Math.abs(steer.steer);
  if (magnitude < state.deadbandM) return;
  const span = clamp((magnitude - state.deadbandM) / 2.5, 0, 1);
  const interval = 760 - span * 600;
  const now = performance.now();
  if (now - lastBeep < interval) return;
  lastBeep = now;
  if (!ensureAudio()) return;
  tone(steer.steer > 0 ? 784 : 494, steer.steer > 0 ? 0.9 : -0.9);
}

function pauseField() {
  state.turn = null;
  state.lastPaint = null;
  if (audioCtx && audioCtx.state === 'running') audioCtx.suspend();
  stopLiveSensors();
  stopLoop();
  holdWake(false);
}

function syncSession() {
  const visible = document.visibilityState === 'visible';
  if (!visible) {
    pauseField();
    paintWake();
    return;
  }
  holdWake(true);
  if (!state.running) {
    stopLiveSensors();
    stopLoop();
    if (audioCtx && audioCtx.state === 'running') audioCtx.suspend();
    paintWake();
    return;
  }
  if (state.mode === 'live') startLiveSensors();
  if (state.audio) ensureAudio();
  startLoop();
  paintWake();
}

function reviveGps() {
  if (state.mode !== 'live' || !state.running || document.visibilityState !== 'visible') return;
  if (state.gpsError === 'Location permission denied') return;
  const age = state.fix ? (performance.now() - state.fix.localTs) / 1000 : 999;
  if (age < 8 || performance.now() - gpsRestartAt < 8000) return;
  gpsRestartAt = performance.now();
  if (sensors.watchId != null && navigator.geolocation) {
    navigator.geolocation.clearWatch(sensors.watchId);
    sensors.watchId = null;
  }
  state.sensorGps = 'searching';
  startLiveSensors();
}

function showSplash() {
  if (state.mode === 'demo') {
    Object.assign(state, liveHold || {});
    liveHold = null;
    state.applying = false;
    state.lastPaint = null;
    rebuildCoverage();
  }
  state.mode = 'idle';
  state.running = false;
  els.splash.hidden = false;
  els.cab.hidden = true;
  document.body.dataset.steer = 'none';
  syncSession();
}

function showCab() {
  els.splash.hidden = true;
  els.cab.hidden = false;
  resizeCanvas();
  paintStatic();
}

function enterDemo() {
  if (state.mode !== 'demo') liveHold = snapshotLive();
  state.mode = 'demo';
  state.running = true;
  resetDemoPath();
  showCab();
  syncSession();
}

async function enterLive() {
  if (state.mode === 'demo' && liveHold) {
    Object.assign(state, liveHold);
    liveHold = null;
    rebuildCoverage();
  }
  state.mode = 'live';
  state.running = true;
  state.applying = false;
  state.lastPaint = null;
  showCab();
  syncSession();
}

function useStraightLine() {
  if (state.guide === 'ab' || !abPair()) return false;
  state.guide = 'ab';
  state.passLock = null;
  state.turn = null;
  state.rowPoints = [];
  toast(state.b ? 'Guiding on A-B' : 'Guiding on A+');
  paintToggles();
  return true;
}

function markA() {
  if (useStraightLine()) return;
  if (state.a && state.b) {
    toast('Clear the line in settings to mark a new A');
    return;
  }
  const pos = markFix();
  if (!pos) {
    toast('Waiting for a GPS fix');
    return;
  }
  state.a = { x: pos.x, y: pos.y };
  state.b = null;
  state.aHeading = null;
  state.guide = 'ab';
  state.passLock = null;
  state.turn = null;
  if (state.mode === 'live' && state.fix && state.origin) {
    state.aGeo = toGeo(pos.x, pos.y);
    state.bGeo = null;
    saveFieldSoon();
  }
  if (courseReady()) {
    state.aHeading = courseHeading();
    toast('A+ set. The line follows your GPS heading through A.');
  } else {
    const rough = state.mode === 'live' && state.fix && shownFeet(state.fix.acc) > 40;
    toast(rough
      ? 'A marked. GPS is wider than 40 ft, so this point may be off.'
      : 'A marked. Drive straight to set the A+ heading.');
  }
  state.applying = true;
  state.lastPaint = null;
  paintStatic();
}

function lockAPlus() {
  if (state.guide !== 'ab' || !state.a || state.b || state.aHeading != null || !courseReady()) return;
  state.aHeading = courseHeading();
  saveFieldSoon();
  toast('A+ set. The line follows your GPS heading through A.');
}

function toGeo(x, y) {
  const lat0 = state.origin.lat * Math.PI / 180;
  return {
    lat: state.origin.lat + (y / EARTH) * 180 / Math.PI,
    lon: state.origin.lon + (x / (EARTH * Math.cos(lat0))) * 180 / Math.PI
  };
}

function markB() {
  if (!state.a) {
    toast('Mark A first');
    return;
  }
  if (state.b) {
    if (useStraightLine()) return;
    toast('B is already set');
    return;
  }
  const pos = markFix();
  if (!pos) {
    toast('Waiting for a GPS fix');
    return;
  }
  const distance = Math.hypot(pos.x - state.a.x, pos.y - state.a.y);
  if (distance < 8) {
    toast('Drive a bit farther down the row');
    return;
  }
  state.aHeading = null;
  state.b = { x: pos.x, y: pos.y };
  state.guide = 'ab';
  if (state.mode === 'live' && state.origin) {
    state.bGeo = toGeo(pos.x, pos.y);
    saveFieldSoon();
  }
  const rough = state.mode === 'live' && state.fix && shownFeet(state.fix.acc) > 40;
  const loose = !lineReady(distance);
  if (rough) toast('B marked. GPS is wider than 40 ft, so this point may be off.');
  else if (loose) toast('B marked. The line is still short, so the heading can wander.');
  else toast('B marked. Apply is on.');
  state.applying = true;
  state.lastPaint = null;
  paintStatic();
}

function shiftLineHere() {
  const pos = vehicle();
  const guide = guidanceNow();
  if (!pos || !guide) {
    toast(state.guide === 'next' ? 'Drive the contour before shifting' : 'Set a line before shifting');
    return;
  }
  let signed = 0;
  const curve = activeCurve();
  if (curve) {
    const hit = closestOnPolyline(curve, pos);
    if (!hit) return;
    signed = hit.signedLeft;
  } else {
    const pair = abPair();
    const frame = pair && lineFrame(pair.a, pair.b);
    if (!frame) return;
    signed = (pos.x - pair.a.x) * frame.lx + (pos.y - pair.a.y) * frame.ly;
  }
  const pass = state.passLock == null ? guide.pass : state.passLock;
  state.nudgeM = clamp(signed - pass * state.boomM, -state.boomM, state.boomM);
  saveFieldSoon();
  toast('Line shifted under you');
}

function nudgeLine(direction) {
  const pos = vehicle();
  let frame = null;
  if (contourReady() && pos) {
    const hit = closestOnPolyline(state.contourPoints, pos);
    if (hit) frame = hit;
  } else if (state.a && state.b) {
    frame = lineFrame(state.a, state.b);
  }
  if (!frame && !contourReady() && !(state.a && state.b)) {
    toast(state.contourTracking ? 'Finish the contour before shifting the line' : 'Mark A and B before shifting the line');
    return;
  }
  const step = 0.0508;
  const heading = currentHeading();
  if (!frame || heading == null) {
    state.nudgeM += direction * step;
  } else {
    const radians = heading * Math.PI / 180;
    const align = frame.lx * Math.cos(radians) + frame.ly * -Math.sin(radians);
    const denom = Math.abs(align) < 0.35 ? Math.sign(align || 1) * 0.35 : align;
    state.nudgeM += (direction * step) / denom;
  }
  state.nudgeM = clamp(state.nudgeM, -state.boomM, state.boomM);
  saveFieldSoon();
  toast(direction > 0 ? 'Line moved right' : 'Line moved left');
}

function stepWidth(direction) {
  state.boomM = clamp(boomFeet() + direction, 4, 200) * FEET;
  rebuildCoverage();
  saveSettings();
  paintWidth();
}

function setApplying(on) {
  state.applying = on;
  state.lastPaint = null;
  paintToggles();
}

function clearContour() {
  state.contourTracking = false;
  state.contourPoints = [];
  state.nextPoints = [];
  state.rowPoints = [];
  state.turn = null;
  if (state.guide !== 'ab') state.guide = 'ab';
  saveFieldSoon();
  toast('Contour line cleared');
  paintStatic();
}

function curveReady() {
  return state.nextPoints.length >= 2 || contourReady();
}

function contourRecording() {
  return state.guide === 'next' && state.nextPoints.length < 2 && !contourReady();
}

function toggleNext() {
  if (contourRecording()) {
    if (!state.applying) {
      state.applying = true;
      state.lastPaint = null;
      toast('Recording contour. Drive the row.');
      paintStatic();
      return;
    }
    if (state.rowPoints.length >= 2 && polylineLength(state.rowPoints) >= 8) {
      finishRow(null);
      return;
    }
    toast('Drive the contour, then tap Recording again');
    return;
  }
  if (curveReady()) {
    if (state.guide === 'ab') {
      state.guide = state.nextPoints.length >= 2 ? 'next' : 'saved';
      state.passLock = null;
      state.turn = null;
      state.rowPoints = [];
      state.applying = true;
      state.lastPaint = null;
      toast('Guiding on contour');
      paintStatic();
      return;
    }
    toast('Contour is set. Clear it in settings to record a new one.');
    return;
  }
  const pos = vehicle();
  if (!pos) {
    toast('Waiting for a GPS fix');
    return;
  }
  state.guide = 'next';
  state.passLock = null;
  state.turn = null;
  state.rowPoints = [];
  state.applying = true;
  state.lastPaint = null;
  saveFieldSoon();
  toast('Recording contour. Drive the row.');
  paintStatic();
}

function clearLine() {
  state.a = null;
  state.b = null;
  state.aGeo = null;
  state.bGeo = null;
  state.aHeading = null;
  state.nudgeM = 0;
  state.passLock = null;
  state.turn = null;
  saveFieldSoon();
  toast('A-B line cleared');
  paintStatic();
}

function newField() {
  state.origin = null;
  state.a = null;
  state.b = null;
  state.aGeo = null;
  state.bGeo = null;
  state.segments = [];
  state.nudgeM = 0;
  state.passLock = null;
  state.appliedM2 = 0;
  state.passes = {};
  state.contourTracking = false;
  state.contourPoints = [];
  state.nextPoints = [];
  state.rowPoints = [];
  state.aHeading = null;
  state.guide = 'ab';
  state.turn = null;
  state.stable = null;
  state.fix = null;
  state.lastPaint = null;
  gpsTrail.length = 0;
  coverage.ox = 0;
  coverage.oy = 0;
  rebuildCoverage();
  if (state.mode === 'demo') {
    demo.x = 0;
    demo.y = 0;
    demo.heading = 0;
  } else saveFieldNow();
  toast('Field cleared');
  paintStatic();
}

function currentPassNumber() {
  const guide = guidanceNow();
  if (guide) return guide.pass;
  return state.passLock || 0;
}

function screenAnchor() {
  return { cx: els.map.width / 2, cy: els.map.height * 0.64 };
}

function pixelsPerMeter() {
  return BASE_PPM * state.zoom * (els.map.width / Math.max(1, els.map.getBoundingClientRect().width));
}

function applyWorldTransform(headingDeg, pos) {
  const ppm = pixelsPerMeter();
  const heading = headingDeg * Math.PI / 180;
  const cos = Math.cos(heading);
  const sin = Math.sin(heading);
  const anchor = screenAnchor();
  const ctx = els.ctx;
  ctx.setTransform(
    ppm * cos, -ppm * sin,
    -ppm * sin, -ppm * cos,
    anchor.cx - pos.x * ppm * cos + pos.y * ppm * sin,
    anchor.cy + pos.x * ppm * sin + pos.y * ppm * cos
  );
  return ppm;
}

function resizeCanvas() {
  const rect = els.map.getBoundingClientRect();
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  const width = Math.max(1, Math.round(rect.width * dpr));
  const height = Math.max(1, Math.round(rect.height * dpr));
  if (els.map.width !== width || els.map.height !== height) {
    els.map.width = width;
    els.map.height = height;
  }
}

function drawGrid(ctx, pos, ppm) {
  const step = 20;
  const range = Math.max(els.map.width, els.map.height) / Math.max(ppm, 0.01);
  const x0 = Math.floor((pos.x - range) / step) * step;
  const y0 = Math.floor((pos.y - range) / step) * step;
  ctx.beginPath();
  ctx.strokeStyle = 'rgba(214, 255, 74, 0.08)';
  ctx.lineWidth = 1 / ppm;
  for (let x = x0; x <= pos.x + range; x += step) {
    ctx.moveTo(x, pos.y - range);
    ctx.lineTo(x, pos.y + range);
  }
  for (let y = y0; y <= pos.y + range; y += step) {
    ctx.moveTo(pos.x - range, y);
    ctx.lineTo(pos.x + range, y);
  }
  ctx.stroke();
}

function offsetPolyline(points, distance) {
  return points.map((point, index) => {
    let lx = 0;
    let ly = 0;
    if (index < points.length - 1) {
      const dx = points[index + 1].x - point.x;
      const dy = points[index + 1].y - point.y;
      const len = Math.hypot(dx, dy) || 1;
      lx += -dy / len;
      ly += dx / len;
    }
    if (index > 0) {
      const dx = point.x - points[index - 1].x;
      const dy = point.y - points[index - 1].y;
      const len = Math.hypot(dx, dy) || 1;
      lx += -dy / len;
      ly += dx / len;
    }
    const len = Math.hypot(lx, ly) || 1;
    return { x: point.x + (lx / len) * distance, y: point.y + (ly / len) * distance };
  });
}

function drawPolyline(ctx, ppm, path, active) {
  if (path.length < 2) return;
  ctx.beginPath();
  path.forEach((point, index) => {
    if (index) ctx.lineTo(point.x, point.y);
    else ctx.moveTo(point.x, point.y);
  });
  ctx.strokeStyle = active ? 'rgba(214, 255, 74, 0.95)' : 'rgba(168, 181, 150, 0.45)';
  ctx.lineWidth = (active ? 2.5 : 1.2) / ppm;
  ctx.stroke();
}

function extendPath(points, distance) {
  if (points.length < 2) return points;
  const head = pathHeading(points, false, 25);
  const tail = pathHeading(points, true, 25);
  if (!head || !tail) return points;
  return [
    { x: head.x - head.ux * distance, y: head.y - head.uy * distance },
    ...points,
    { x: tail.x + tail.ux * distance, y: tail.y + tail.uy * distance }
  ];
}

function visiblePassCount(ppm) {
  const reach = Math.max(els.map.width, els.map.height) / Math.max(ppm, 0.01) / 2;
  return clamp(Math.ceil(reach / Math.max(state.boomM, 1)) + 1, 4, 10);
}

function drawFaintLine(ctx, ppm, a, b) {
  const frame = lineFrame(a, b);
  if (!frame) return;
  ctx.beginPath();
  ctx.moveTo(a.x - frame.ux * 4000, a.y - frame.uy * 4000);
  ctx.lineTo(a.x + frame.ux * 4000, a.y + frame.uy * 4000);
  ctx.strokeStyle = 'rgba(168, 181, 150, 0.28)';
  ctx.lineWidth = 1.2 / ppm;
  ctx.stroke();
}

function drawContour(ctx, ppm, guide, points) {
  const path = extendPath(points, 2000);
  ctx.lineCap = 'round';
  ctx.lineJoin = 'round';
  if (!guide || !guide.contour) {
    drawPolyline(ctx, ppm, path, true);
    return;
  }
  const count = visiblePassCount(ppm);
  for (let offset = -count; offset <= count; offset += 1) {
    const lineOffset = (guide.pass + offset) * state.boomM + state.nudgeM;
    drawPolyline(ctx, ppm, offsetPolyline(path, lineOffset), offset === 0);
  }
}

function drawSwaths(ctx, pos, ppm, guide) {
  if (!guide || guide.contour) return;
  const { frame } = guide;
  ctx.lineCap = 'butt';
  const count = visiblePassCount(ppm);
  for (let offset = -count; offset <= count; offset += 1) {
    const pass = guide.pass + offset;
    const lineOffset = pass * state.boomM + state.nudgeM;
    const px = state.a.x + frame.lx * lineOffset;
    const py = state.a.y + frame.ly * lineOffset;
    ctx.beginPath();
    ctx.moveTo(px - frame.ux * 4000, py - frame.uy * 4000);
    ctx.lineTo(px + frame.ux * 4000, py + frame.uy * 4000);
    ctx.strokeStyle = offset === 0 ? 'rgba(214, 255, 74, 0.95)' : 'rgba(168, 181, 150, 0.45)';
    ctx.lineWidth = (offset === 0 ? 2.5 : 1.2) / ppm;
    ctx.stroke();
  }
}

function drawBoom(ctx, pos, headingDeg, ppm) {
  const heading = headingDeg * Math.PI / 180;
  const forwardX = Math.sin(heading);
  const forwardY = Math.cos(heading);
  const leftX = -forwardY;
  const leftY = forwardX;
  const half = state.boomM / 2;
  ctx.beginPath();
  ctx.moveTo(pos.x + leftX * half, pos.y + leftY * half);
  ctx.lineTo(pos.x - leftX * half, pos.y - leftY * half);
  ctx.strokeStyle = state.applying ? 'rgba(214, 255, 74, 0.95)' : 'rgba(244, 247, 241, 0.7)';
  ctx.lineWidth = 4 / ppm;
  ctx.stroke();
  ctx.beginPath();
  ctx.moveTo(pos.x, pos.y);
  ctx.lineTo(pos.x + forwardX * 16, pos.y + forwardY * 16);
  ctx.strokeStyle = 'rgba(244, 247, 241, 0.85)';
  ctx.lineWidth = 2 / ppm;
  ctx.stroke();
}

function drawMarker(ctx, point, ppm, color) {
  ctx.beginPath();
  ctx.arc(point.x, point.y, 5 / ppm, 0, Math.PI * 2);
  ctx.fillStyle = color;
  ctx.fill();
}

function draw() {
  const canvas = els.map;
  const ctx = els.ctx;
  const width = canvas.width;
  const height = canvas.height;
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.fillStyle = '#101410';
  ctx.fillRect(0, 0, width, height);
  const pos = vehicle();
  if (!pos) {
    ctx.fillStyle = '#a8b5a6';
    ctx.font = `${16 * Math.min(window.devicePixelRatio || 1, 2)}px Segoe UI, sans-serif`;
    ctx.textAlign = 'center';
    ctx.fillText('Waiting for a satellite fix', width / 2, height / 2);
    return;
  }
  const heading = currentHeading();
  const headingDeg = heading == null ? 0 : heading;
  const ppm = applyWorldTransform(headingDeg, pos);
  recenterCoverage(pos);
  if (coverage.canvas) {
    ctx.save();
    ctx.imageSmoothingEnabled = false;
    ctx.drawImage(coverage.canvas, coverage.ox - BUFFER_CENTER, coverage.oy + BUFFER_CENTER, BUFFER, -BUFFER);
    ctx.restore();
  }
  drawGrid(ctx, pos, ppm);
  const guide = guidanceNow();
  const curve = activeCurve();
  if (curve) {
    drawContour(ctx, ppm, guide, curve);
    const pair = abPair();
    if (pair) drawFaintLine(ctx, ppm, pair.a, pair.b);
  } else drawSwaths(ctx, pos, ppm, guide);
  if (state.guide === 'ab' && state.nextPoints.length >= 2) drawPolyline(ctx, ppm, state.nextPoints, false);
  if (state.guide !== 'saved' && contourReady()) drawPolyline(ctx, ppm, state.contourPoints, false);
  if (state.rowPoints.length >= 2) drawPolyline(ctx, ppm, state.rowPoints, true);
  if (state.a) drawMarker(ctx, state.a, ppm, '#d6ff4a');
  if (state.b) drawMarker(ctx, state.b, ppm, '#f4f7f1');
  drawBoom(ctx, pos, headingDeg, ppm);

  const anchor = screenAnchor();
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.beginPath();
  const scale = width / Math.max(1, canvas.clientWidth || width);
  ctx.moveTo(anchor.cx, anchor.cy - 15 * scale);
  ctx.lineTo(anchor.cx + 11 * scale, anchor.cy + 12 * scale);
  ctx.lineTo(anchor.cx, anchor.cy + 5 * scale);
  ctx.lineTo(anchor.cx - 11 * scale, anchor.cy + 12 * scale);
  ctx.closePath();
  ctx.fillStyle = '#f4f7f1';
  ctx.fill();
  if (els.rose) els.rose.style.setProperty('--deg', `${-headingDeg}deg`);
}

function paintLightbar(guide) {
  let mode = 'none';
  let lights = 0;
  if (guide) {
    const magnitude = Math.abs(guide.steer);
    if (magnitude < state.deadbandM) mode = 'on';
    else {
      mode = guide.steer > 0 ? 'right' : 'left';
      lights = clamp(Math.round((magnitude - state.deadbandM) / 0.1524), 1, 8);
    }
  }
  const signature = `${mode}:${lights}`;
  if (signature === barSig) return;
  barSig = signature;
  const peg = lights >= 8;
  Array.from(els.lightbar.children).forEach((led, index) => {
    const dist = index - 8;
    led.className = `led${index === 8 ? ' center' : ''}`;
    if (mode === 'on' && Math.abs(dist) <= 1) led.classList.add('on-line');
    if (mode === 'right' && dist > 0 && dist <= lights) led.classList.add('on-right');
    if (mode === 'left' && dist < 0 && -dist <= lights) led.classList.add('on-left');
    if (peg && ((mode === 'right' && index === 16) || (mode === 'left' && index === 0))) led.classList.add('peg');
  });
}

function updateBand(steer) {
  if (steer == null) {
    state.steerBand = 'none';
    return;
  }
  const magnitude = Math.abs(steer);
  if (state.steerBand === 'on' || state.steerBand === 'none') {
    if (magnitude > state.deadbandM + 0.05) state.steerBand = steer > 0 ? 'right' : 'left';
    else state.steerBand = 'on';
  } else if (magnitude < state.deadbandM - 0.03) state.steerBand = 'on';
  else state.steerBand = steer > 0 ? 'right' : 'left';
}

function updateReadout(guide) {
  const steer = guide ? guide.steer : null;
  if (steer == null) state.steerView = 0;
  else state.steerView += (steer - state.steerView) * 0.22;
  updateBand(steer);
  const recordingContour = contourRecording() && state.applying;
  document.body.dataset.steer = guide ? state.steerBand : 'none';
  const waiting = state.mode === 'live' && !vehicle();
  const idle = !recordingContour && !guide;
  const gpsStale = state.mode === 'live' && (!state.fix || performance.now() - state.fix.localTs > 15000);
  els.steerDir.classList.toggle('prompt', (idle || recordingContour) && !waiting && !gpsStale);
  if (gpsStale || (waiting && !guide)) {
    setText(els.steerDir, 'WAITING FOR GPS');
  } else if (recordingContour) {
    setText(els.steerDir, 'Recording contour');
  } else if (idle) {
    setText(els.steerDir, 'set mark');
  } else if (steer == null) {
    setText(els.steerDir, 'NO HEADING');
  } else {
    setText(els.steerDir, state.steerBand === 'on' ? 'CENTERED' : state.steerBand === 'right' ? 'STEER RIGHT' : 'STEER LEFT');
  }

  if (state.mode === 'demo') {
    setText(els.speedRead, formatSpeed(demo.speed));
    setText(els.headRead, `${Math.round(demo.heading)}°`);
  } else {
    setText(els.speedRead, formatSpeed(state.fix && state.fix.speed));
    setText(els.headRead, state.heading == null ? '—' : `${Math.round(state.heading)}°`);
  }
  setText(els.sourceRead, state.headingSource);
  els.sourceRead.hidden = state.mode !== 'demo';
  paintGps();
  paintLightbar(guide);
  paintStatus(guide);
  paintToggles();
  paintWork();
  if (els.sheet.open) renderSensors();
}

function paintGps() {
  const pill = els.gpsPill;
  pill.className = 'pill';
  if (state.mode === 'demo') {
    pill.classList.add('ok');
    setText(pill, 'DEMO');
    return;
  }
  if (!state.fix || performance.now() - state.fix.localTs > 8000) {
    setText(pill, state.gpsError || 'GPS …');
    pill.classList.add('poor');
    return;
  }
  const feet = shownFeet(state.fix.acc);
  setText(pill, `± ${feet} ft`);
  pill.classList.add(feet <= 20 ? 'ok' : feet <= 40 ? 'fair' : 'poor');
}

function patternName() {
  if (state.guide === 'next' || state.guide === 'saved') return 'Guiding on contour';
  if (state.aHeading != null && !state.b) return 'Guiding on A+';
  return 'Guiding on A-B';
}

function paintStatus(guide) {
  if (contourRecording() && state.applying) {
    setText(els.statusLine, 'Recording contour');
    return;
  }
  if (contourRecording()) {
    setText(els.statusLine, 'set mark');
    return;
  }
  if (state.guide === 'ab' && state.a && !state.b && state.aHeading == null) {
    setText(els.statusLine, 'Drive straight to set the A+ heading');
    return;
  }
  if (!guide && state.guide === 'ab' && !abPair()) {
    setText(els.statusLine, state.mode === 'live' && !state.stable
      ? (state.gpsError || 'Waiting for a satellite fix')
      : 'Mark A at the start of a row');
    return;
  }
  let name = patternName();
  if (state.guide === 'ab' && state.a && !state.b && state.aHeading != null) {
    const pos = vehicle();
    if (pos) {
      const distance = Math.hypot(pos.x - state.a.x, pos.y - state.a.y);
      if (distance >= 8 && !lineReady(distance)) name = 'Guiding on A+ · line still loose';
      else if (lineReady(distance)) name = 'Guiding on A+ · line ready';
    }
  }
  const mode = state.passLock == null ? 'auto' : 'held';
  const pass = !guide ? '' : (guide.contour && guide.pass === 0 ? 'this row' : formatPass(guide.pass));
  setText(els.statusLine, `${name}${pass ? ` · ${pass} ${mode}` : ''}`);
}

function paintToggles() {
  els.applyBtn.classList.toggle('is-on', state.applying);
  els.applyBtn.setAttribute('aria-pressed', state.applying ? 'true' : 'false');
  setText(els.applyBtn, state.applying ? 'Applying' : 'Apply');
  const recording = contourRecording() && state.applying;
  const ready = curveReady();
  els.contourBtn.classList.toggle('is-on', recording);
  els.contourBtn.classList.toggle('is-set', ready && !recording);
  els.contourBtn.setAttribute('aria-pressed', recording || ready ? 'true' : 'false');
  setText(els.contourBtn, recording ? 'Recording' : ready ? 'Contour set' : 'Mark Contour');
  const aSet = Boolean(state.a);
  const bSet = Boolean(state.b);
  els.markA.classList.toggle('is-set', aSet);
  els.markB.classList.toggle('is-set', bSet);
  setText(els.markA, aSet && bSet ? 'A set' : aSet ? 'Reset A' : 'Mark A');
  setText(els.markB, bSet ? 'B set' : 'Mark B');
  paintPass();
}

function paintWidth() {
  if (document.activeElement !== els.widthInput) els.widthInput.value = String(boomFeet());
  setText(els.widthUnit, 'ft');
  setText(els.boomNum, String(boomFeet()));
}

function paintWork() {
  const count = Object.keys(state.passes).length;
  setText(els.passChip, `${count} ${count === 1 ? 'pass' : 'passes'}`);
  setText(els.acreChip, formatAcres(state.appliedM2));
  els.passChip.hidden = !state.tally;
  els.acreChip.hidden = !state.tally;
}

function paintMount() {
  document.querySelectorAll('[data-mount]').forEach((button) => {
    button.setAttribute('aria-pressed', Number(button.dataset.mount) === state.mount ? 'true' : 'false');
  });
}

function paintPass() {
  const locked = state.passLock != null;
  const label = locked ? (state.passLock === 0 ? 'AB' : `${state.passLock > 0 ? '+' : '−'}${Math.abs(state.passLock)}`) : 'Auto';
  setText(els.dockPassMode, label);
  if (els.dockPassAuto) els.dockPassAuto.setAttribute('aria-pressed', locked ? 'false' : 'true');
}

function shiftPass(direction) {
  const base = state.passLock == null ? currentPassNumber() : state.passLock;
  state.passLock = base + direction;
  paintPass();
}

function setPassAuto() {
  state.passLock = null;
  paintPass();
}

function syncSheet() {
  const feet = clamp(Math.round(state.deadbandM / FEET), 1, 20);
  els.deadband.value = String(feet);
  setText(els.deadbandRead, `${feet} ft`);
  els.volume.value = String(Math.round(state.volume * 100));
  setText(els.volumeRead, `${els.volume.value}%`);
  els.tallyToggle.checked = state.tally;
  paintMount();
  paintPass();
  renderSensors();
}

function powerLabel() {
  if (document.visibilityState !== 'visible') return 'Resting in the background';
  if (state.awake) return 'Awake while this app is open';
  return state.wakeNote || 'Waiting for a tap';
}

function renderSensors() {
  const gps = state.mode === 'demo'
    ? 'Not used in the preview'
    : state.gpsError
      || (state.sensorGps === 'searching' ? 'Searching' : '')
      || (state.fix ? `± ${formatDistance(state.fix.acc)}${state.fix.held ? ' · holding still' : ''}` : 'Waiting');
  const compass = state.mode === 'demo'
    ? 'Not used in the preview'
    : state.sensorCompass === 'live' ? 'Live' : state.sensorCompass;
  const motion = state.mode === 'demo'
    ? 'Not used in the preview'
    : state.sensorMotion === 'live' ? 'Live' : state.sensorMotion;
  const rows = [
    ['GPS', gps || 'Waiting'],
    ['Compass', compass],
    ['Motion', motion],
    ['Heading', state.headingSource],
    ['Screen', powerLabel()]
  ];
  els.sensorList.replaceChildren(...rows.map(([name, value]) => {
    const item = document.createElement('li');
    const label = document.createElement('span');
    const detail = document.createElement('b');
    label.textContent = name;
    detail.textContent = value;
    item.append(label, detail);
    return item;
  }));
  paintWake();
}

function paintStatic() {
  paintWidth();
  paintToggles();
  const guide = guidanceNow();
  updateReadout(guide);
}

function loop(timestamp) {
  if (!state.running || document.visibilityState !== 'visible') {
    rafId = 0;
    return;
  }
  if (!lastFrame) lastFrame = timestamp;
  const dt = Math.min(0.1, (timestamp - lastFrame) / 1000);
  lastFrame = timestamp;
  try {
    if (state.mode === 'demo') stepDemo(dt);
    else reviveGps();
    smoothHeading(dt);
    coastPosition(dt);
    rememberBias();
    sampleRow();
    watchTurn();
    lockAPlus();
    const gpsStale = state.mode === 'live' && (!state.fix || performance.now() - state.fix.localTs > 15000);
    const guide = gpsStale ? null : guidanceNow();
    serviceAudio(guide);
    maybePaint(vehicle());
    draw();
    updateReadout(guide);
  } catch (error) {
    console.error(error);
  }
  rafId = requestAnimationFrame(loop);
}

function startLoop() {
  if (rafId) cancelAnimationFrame(rafId);
  rafId = 0;
  lastFrame = 0;
  rafId = requestAnimationFrame(loop);
}

function stopLoop() {
  if (rafId) cancelAnimationFrame(rafId);
  rafId = 0;
  lastFrame = 0;
}

function bind() {
  const ids = [
    'splash', 'cab', 'startBtn', 'demoBtn', 'installBtn', 'installHint', 'offlineFlag',
    'gpsPill', 'compassBtn', 'steerDir', 'speedRead',
    'headRead', 'sourceRead', 'lightbar', 'markA', 'markB', 'applyBtn',
    'contourBtn', 'dockPassMinus', 'dockPassAuto', 'dockPassMode', 'dockPassPlus', 'widthMinus', 'widthPlus', 'widthInput', 'widthUnit',
    'boomChip', 'boomNum', 'passChip', 'acreChip', 'map', 'rose', 'zoomIn', 'zoomOut', 'sheet', 'closeSheet',
    'deadband', 'deadbandRead', 'volume', 'volumeRead',
    'tallyToggle', 'sensorList', 'wakeState', 'clearLine', 'clearContour', 'newField', 'backBtn', 'toast',
    'confirm', 'confirmText', 'confirmNo', 'confirmYes'
  ];
  ids.forEach((id) => { els[id] = $(id); });
  els.ctx = els.map.getContext('2d');
  for (let i = 0; i < 17; i += 1) {
    const led = document.createElement('span');
    led.className = `led${i === 8 ? ' center' : ''}`;
    els.lightbar.appendChild(led);
  }

  els.startBtn.addEventListener('click', async () => {
    holdWake(true);
    ensureAudio();
    const permission = requestSensorPermissions();
    await bootPromise;
    await permission;
    enterLive();
  });
  els.demoBtn.addEventListener('click', async () => {
    holdWake(true);
    ensureAudio();
    await bootPromise;
    enterDemo();
  });
  els.installBtn.addEventListener('click', async () => {
    if (!deferredInstall) return;
    deferredInstall.prompt();
    await deferredInstall.userChoice;
    deferredInstall = null;
    els.installBtn.hidden = true;
  });
  els.compassBtn.addEventListener('click', () => {
    syncSheet();
    els.sheet.showModal();
  });
  els.closeSheet.addEventListener('click', () => els.sheet.close());
  els.markA.addEventListener('click', markA);
  els.markB.addEventListener('click', markB);
  els.applyBtn.addEventListener('click', () => setApplying(!state.applying));
  els.contourBtn.addEventListener('click', toggleNext);
  els.widthMinus.addEventListener('click', () => stepWidth(-1));
  els.widthPlus.addEventListener('click', () => stepWidth(1));
  els.widthInput.addEventListener('change', () => {
    let value = Number(els.widthInput.value);
    if (!Number.isFinite(value)) return paintWidth();
    state.boomM = clamp(value, 4, 200) * FEET;
    rebuildCoverage();
    saveSettings();
    paintWidth();
  });
  els.dockPassMinus.addEventListener('click', () => shiftPass(-1));
  els.dockPassPlus.addEventListener('click', () => shiftPass(1));
  els.dockPassAuto.addEventListener('click', setPassAuto);
  els.zoomIn.addEventListener('click', () => {
    state.zoom = clamp(state.zoom * 1.2, ZOOM_MIN, ZOOM_MAX);
    saveSettings();
  });
  els.zoomOut.addEventListener('click', () => {
    state.zoom = clamp(state.zoom / 1.2, ZOOM_MIN, ZOOM_MAX);
    saveSettings();
  });
  document.querySelectorAll('[data-mount]').forEach((button) => {
    button.addEventListener('click', () => {
      state.mount = Number(button.dataset.mount);
      state.compassBias = 0;
      state.biasSaved = 0;
      state.biasDirty = false;
      saveSettings();
      paintMount();
      if (state.compassRaw != null) noteCompass(state.compassRaw, null, 'event');
    });
  });
  els.deadband.addEventListener('input', () => {
    state.deadbandM = clamp(Number(els.deadband.value), 1, 20) * FEET;
    setText(els.deadbandRead, `${els.deadband.value} ft`);
    saveSettings();
  });
  els.volume.addEventListener('input', () => {
    state.volume = clamp(Number(els.volume.value) / 100, 0, 1);
    state.audio = state.volume > 0;
    setText(els.volumeRead, `${Math.round(state.volume * 100)}%`);
    saveSettings();
  });
  els.tallyToggle.addEventListener('change', () => {
    state.tally = els.tallyToggle.checked;
    saveSettings();
    paintWork();
  });
  els.clearLine.addEventListener('click', () => askConfirm('Clear the A-B line?', 'Clear', clearLine));
  els.clearContour.addEventListener('click', () => askConfirm('Clear the contour line?', 'Clear', clearContour));
  els.newField.addEventListener('click', () => askConfirm('Start a new field? This clears the line, curves, and coverage.', 'New field', newField));
  els.confirmNo.addEventListener('click', () => {
    pendingConfirm = null;
    els.confirm.close();
  });
  els.confirmYes.addEventListener('click', () => {
    const action = pendingConfirm;
    pendingConfirm = null;
    els.confirm.close();
    if (action) action();
  });
  els.confirm.addEventListener('close', () => { pendingConfirm = null; });
  els.backBtn.addEventListener('click', () => {
    els.sheet.close();
    showSplash();
  });

  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'hidden') saveFieldNow();
    syncSession();
  });
  document.addEventListener('pointerdown', () => {
    if (document.visibilityState !== 'visible') return;
    holdWake(true);
    if (state.audio) ensureAudio();
  }, { passive: true });
  window.addEventListener('pagehide', () => {
    saveFieldNow();
    pauseField();
  });
  window.addEventListener('pageshow', () => syncSession());
  document.addEventListener('freeze', () => {
    saveFieldNow();
    pauseField();
  });
  document.addEventListener('resume', () => syncSession());
  new ResizeObserver(() => resizeCanvas()).observe(els.map.parentElement);
  window.addEventListener('beforeinstallprompt', (event) => {
    event.preventDefault();
    deferredInstall = event;
    els.installBtn.hidden = false;
  });
}

function paintInstallHint() {
  const standalone = window.matchMedia('(display-mode: standalone)').matches || window.navigator.standalone;
  if (!window.isSecureContext) {
    els.installHint.textContent = 'Open Field Nav over HTTPS to use GPS and the compass.';
    return;
  }
  if (standalone) {
    els.installHint.textContent = 'Installed on this device. Allow Location and Motion & Orientation when you start Guidance.';
    return;
  }
  els.installHint.textContent = 'On iPhone, open this page in Safari. Tap Share, then Add to Home Screen. When you start Guidance, allow Location and Motion & Orientation.';
}

const bootPromise = (async function boot() {
  bind();
  loadSettings();
  paintWidth();
  paintInstallHint();
  await loadField();
  if ('serviceWorker' in navigator) {
    navigator.serviceWorker.register('./sw.js').catch(() => {});
  }
  window.addEventListener('online', paintInstallHint);
  holdWake(true);
})();

window.fieldnav = {
  selfTest: runSelfTest,
  getState: () => ({
    awake: state.awake,
    mode: state.mode,
    steer: state.steerView,
    band: state.steerBand,
    beepCount: state.beepCount,
    heading: state.heading,
    applying: state.applying,
    segments: state.segments.length,
    audio: state.audio,
    wakeNote: state.wakeNote
  })
};

if (!runSelfTest()) console.warn('Field Nav guidance self-test failed');
