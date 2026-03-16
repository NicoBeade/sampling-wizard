/* ═══════════════════════════════════════════════════════
   Sampling Wizard — app.js
   DSP Engine · Plotting · UI · Modal Editor · Theme
   Uses: filters.js (must be loaded first)
   ═══════════════════════════════════════════════════════ */
'use strict';

/* ─── §1 Constants & State ─── */
const BASE_N = 16384; 
function getN() {
  if (state.waveform === 'bitstream') {
    // 1024 samples per symbol provides very high precision for filtering.
    const needed = state.sigNumSymbols * 1024;
    let n = BASE_N;
    while (n < needed && n < 524288) n <<= 1;
    return n;
  }
  return BASE_N;
}

const state = {
  waveform: 'sine', sigFreq: 1000, sigAmp: 1, sigDC: 0, sigPhase: 0, sigDuty: 50,
  sigSymbolRate: 1000, sigRolloff: 0.5, sigNumSymbols: 10, sigNumPeriods: 2,
  amEnabled: false, amFreq: 1000,
  samplingFreq: 8000,
  stages: {
    aaf: { enabled: true, type: 'butterworth', fp: 1000, Gp: -1, Ga: -40, sos: [], order: 0 },
    sh: { enabled: true, duty: 50 },
    sw: { enabled: true, duty: 50 },
    recon: { enabled: true, type: 'butterworth', fp: 1000, Gp: -1, Ga: -40, sos: [], order: 0 },
  },
  sameFilter: false,
  faFromSampling: false,
  zoom: { time: { scale: 1, offset: 0 }, freq: { scale: 1, offset: 0 } },
  spectrumViewType: 'line'
};

function getInternalRate() { 
  let signalBW = 0;
  if (state.waveform === 'bitstream') {
    signalBW = (state.sigSymbolRate / 2) * (1 + state.sigRolloff);
  } else {
    signalBW = state.sigFreq;
  }

  const maxContFreq = Math.max(signalBW, state.amEnabled ? state.amFreq + signalBW : 0);
  const minContFreq = state.amEnabled ? Math.min(signalBW, state.amFreq) : signalBW;
  
  const targetPeriods = state.waveform === 'bitstream' ? Math.max(5, state.sigNumSymbols) : state.sigNumPeriods;
  const baseRate = getN() * (minContFreq > 0.1 ? minContFreq : 1) / targetPeriods;
  // Increase rate to support the 8x spectrum view without aliasing in the sim
  return Math.max(baseRate, state.samplingFreq * 24, maxContFreq * 10); 
}
function getTWindow() { return getN() / getInternalRate(); }

/* ─── §1b Bitstream Utils ─── */
function rrcPulse(t, T, beta) {
  const t_T = t / T;
  const pix = Math.PI * t_T;
  if (t === 0) return (1 / Math.sqrt(T)) * (1 - beta + 4 * beta / Math.PI);
  if (Math.abs(Math.abs(t) - T / (4 * beta)) < 1e-10) {
    return (beta / Math.sqrt(2 * T)) * (
      (1 + 2 / Math.PI) * Math.sin(Math.PI / (4 * beta)) +
      (1 - 2 / Math.PI) * Math.cos(Math.PI / (4 * beta))
    );
  }
  const den = Math.PI * t_T * (1 - Math.pow(4 * beta * t_T, 2));
  const num = Math.sin(pix * (1 - beta)) + 4 * beta * t_T * Math.cos(pix * (1 + beta));
  return (1 / Math.sqrt(T)) * num / den;
}

let bitCache = { symbols: [], rate: 0, count: 0 };
function getSymbols(count) {
  if (bitCache.count >= count) return bitCache.symbols;
  const needed = count - bitCache.count;
  for (let i = 0; i < needed; i++) bitCache.symbols.push(Math.random() < 0.5 ? -1 : 1);
  bitCache.count = count;
  return bitCache.symbols;
}

function generateBitstream(n, rate, symbolRate, rolloff, amp) {
  const out = new Float64Array(n);
  const T = 1 / (symbolRate || 1);
  const duration = n / rate;
  const span = 6; // Symbols on each side
  const numSymbols = Math.ceil(duration / T) + span + 2; 
  const symbols = getSymbols(numSymbols);
  
  for (let i = 0; i < n; i++) {
    const t = i / rate;
    const centerSymbolIdx = Math.floor(t / T - 0.5); 
    let val = 0;
    for (let s = centerSymbolIdx - span; s <= centerSymbolIdx + span; s++) {
      if (s >= 0 && s < symbols.length) {
        // Center symbol s at (s + 0.5) * T
        val += symbols[s] * rrcPulse(t - (s + 0.5) * T, T, rolloff);
      }
    }
    out[i] = val * amp * Math.sqrt(T); // Normalized amp
  }
  return out;
}

let activeModalFilter = null; // 'aaf' or 'recon'
/* ─── §2 Signal Generator ─── */
function generateSignal(type, freq, amp, dc, phaseDeg, duty, n, rate, amEnabled, amFreq) {
  const out = new Float64Array(n);
  const phaseRad = phaseDeg * Math.PI / 180;
  for (let i = 0; i < n; i++) {
    const t = i / rate;
    const phi = 2 * Math.PI * freq * t + phaseRad;
    let v = 0;
    switch (type) {
      case 'sine': v = Math.sin(phi); break;
      case 'square': { const f = ((phi / (2 * Math.PI)) % 1 + 1) % 1; v = f < (duty / 100) ? 1 : -1; break; }
      case 'triangle': { const f = ((phi / (2 * Math.PI)) % 1 + 1) % 1; v = f < 0.5 ? (4 * f - 1) : (3 - 4 * f); break; }
      case 'sawtooth': { const f = ((phi / (2 * Math.PI)) % 1 + 1) % 1; v = 2 * f - 1; break; }
      case 'bitstream': return generateBitstream(n, rate, state.sigSymbolRate, state.sigRolloff, amp);
    }
    v = v * amp + dc;
    if (amEnabled) v *= Math.cos(2 * Math.PI * amFreq * t);
    out[i] = v;
  }
  return out;
}

/* ─── §3 Sampling Stages ─── */
function controlPulse(n, rate, samplingFreq, dutyPct, offsetPct) {
  const out = new Float64Array(n);
  const period = rate / samplingFreq;
  const onSamples = period * (dutyPct / 100);
  const offset = period * (offsetPct / 100);
  for (let i = 0; i < n; i++) {
    const pos = (((i - offset) % period) + period) % period;
    out[i] = pos < onSamples ? 1 : 0;
  }
  return out;
}

function sampleAndHold(signal, pulse) {
  const n = signal.length, out = new Float64Array(n);
  let held = 0, prevPulse = 0;
  for (let i = 0; i < n; i++) {
    if (pulse[i] === 1) { out[i] = signal[i]; held = signal[i]; }
    else { if (prevPulse === 1) held = signal[i > 0 ? i - 1 : 0]; out[i] = held; }
    prevPulse = pulse[i];
  }
  return out;
}

function analogSwitch(signal, pulse) {
  const n = signal.length, out = new Float64Array(n);
  for (let i = 0; i < n; i++) out[i] = signal[i] * pulse[i];
  return out;
}

/* ─── §4 FFT ─── */
function fft(real, imag) {
  const n = real.length;
  if (n <= 1) return;
  for (let i = 1, j = 0; i < n; i++) {
    let bit = n >> 1; while (j & bit) { j ^= bit; bit >>= 1; } j ^= bit;
    if (i < j) { [real[i], real[j]] = [real[j], real[i]];[imag[i], imag[j]] = [imag[j], imag[i]]; }
  }
  for (let len = 2; len <= n; len <<= 1) {
    const half = len >> 1, ang = -2 * Math.PI / len, wR = Math.cos(ang), wI = Math.sin(ang);
    for (let i = 0; i < n; i += len) {
      let cR = 1, cI = 0;
      for (let j = 0; j < half; j++) {
        const tR = cR * real[i + j + half] - cI * imag[i + j + half], tI = cR * imag[i + j + half] + cI * real[i + j + half];
        real[i + j + half] = real[i + j] - tR; imag[i + j + half] = imag[i + j] - tI;
        real[i + j] += tR; imag[i + j] += tI;
        const tmp = cR * wR - cI * wI; cI = cR * wI + cI * wR; cR = tmp;
      }
    }
  }
}

function magnitudeSpectrum(signal) {
  const n = signal.length, re = new Float64Array(n), im = new Float64Array(n);
  for (let i = 0; i < n; i++) re[i] = signal[i];
  fft(re, im);
  const halfN = (n >> 1) + 1, mag = new Float64Array(halfN);
  for (let i = 0; i < halfN; i++) mag[i] = 20 * Math.log10(Math.max(Math.sqrt(re[i] * re[i] + im[i] * im[i]) / n, 1e-12));
  return mag;
}

/* ─── §5 Filter Redesign ─── */
function redesignFilter(key) {
  const f = state.stages[key];
  if (!f.type) return;
  try {
    const result = designFilter(f.type, f.fp, f.Gp, f.Ga, getInternalRate());
    f.sos = result.sos; f.order = result.order;
  } catch (e) { console.warn('Filter design failed:', e); f.sos = []; f.order = 0; }
  updateSidebarSummary(key);
}

function updateSidebarSummary(key) {
  const f = state.stages[key];
  const el = document.getElementById(key + '-summary');
  if (!el) return;
  const typeNames = {
    butterworth: 'Butterworth', chebyshev1: 'Chebyshev I', chebyshev2: 'Chebyshev II',
    cauer: 'Cauer', bessel: 'Bessel', legendre: 'Legendre'
  };
  const name = typeNames[f.type] || f.type;
  el.textContent = `${name} · fp=${f.fp} Hz · fa=${f.fp * 2} Hz · N=${f.order || '—'}`;
}

function updateSignalSummary() {
  const { waveform, sigFreq, sigAmp, sigDC, amEnabled, amFreq } = state;
  const el = document.getElementById('sig-summary');
  if (!el) return;
  const name = waveform === 'bitstream' ? 'Bitstream' : waveform.charAt(0).toUpperCase() + waveform.slice(1);
  let txt = name;
  if (waveform === 'bitstream') {
    txt += ` · ${state.sigSymbolRate} Baud · &beta;=${state.sigRolloff}`;
  } else {
    txt += ` · ${sigFreq} Hz · ${sigAmp.toFixed(2)} V`;
  }
  if (sigDC !== 0) txt += ` · ${sigDC.toFixed(1)} Vdc`;
  if (amEnabled) txt += ` · AM (${amFreq} Hz)`;
  el.innerHTML = txt; // Use innerHTML for &beta;
}

/* ─── §6 DSP Pipeline ─── */
function processPipeline() {
  const { waveform, sigFreq, sigAmp, sigDC, sigPhase, sigDuty, amEnabled, amFreq, samplingFreq, stages } = state;
  const n = getN();
  const rate = getInternalRate();
  const original = generateSignal(waveform, sigFreq, sigAmp, sigDC, sigPhase, sigDuty, n, rate, amEnabled, amFreq);
  let sig = original;
  if (stages.aaf.enabled && stages.aaf.sos.length > 0) sig = applySOS(sig, stages.aaf.sos);
  const shPulse = controlPulse(n, rate, samplingFreq, stages.sh.duty, 0);
  const swPulse = controlPulse(n, rate, samplingFreq, stages.sw.duty, stages.sh.duty);
  if (stages.sh.enabled) sig = sampleAndHold(sig, shPulse);
  if (stages.sw.enabled) sig = analogSwitch(sig, swPulse);
  if (stages.recon.enabled && stages.recon.sos.length > 0) sig = applySOS(sig, stages.recon.sos);
  return { original, processed: sig, spectrum: magnitudeSpectrum(sig) };
}

/* ─── §7 Canvas Plotter ─── */
let cachedColors = null;
const canvasSizeCache = new WeakMap();
let canvasSizesDirty = true;

function refreshColors() {
  const s = getComputedStyle(document.documentElement);
  cachedColors = {
    grid: s.getPropertyValue('--grid-color').trim() || 'rgba(148,163,184,0.08)',
    axis: s.getPropertyValue('--axis-color').trim() || 'rgba(148,163,184,0.22)',
    label: s.getPropertyValue('--label-color').trim() || '#64748b',
    original: s.getPropertyValue('--plot-original').trim() || '#38bdf8',
    processed: s.getPropertyValue('--plot-processed').trim() || '#2dd4bf',
    spectrum: s.getPropertyValue('--plot-spectrum').trim() || '#a78bfa',
  };
}
function invalidateCanvasCache() { canvasSizesDirty = true; }

function getCanvasCtx(canvas) {
  const dpr = window.devicePixelRatio || 1;
  if (!canvasSizesDirty && canvasSizeCache.has(canvas)) {
    const c = canvasSizeCache.get(canvas);
    if (c.dpr === dpr) {
      c.ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      return c;
    }
  }
  // Reset canvas so it doesn't influence parent layout measurement
  canvas.style.width = '100%'; canvas.style.height = '100%';
  canvas.width = 0; canvas.height = 0;
  
  // Measure exactly what the CSS layout allocated
  const rect = canvas.getBoundingClientRect();
  const w = Math.max(rect.width, 40);
  const h = Math.max(rect.height, 40);
  
  canvas.width = w * dpr; canvas.height = h * dpr;
  const ctx = canvas.getContext('2d');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  const result = { ctx, w, h, dpr };
  canvasSizeCache.set(canvas, result);
  return result;
}

function drawGrid(ctx, pad, pw, ph, nX, nY) {
  ctx.strokeStyle = cachedColors.grid; ctx.lineWidth = 1;
  for (let i = 0; i <= nY; i++) { const y = pad.top + (i / nY) * ph; ctx.beginPath(); ctx.moveTo(pad.left, y); ctx.lineTo(pad.left + pw, y); ctx.stroke(); }
  for (let i = 0; i <= nX; i++) { const x = pad.left + (i / nX) * pw; ctx.beginPath(); ctx.moveTo(x, pad.top); ctx.lineTo(x, pad.top + ph); ctx.stroke(); }
}

function plotTime(canvas, data, color) {
  const { ctx, w, h } = getCanvasCtx(canvas);
  const pad = { left: 42, right: 8, top: 6, bottom: 20 }, pw = w - pad.left - pad.right, ph = h - pad.top - pad.bottom;
  ctx.clearRect(0, 0, w, h);
  let yMax = 0; for (let i = 0; i < data.length; i++) { const a = Math.abs(data[i]); if (a > yMax) yMax = a; }
  yMax = Math.max(yMax * 1.15, 0.1);
  drawGrid(ctx, pad, pw, ph, 8, 4);
  ctx.strokeStyle = cachedColors.axis; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(pad.left, pad.top + ph / 2); ctx.lineTo(pad.left + pw, pad.top + ph / 2); ctx.stroke();
  ctx.fillStyle = cachedColors.label; ctx.font = '10px "JetBrains Mono",monospace';
  
  // Y-axis labels and title
  ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
  for (let i = 0; i <= 4; i++) { const y = pad.top + (i / 4) * ph; ctx.fillText((yMax - 2 * yMax * i / 4).toFixed(1), pad.left - 4, y); }
  
  ctx.save();
  ctx.translate(10, pad.top + ph / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.font = '600 10px "Inter",sans-serif';
  ctx.fillText('Amplitude', 0, 0);
  ctx.restore();

  // X-axis labels and title
  ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  ctx.font = '10px "JetBrains Mono",monospace';
  const z = state.zoom.time;
  const tTotal = getTWindow() * 1000; // ms
  // Dynamic precision: more decimals for small time windows
  let tPrec = 1;
  if (tTotal / z.scale < 0.1) tPrec = 4;
  else if (tTotal / z.scale < 1) tPrec = 3;
  else if (tTotal / z.scale < 10) tPrec = 2;

  for (let i = 0; i <= 8; i += 2) { 
    const x = pad.left + (i / 8) * pw; 
    const tFraction = z.offset + (i / 8) / z.scale;
    ctx.fillText((tTotal * tFraction).toFixed(tPrec), x, pad.top + ph + 4); 
  }
  
  ctx.font = '600 10px "Inter",sans-serif';
  ctx.fillText('Time (ms)', pad.left + pw / 2, h - 8);

  ctx.beginPath(); ctx.strokeStyle = color; ctx.lineWidth = 1.4;
  for (let px = 0; px < pw; px++) {
    const fraction = z.offset + (px / pw) / z.scale;
    const idx = Math.min(data.length - 1, Math.floor(fraction * data.length));
    const x = pad.left + px, y = pad.top + ph / 2 - (data[idx] / yMax) * (ph / 2);
    px === 0 ? ctx.moveTo(x, y) : ctx.lineTo(x, y);
  }
  ctx.stroke();
}

function plotSpectrum(canvas, magDb, nyquist, displayLimit) {
  const { ctx, w, h } = getCanvasCtx(canvas);
  const pad = { left: 42, right: 8, top: 6, bottom: 20 }, pw = w - pad.left - pad.right, ph = h - pad.top - pad.bottom;
  ctx.clearRect(0, 0, w, h);
  const dbMax = 0, dbMin = -80, dbRange = dbMax - dbMin;
  drawGrid(ctx, pad, pw, ph, 8, 4);
  ctx.fillStyle = cachedColors.label; ctx.font = '10px "JetBrains Mono",monospace';
  
  // Y-axis labels and title
  ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
  for (let i = 0; i <= 4; i++) { const y = pad.top + (i / 4) * ph; ctx.fillText((dbMax - dbRange * i / 4).toFixed(0), pad.left - 4, y); }
  
  ctx.save();
  ctx.translate(10, pad.top + ph / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.font = '600 10px "Inter",sans-serif';
  ctx.fillText('Magnitude (dB)', 0, 0);
  ctx.restore();

  // X-axis labels and title
  ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  ctx.font = '10px "JetBrains Mono",monospace';
  const z = state.zoom.freq;
  const fPrec = z.scale > 10 ? 1 : 0;
  for (let i = 0; i <= 8; i += 2) { 
    const x = pad.left + (i / 8) * pw; 
    const fFraction = z.offset + (i / 8) / z.scale;
    ctx.fillText((displayLimit * fFraction).toFixed(fPrec), x, pad.top + ph + 4); 
  }
  
  ctx.font = '600 10px "Inter",sans-serif';
  ctx.fillText('Frequency (Hz)', pad.left + pw / 2, h - 8);

  // Vertical orange opaque semi-transparent lines at multiples of sampling frequency
  const fs = state.samplingFreq;
  ctx.save();
  ctx.strokeStyle = 'rgba(255, 140, 0, 0.35)'; // Orange opaque semi-transparent
  ctx.setLineDash([4, 2]);
  for (let k = 1; k * fs <= displayLimit; k++) {
    const fLoc = k * fs;
    const fraction = (fLoc / displayLimit - z.offset) * z.scale;
    if (fraction >= 0 && fraction <= 1) {
      const x = pad.left + fraction * pw;
      ctx.beginPath(); ctx.moveTo(x, pad.top); ctx.lineTo(x, pad.top + ph); ctx.stroke();
    }
  }
  ctx.restore();

  const nBins = magDb.length;
  ctx.strokeStyle = cachedColors.spectrum; ctx.lineWidth = 1.4;

  if (state.spectrumViewType === 'stems') {
    // Determine a reasonable step to not crowd stems. 
    // We want at most ~200 stems on screen.
    const skip = Math.max(1, Math.floor(pw / 100)); // Fixed: This was calculating skips based on n, should be based on px
    // Actually, let's step by pixels.
    const stepPx = Math.max(4, Math.floor(pw / 120)); 
    for (let px = 0; px < pw; px += stepPx) {
      const fraction = z.offset + (px / pw) / z.scale;
      const freq = fraction * displayLimit;
      const bin = Math.min(nBins - 1, Math.floor((freq / nyquist) * nBins));
      const db = Math.max(magDb[bin], dbMin);
      const x = pad.left + px, y = pad.top + (1 - (db - dbMin) / dbRange) * ph;
      const y0 = pad.top + ph;
      
      ctx.beginPath();
      ctx.moveTo(x, y0);
      ctx.lineTo(x, y);
      ctx.stroke();
      
      ctx.beginPath();
      ctx.arc(x, y, 2, 0, 2 * Math.PI);
      ctx.fillStyle = cachedColors.spectrum;
      ctx.fill();
    }
  } else {
    ctx.beginPath();
    for (let px = 0; px < pw; px++) {
      const fraction = z.offset + (px / pw) / z.scale;
      const freq = fraction * displayLimit;
      const bin = Math.min(nBins - 1, Math.floor((freq / nyquist) * nBins));
      const db = Math.max(magDb[bin], dbMin);
      const x = pad.left + px, y = pad.top + (1 - (db - dbMin) / dbRange) * ph;
      px === 0 ? ctx.moveTo(x, y) : ctx.lineTo(x, y);
    }
    ctx.stroke();
  }
}

/* ─── §8 Render ─── */
const canvasOriginal = document.getElementById('plot-original');
const canvasSampled = document.getElementById('plot-sampled');
const canvasSpectrum = document.getElementById('plot-spectrum');

/* ─── §7b Zoom Handlers ─── */
function attachZoomHandlers(canvas, zoomKey) {
  let isDragging = false;
  let lastX = 0;

  const pad = { left: 42, right: 8, top: 6, bottom: 20 };

  canvas.addEventListener('wheel', e => {
    e.preventDefault();
    const z = state.zoom[zoomKey];
    const rect = canvas.getBoundingClientRect();
    const pw = rect.width - pad.left - pad.right;
    const px = e.clientX - rect.left - pad.left;

    if (px < 0 || px > pw) return;

    const pxFraction = px / pw;
    const zoomFactor = e.deltaY > 0 ? 1.15 : 0.85;
    
    let newScale = Math.max(1, z.scale / zoomFactor);
    let newOffset = z.offset + pxFraction * (1 / z.scale) - pxFraction * (1 / newScale);
    
    newOffset = Math.max(0, Math.min(1 - 1 / newScale, newOffset));
    if (newOffset < 1e-5) newOffset = 0; 
    
    z.scale = newScale;
    z.offset = newOffset;
    
    scheduleRender();
  }, { passive: false });

  canvas.addEventListener('mousedown', e => {
    e.preventDefault();
    isDragging = true;
    lastX = e.clientX;
    canvas.style.cursor = 'grabbing';
  });

  window.addEventListener('mousemove', e => {
    if (!isDragging) return;
    const z = state.zoom[zoomKey];
    const rect = canvas.getBoundingClientRect();
    const pw = rect.width - pad.left - pad.right;

    const deltaPx = e.clientX - lastX;
    lastX = e.clientX;

    const deltaFraction = deltaPx / pw;
    let newOffset = z.offset - deltaFraction * (1 / z.scale);
    
    newOffset = Math.max(0, Math.min(1 - 1 / z.scale, newOffset));
    if (newOffset < 1e-5) newOffset = 0;
    
    z.offset = newOffset;
    scheduleRender();
  });

  window.addEventListener('mouseup', () => {
    if (isDragging) {
      isDragging = false;
      canvas.style.cursor = 'default';
    }
  });

  canvas.style.cursor = 'default';
}

function attachInputScrollHandlers() {
  document.querySelectorAll('.input-text').forEach(el => {
    el.addEventListener('wheel', e => {
      e.preventDefault();
      const step = parseFloat(el.getAttribute('step')) || 1;
      const min = parseFloat(el.getAttribute('min'));
      const max = parseFloat(el.getAttribute('max'));
      let val = parseFloat(el.value) || 0;
      
      if (e.deltaY < 0) val += step;
      else val -= step;
      
      if (!isNaN(min)) val = Math.max(min, val);
      if (!isNaN(max)) val = Math.min(max, val);
      
      // Fixed precision based on step
      const precision = step < 1 ? step.toString().split('.')[1].length : 0;
      el.value = val.toFixed(precision);
      
      // Trigger update
      el.dispatchEvent(new Event('input'));
      el.dispatchEvent(new Event('change'));
    }, { passive: false });
  });
}

function render() {
  if (!cachedColors) refreshColors();
  const { original, processed, spectrum } = processPipeline();
  const nyquist = getInternalRate() / 2;
  
  let effectiveSigFreq = state.sigFreq;
  if (state.waveform === 'bitstream') {
    effectiveSigFreq = state.sigSymbolRate;
  }

  const maxKeyFreq = Math.max(effectiveSigFreq, state.samplingFreq, state.amEnabled ? state.amFreq : 0);
  const displayLimit = Math.min(nyquist, 8 * maxKeyFreq);
  
  plotTime(canvasOriginal, original, cachedColors.original);
  plotTime(canvasSampled, processed, cachedColors.processed);
  plotSpectrum(canvasSpectrum, spectrum, nyquist, displayLimit);
  canvasSizesDirty = false;
}

let rafId = null;
function scheduleRender() { if (rafId) return; rafId = requestAnimationFrame(() => { render(); rafId = null; }); }

/* ─── §9 Presets ─── */
function applyPreset(preset) {
  switch (preset) {
    case 'instantaneous': state.stages.sh.enabled = true; state.stages.sh.duty = 5; state.stages.sw.enabled = true; state.stages.sw.duty = 5; break;
    case 'natural': state.stages.sh.enabled = false; state.stages.sw.enabled = true; state.stages.sw.duty = 50; break;
    case 'flat-top': state.stages.sh.enabled = true; state.stages.sh.duty = 50; state.stages.sw.enabled = false; break;
    case 'custom': break;
  }
  syncUIFromState();
}

/* ─── §10 Theme Toggle ─── */
function initTheme() {
  const saved = localStorage.getItem('sw-theme') || 'dark';
  applyTheme(saved);
  document.getElementById('theme-toggle').addEventListener('click', () => {
    const cur = document.documentElement.getAttribute('data-theme');
    const next = cur === 'light' ? 'dark' : 'light';
    applyTheme(next); localStorage.setItem('sw-theme', next);
    refreshColors(); scheduleRender();
  });
}
function applyTheme(theme) {
  if (theme === 'light') {
    document.documentElement.setAttribute('data-theme', 'light');
    document.getElementById('theme-icon').textContent = '';
    document.getElementById('theme-label').textContent = 'Dark Mode';
  } else {
    document.documentElement.removeAttribute('data-theme');
    document.getElementById('theme-icon').textContent = '';
    document.getElementById('theme-label').textContent = 'Light Mode';
  }
}

/* ─── §11 Filter Modal Editor ─── */
function openFilterModal(filterKey) {
  activeModalFilter = filterKey;
  const f = state.stages[filterKey];
  if (f.sos.length === 0) redesignFilter(filterKey);
  const title = filterKey === 'aaf' ? 'Anti-Alias Filter' : 'Reconstruction Filter';
  document.getElementById('modal-title').textContent = title;

  // Populate controls from state
  document.getElementById('modal-type').value = f.type;
  document.getElementById('modal-fp').value = f.fp;
  document.getElementById('modal-gp').value = f.Gp;
  document.getElementById('modal-ga').value = f.Ga;
  document.getElementById('modal-fa-val').textContent = f.fp * 2;
  document.getElementById('modal-order-val').textContent = f.order || '—';

  // Disable fp if fa=fs
  document.getElementById('modal-fp').disabled = state.faFromSampling;

  document.getElementById('filter-modal').style.display = '';
  document.body.classList.add('modal-open');

  // Draw all 3 plots after a short delay for layout
  requestAnimationFrame(() => drawModalPlots(f));
}

function closeFilterModal() {
  document.getElementById('filter-modal').style.display = 'none';
  document.body.classList.remove('modal-open');
  if (activeModalFilter) {
    updateSidebarSummary(activeModalFilter);
    if (state.sameFilter) updateSidebarSummary(activeModalFilter === 'aaf' ? 'recon' : 'aaf');
    scheduleRender();
  }
  activeModalFilter = null;
}

/* ─── §11b Signal Modal Editor ─── */
function openSignalModal() {
  // Populate from current state
  document.getElementById('msig-waveform').value = state.waveform;
  document.getElementById('msig-amp').value = state.sigAmp;
  document.getElementById('msig-dc').value = state.sigDC;
  document.getElementById('msig-phase').value = state.sigPhase;
  document.getElementById('msig-duty').value = state.sigDuty;
  
  document.getElementById('msig-am-enabled').checked = state.amEnabled;
  document.getElementById('msig-am-freq').value = state.amFreq;

  const isBitstream = state.waveform === 'bitstream';
  const isSquare = state.waveform === 'square';

  document.getElementById('msig-amp-row').style.display = isBitstream ? 'none' : '';
  document.getElementById('msig-dc-row').style.display = isBitstream ? 'none' : '';
  document.getElementById('msig-phase-row').style.display = isBitstream ? 'none' : '';
  document.getElementById('msig-am-freq-row').style.display = (!isBitstream && state.amEnabled) ? '' : 'none';
  // AM toggle itself should also be hidden for Bitstream based on "only leave..."
  document.getElementById('msig-am-enabled').closest('.control-row').style.display = isBitstream ? 'none' : '';

  document.getElementById('msig-duty-row').style.display = isSquare ? '' : 'none';
  
  document.getElementById('msig-symbol-rate-row').style.display = isBitstream ? '' : 'none';
  document.getElementById('msig-rolloff-row').style.display = isBitstream ? '' : 'none';
  document.getElementById('msig-symbol-count-row').style.display = isBitstream ? '' : 'none';
  document.getElementById('msig-periods-row').style.display = isBitstream ? 'none' : '';

  document.getElementById('msig-symbol-rate').value = state.sigSymbolRate;
  document.getElementById('msig-rolloff').value = state.sigRolloff;
  document.getElementById('msig-symbol-count').value = state.sigNumSymbols;
  document.getElementById('msig-periods').value = state.sigNumPeriods;
  
  document.getElementById('sig-modal').style.display = '';
  document.body.classList.add('modal-open');
  
  renderSignalPreview();
}

function closeSignalModal() {
  document.getElementById('sig-modal').style.display = 'none';
  document.body.classList.remove('modal-open');
  scheduleRender();
}

function renderSignalPreview() {
  const canvas = document.getElementById('modal-sig-preview');
  if (!canvas) return;
  
  const type = document.getElementById('msig-waveform').value;
  const amp = parseFloat(document.getElementById('msig-amp').value) || 0;
  const dc = parseFloat(document.getElementById('msig-dc').value) || 0;
  const phase = parseFloat(document.getElementById('msig-phase').value) || 0;
  const duty = parseFloat(document.getElementById('msig-duty').value) || 50;
  const freq = state.sigFreq; // Use current signal freq for labels

  const amEnabled = document.getElementById('msig-am-enabled').checked;
  const amFreq = parseFloat(document.getElementById('msig-am-freq').value) || 0;
  const numPeriods = parseInt(document.getElementById('msig-periods').value) || 2;

  // Plot requested periods of the lowest frequency
  let lowestFreq = amEnabled ? Math.min(freq, amFreq) : freq;
  if (type === 'bitstream') {
    const symbolRate = parseFloat(document.getElementById('msig-symbol-rate').value) || 1000;
    const sigBW = symbolRate / 2;
    lowestFreq = amEnabled ? Math.min(sigBW, amFreq) : sigBW;
  }
  const T = 1 / (lowestFreq || 1); 
  const totalTime = (type === 'bitstream' ? 2 : numPeriods) * T;
  const previewRate = 1000 / totalTime; // 1000 points total
  const n = 1000;
  
  const data = generateSignal(type, freq, amp, dc, phase, duty, n, previewRate, amEnabled, amFreq);
  
  const ctxResult = getCanvasCtx(canvas);
  const ctx = ctxResult.ctx;
  const w = ctxResult.w;
  const h = ctxResult.h;
  if (!cachedColors) refreshColors();
  
  const pad = { left: 42, right: 10, top: 10, bottom: 25 };
  const pw = w - pad.left - pad.right;
  const ph = h - pad.top - pad.bottom;
  ctx.clearRect(0, 0, w, h);
  
  let yMax = Math.max(Math.abs(amp) + Math.abs(dc), 0.1) * 1.3;
  drawGrid(ctx, pad, pw, ph, 4, 4);
  
  ctx.strokeStyle = cachedColors.axis; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(pad.left, pad.top + ph / 2); ctx.lineTo(pad.left + pw, pad.top + ph / 2); ctx.stroke();
  
  // Y-axis labels
  ctx.fillStyle = cachedColors.label; ctx.font = '10px "JetBrains Mono",monospace';
  ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
  ctx.fillText(yMax.toFixed(1), pad.left - 4, pad.top);
  ctx.fillText((-yMax).toFixed(1), pad.left - 4, pad.top + ph);

  // X-axis labels (0 to 2T in ms)
  ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  ctx.fillText('0', pad.left, pad.top + ph + 4);
  ctx.fillText((totalTime * 1000).toFixed(1) + 'ms', pad.left + pw, pad.top + ph + 4);

  // Axis Titles
  ctx.font = '600 9px "Inter",sans-serif';
  const xTitle = type === 'bitstream' ? `${state.sigNumSymbols} symbols` : `${numPeriods} periods`;
  ctx.fillText('Time (' + xTitle + ')', pad.left + pw / 2, h - 8);
  
  ctx.save();
  ctx.translate(10, pad.top + ph / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.fillText('Amp', 0, 0);
  ctx.restore();

  ctx.beginPath(); ctx.strokeStyle = cachedColors.original; ctx.lineWidth = 2;
  for(let i=0; i<pw; i++) {
    const idx = Math.min(n - 1, Math.floor(i/pw * n));
    const x = pad.left + i, y = pad.top + ph/2 - (data[idx]/yMax)*(ph/2);
    i===0 ? ctx.moveTo(x,y) : ctx.lineTo(x,y);
  }
  ctx.stroke();
}

function updateStateFromSignalModal() {
  state.waveform = document.getElementById('msig-waveform').value;
  state.sigAmp = parseFloat(document.getElementById('msig-amp').value) || 0.1;
  state.sigDC = parseFloat(document.getElementById('msig-dc').value) || 0;
  state.sigPhase = parseFloat(document.getElementById('msig-phase').value) || 0;
  state.sigDuty = parseFloat(document.getElementById('msig-duty').value) || 50;
  state.sigSymbolRate = parseFloat(document.getElementById('msig-symbol-rate').value) || 1000;
  state.sigRolloff = parseFloat(document.getElementById('msig-rolloff').value) || 0.5;
  
  state.amEnabled = document.getElementById('msig-am-enabled').checked;
  state.amFreq = parseFloat(document.getElementById('msig-am-freq').value) || 1000;
  state.sigNumSymbols = Math.max(1, parseInt(document.getElementById('msig-symbol-count').value) || 10);
  state.sigNumPeriods = Math.max(1, parseInt(document.getElementById('msig-periods').value) || 2);

  const isBitstream = state.waveform === 'bitstream';
  const isSquare = state.waveform === 'square';

  document.getElementById('msig-amp-row').style.display = isBitstream ? 'none' : '';
  document.getElementById('msig-dc-row').style.display = isBitstream ? 'none' : '';
  document.getElementById('msig-phase-row').style.display = isBitstream ? 'none' : '';
  document.getElementById('msig-am-freq-row').style.display = (!isBitstream && state.amEnabled) ? '' : 'none';
  document.getElementById('msig-am-enabled').closest('.control-row').style.display = isBitstream ? 'none' : '';
  document.getElementById('msig-duty-row').style.display = isSquare ? '' : 'none';
  document.getElementById('msig-symbol-rate-row').style.display = isBitstream ? '' : 'none';
  document.getElementById('msig-rolloff-row').style.display = isBitstream ? '' : 'none';
  document.getElementById('msig-symbol-count-row').style.display = isBitstream ? '' : 'none';
  document.getElementById('msig-periods-row').style.display = isBitstream ? 'none' : '';

  redesignFilter('aaf');
  redesignFilter('recon');
  autoZoomTime();
  updateSignalSummary();
  renderSignalPreview();
  scheduleRender();
}

function autoZoomTime() {
  // Auto-adjust zoom to show the targeted duration.
  // Scale = Window / Target
  const lowestFreq = state.amEnabled ? Math.min(state.sigFreq, state.amFreq) : state.sigFreq;
  let targetDur = lowestFreq > 0.1 ? state.sigNumPeriods / lowestFreq : state.sigNumPeriods;

  if (state.waveform === 'bitstream') {
    targetDur = state.sigNumSymbols / state.sigSymbolRate;
  }
  
  // We Math.max(1, ...) to avoid zooming "out" beyond the window we have
  // (which would show the end of the buffer as a flat line)
  state.zoom.time.scale = Math.max(1, getTWindow() / targetDur);
  state.zoom.time.offset = 0;
}

function onModalParamChange() {
  if (!activeModalFilter) return;
  const f = state.stages[activeModalFilter];
  f.type = document.getElementById('modal-type').value;
  if (!state.faFromSampling) f.fp = parseFloat(document.getElementById('modal-fp').value) || 5;
  f.Gp = parseFloat(document.getElementById('modal-gp').value) || -1;
  f.Ga = parseFloat(document.getElementById('modal-ga').value) || -40;

  document.getElementById('modal-fa-val').textContent = (f.fp * 2).toFixed(0);

  // Sync if same filter
  if (state.sameFilter) {
    const other = activeModalFilter === 'aaf' ? 'recon' : 'aaf';
    Object.assign(state.stages[other], { type: f.type, fp: f.fp, Gp: f.Gp, Ga: f.Ga });
    redesignFilter(other);
  }

  redesignFilter(activeModalFilter);
  document.getElementById('modal-order-val').textContent = f.order || '—';
  drawModalPlots(f);
}

function drawModalPlots(f) {
  if (!cachedColors) refreshColors();
  if (f.sos.length === 0) return;

  const maxFreq = f.fp * 2 * 1.1; // 1.1 × fa
  const nPts = 512;
  const resp = freqResponseFull(f.sos, nPts, getInternalRate(), maxFreq);

  const canvases = [
    { el: document.getElementById('modal-mag'), data: resp.mags, unit: 'dB', color: cachedColors.spectrum },
    { el: document.getElementById('modal-phase'), data: resp.phases, unit: '°', color: cachedColors.original },
    { el: document.getElementById('modal-gd'), data: resp.groupDelays, unit: 'ms', color: cachedColors.processed },
  ];

  for (const { el, data, unit, color } of canvases) {
    drawModalSinglePlot(el, data, maxFreq, nPts, unit, color, f);
  }
}

function drawModalSinglePlot(canvas, data, maxFreq, nPts, unit, color, f) {
  const dpr = window.devicePixelRatio || 1;
  const parent = canvas.parentElement;

  // Temporarily reset canvas sizes so they don't block flex container from shrinking
  canvas.style.width = '0px'; canvas.style.height = '0px';
  canvas.width = 0; canvas.height = 0;

  const w = parent.clientWidth;
  const label = parent.querySelector('.modal-plot-label');
  const usedH = label ? label.offsetHeight + 4 : 0;
  const h = Math.max(parent.clientHeight - usedH, 30);

  canvas.width = w * dpr; canvas.height = h * dpr;
  canvas.style.width = w + 'px'; canvas.style.height = h + 'px';
  const ctx = canvas.getContext('2d');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

  const pad = { left: 46, right: 25, top: 4, bottom: 30 };
  const pw = w - pad.left - pad.right, ph = h - pad.top - pad.bottom;
  ctx.clearRect(0, 0, w, h);

  // Auto range
  let yMin = Infinity, yMax = -Infinity;
  for (let i = 0; i < nPts; i++) {
    if (isFinite(data[i])) { if (data[i] < yMin) yMin = data[i]; if (data[i] > yMax) yMax = data[i]; }
  }
  if (unit === 'dB') { yMin = Math.max(yMin, -100); yMax = Math.min(yMax + 5, 10); }
  else { yMin = Math.min(yMin, 0); yMax = yMax * 1.1 || 1; }
  if (yMax - yMin < 1) { yMax += 0.5; yMin -= 0.5; }
  const yRange = yMax - yMin;

  // Grid
  drawGrid(ctx, pad, pw, ph, 8, 4);

  // Y labels
  ctx.fillStyle = cachedColors.label; ctx.font = '9px "JetBrains Mono",monospace';
  ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
  for (let i = 0; i <= 4; i++) {
    const y = pad.top + (i / 4) * ph;
    const val = yMax - (i / 4) * yRange;
    ctx.fillText(val.toFixed(unit === 'dB' ? 0 : 1), pad.left - 4, y);
  }

  // X labels
  ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  for (let i = 0; i <= 4; i++) {
    const x = pad.left + (i / 4) * pw;
    ctx.fillText((maxFreq * i / 4).toFixed(0), x, pad.top + ph + 2);
  }

  // Axis Titles
  const unitMap = { 'dB': 'Mag (dB)', '°': 'Phase (°)', 'ms': 'Delay (ms)' };
  ctx.font = '600 9px "Inter",sans-serif';
  ctx.textAlign = 'center';
  ctx.fillText('Frequency (Hz)', pad.left + pw / 2, h - 8);
  
  ctx.save();
  ctx.translate(10, pad.top + ph / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.fillText(unitMap[unit] || unit, 0, 0);
  ctx.restore();

  // Trace
  ctx.beginPath(); ctx.strokeStyle = color; ctx.lineWidth = 1.6;
  for (let px = 0; px < pw; px++) {
    const bin = Math.floor(px / pw * nPts);
    const val = Math.max(Math.min(data[bin], yMax), yMin);
    const x = pad.left + px, y = pad.top + (1 - (val - yMin) / yRange) * ph;
    px === 0 ? ctx.moveTo(x, y) : ctx.lineTo(x, y);
  }
  ctx.stroke();

  // fp and fa markers (vertical dashed lines)
  ctx.setLineDash([3, 2]);
  const fpX = pad.left + (f.fp / maxFreq) * pw;
  const faX = pad.left + (f.fp * 2 / maxFreq) * pw;
  ctx.strokeStyle = cachedColors.processed; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(fpX, pad.top); ctx.lineTo(fpX, pad.top + ph); ctx.stroke();
  ctx.strokeStyle = '#f87171';
  ctx.beginPath(); ctx.moveTo(faX, pad.top); ctx.lineTo(faX, pad.top + ph); ctx.stroke();
  ctx.setLineDash([]);
}

/* ─── §12 UI Controller ─── */
function setNested(path, value) {
  const keys = path.split('.'); let obj = state;
  for (let i = 0; i < keys.length - 1; i++)obj = obj[keys[i]];
  obj[keys[keys.length - 1]] = value;
}
function getNested(path) { return path.split('.').reduce((o, k) => o[k], state); }

function bindSlider(id, key, fmt) {
  const el = document.getElementById(id), ro = document.getElementById(id + '-val');
  if (!el) return;
  el.addEventListener('input', () => {
    const v = parseFloat(el.value); setNested(key, v);
    if (ro) ro.textContent = fmt ? fmt(v) : v;
    scheduleRender();
  });
}

function syncUIFromState() {
  const toggleMap = { 'stage-aaf': 'stages.aaf.enabled', 'stage-sh': 'stages.sh.enabled', 'stage-sw': 'stages.sw.enabled', 'stage-recon': 'stages.recon.enabled' };
  for (const [id, path] of Object.entries(toggleMap)) {
    const el = document.getElementById(id);
    if (el) { el.checked = getNested(path); updateStageVisual(el); }
  }
  const sliderMap = { 'sh-duty': 'stages.sh.duty', 'sw-duty': 'stages.sw.duty' };
  for (const [id, path] of Object.entries(sliderMap)) {
    const el = document.getElementById(id), ro = document.getElementById(id + '-val');
    if (el) { el.value = getNested(path); if (ro) ro.textContent = getNested(path); }
  }
  updateSidebarSummary('aaf');
  updateSidebarSummary('recon');
}

function updateStageVisual(chk) {
  const block = chk.closest('.stage-block');
  if (block) block.classList.toggle('disabled', !chk.checked);
}

function applyFaFromSampling() {
  if (!state.faFromSampling) return;
  const fp = state.samplingFreq / 2;
  state.stages.aaf.fp = fp;
  state.stages.recon.fp = fp;
  redesignFilter('aaf');
  redesignFilter('recon');
}

let redesignTimeout = null;

function initUI() {
  const sigFreqEl = document.getElementById('sig-freq');
  const sigFreqVal = document.getElementById('sig-freq-val');
  
  const updateSigFreq = (val) => {
    const v = parseFloat(val);
    if (isNaN(v)) return;
    setNested('sigFreq', v);
    sigFreqEl.value = v;
    sigFreqVal.value = v;
    
    autoZoomTime();
    
    clearTimeout(redesignTimeout);
    redesignTimeout = setTimeout(() => {
      redesignFilter('aaf');
      redesignFilter('recon');
      scheduleRender();
    }, 150);
    
    updateSignalSummary();
    scheduleRender();
  };

  sigFreqEl.addEventListener('input', () => updateSigFreq(sigFreqEl.value));
  sigFreqVal.addEventListener('input', () => updateSigFreq(sigFreqVal.value));

  // Signal edit button
  document.getElementById('sig-plot-btn').addEventListener('click', openSignalModal);
  document.getElementById('sig-modal-close').addEventListener('click', closeSignalModal);
  
  // Signal modal live preview updates
  ['msig-waveform', 'msig-amp', 'msig-dc', 'msig-phase', 'msig-duty', 'msig-am-enabled', 'msig-am-freq', 'msig-symbol-rate', 'msig-rolloff', 'msig-symbol-count', 'msig-periods'].forEach(id => {
    const el = document.getElementById(id);
    if (!el) return;
    el.addEventListener(el.type === 'checkbox' ? 'change' : 'input', () => {
      if(id === 'msig-waveform') {
        const isSquare = el.value === 'square';
        const isBitstream = el.value === 'bitstream';
        document.getElementById('msig-amp-row').style.display = isBitstream ? 'none' : '';
        document.getElementById('msig-dc-row').style.display = isBitstream ? 'none' : '';
        document.getElementById('msig-phase-row').style.display = isBitstream ? 'none' : '';
        document.getElementById('msig-am-enabled').closest('.control-row').style.display = isBitstream ? 'none' : '';
        document.getElementById('msig-duty-row').style.display = isSquare ? '' : 'none';
        document.getElementById('msig-symbol-rate-row').style.display = isBitstream ? '' : 'none';
        document.getElementById('msig-rolloff-row').style.display = isBitstream ? '' : 'none';
        document.getElementById('msig-symbol-count-row').style.display = isBitstream ? '' : 'none';
        document.getElementById('msig-periods-row').style.display = isBitstream ? 'none' : '';
      }
      if(id === 'msig-am-enabled') {
        document.getElementById('msig-am-freq-row').style.display = el.checked ? '' : 'none';
      }
      updateStateFromSignalModal();
    });
  });

  // Spectrum toggle stems
  const toggleBtn = document.getElementById('toggle-fft-view');
  if (toggleBtn) {
    toggleBtn.addEventListener('click', (e) => {
      e.preventDefault();
      e.stopPropagation();
      state.spectrumViewType = (state.spectrumViewType === 'stems' ? 'line' : 'stems');
      toggleBtn.textContent = (state.spectrumViewType === 'stems' ? 'Lines' : 'Stems');
      scheduleRender();
    });
  }

  const sampEl = document.getElementById('sampling-freq'), sampVal = document.getElementById('sampling-freq-val');
  
  const updateSamplingFreq = (val) => {
    let v = parseFloat(val);
    if (isNaN(v)) return;
    if (v < 100) v = 100; // Safety guard
    state.samplingFreq = v;
    sampEl.value = v;
    sampVal.value = v;
    
    autoZoomTime(); // Rate might change
    if (state.faFromSampling) applyFaFromSampling();
    scheduleRender();
  };

  sampEl.addEventListener('input', () => updateSamplingFreq(sampEl.value));
  sampVal.addEventListener('input', () => updateSamplingFreq(sampVal.value));



  // Stage toggles
  ['stage-aaf', 'stage-sh', 'stage-sw', 'stage-recon'].forEach(id => {
    const el = document.getElementById(id);
    const paths = { 'stage-aaf': 'stages.aaf.enabled', 'stage-sh': 'stages.sh.enabled', 'stage-sw': 'stages.sw.enabled', 'stage-recon': 'stages.recon.enabled' };
    el.addEventListener('change', () => {
      setNested(paths[id], el.checked); updateStageVisual(el);
      scheduleRender();
    });
    updateStageVisual(el);
  });

  bindSlider('sh-duty', 'stages.sh.duty', v => v);
  bindSlider('sw-duty', 'stages.sw.duty', v => v);

  // Filter edit buttons
  ['aaf', 'recon'].forEach(key => {
    document.getElementById(key + '-plot-btn').addEventListener('click', () => openFilterModal(key));
  });

  // Modal controls — live update on every change
  ['modal-type', 'modal-fp', 'modal-gp', 'modal-ga'].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.addEventListener(el.tagName === 'SELECT' ? 'change' : 'input', onModalParamChange);
  });

  // Modal close
  document.getElementById('modal-close').addEventListener('click', closeFilterModal);
  document.getElementById('filter-modal').addEventListener('click', e => {
    if (e.target === e.currentTarget) closeFilterModal();
  });
  document.getElementById('sig-modal').addEventListener('click', e => {
    if (e.target === e.currentTarget) closeSignalModal();
  });

  // Global toggle buttons
  const btnSame = document.getElementById('opt-same-filter');
  const reconBtn = document.getElementById('recon-plot-btn');
  btnSame.addEventListener('click', () => {
    state.sameFilter = !state.sameFilter;
    btnSame.classList.toggle('active', state.sameFilter);
    reconBtn.disabled = state.sameFilter;
    
    if (state.sameFilter) {
      const aaf = state.stages.aaf;
      Object.assign(state.stages.recon, { type: aaf.type, fp: aaf.fp, Gp: aaf.Gp, Ga: aaf.Ga });
      redesignFilter('recon');
      updateSidebarSummary('recon');
      scheduleRender();
    }
  });

  const btnFaFs = document.getElementById('opt-fa-fs');
  btnFaFs.addEventListener('click', () => {
    state.faFromSampling = !state.faFromSampling;
    btnFaFs.classList.toggle('active', state.faFromSampling);
    if (state.faFromSampling) { applyFaFromSampling(); scheduleRender(); }
  });

  // Resize & DPR change detection
  window.addEventListener('resize', () => {
    invalidateCanvasCache();
    scheduleRender();
    if (activeModalFilter) drawModalPlots(state.stages[activeModalFilter]);
  });

  let dprQuery = window.matchMedia(`(resolution: ${window.devicePixelRatio}dppx)`);
  const onDprChange = () => {
    invalidateCanvasCache();
    scheduleRender();
    if (activeModalFilter) drawModalPlots(state.stages[activeModalFilter]);
    dprQuery.removeEventListener('change', onDprChange);
    dprQuery = window.matchMedia(`(resolution: ${window.devicePixelRatio}dppx)`);
    dprQuery.addEventListener('change', onDprChange);
  };
  dprQuery.addEventListener('change', onDprChange);

  // Info Tooltip interactivity
  document.querySelectorAll('.info-tooltip').forEach(el => {
    el.addEventListener('click', (e) => {
      e.stopPropagation();
      el.classList.toggle('active');
    });
    el.addEventListener('mouseleave', () => el.classList.remove('active'));
  });

  // Init
  initTheme();
  attachZoomHandlers(canvasOriginal, 'time');
  attachZoomHandlers(canvasSampled, 'time');
  attachZoomHandlers(canvasSpectrum, 'freq');
  attachInputScrollHandlers();
  redesignFilter('aaf');
  redesignFilter('recon');
  updateSignalSummary();
  render();
}

document.addEventListener('DOMContentLoaded', initUI);
