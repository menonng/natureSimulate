'use strict';
/* ============================================================
   방귀 유체 시뮬레이터 (Navier-Stokes fart fluid simulator)
   Classic "Stable Fluids" (Jos Stam) grid solver, from scratch.
   Wrapped in an IIFE so its names never collide with script.js.
   ============================================================ */
(function () {
  const N = 100;                 // interior grid cells (N x N)
  const ITER = 10;                // Gauss-Seidel iterations for each solve
  const SIZE = (N + 2) * (N + 2);
  const DT = 0.14;
  const DIFFUSION = 0.00002;
  const VISCOSITY = 0.0000005;
  const BUOYANCY = 0.28;          // gas rises like real smoke
  const FADE = 0.996;              // density slowly dissipates

  let Vx = new Float32Array(SIZE), Vy = new Float32Array(SIZE);
  let Vx0 = new Float32Array(SIZE), Vy0 = new Float32Array(SIZE);
  let density = new Float32Array(SIZE), density0 = new Float32Array(SIZE);

  // Grid-space position the character sits at (matches #fluidChar's CSS: 50%/66%).
  const emitterX = N * 0.5, emitterY = N * 0.66;

  function IX(x, y) { return x + y * (N + 2); }

  function setBnd(b, x) {
    for (let i = 1; i <= N; i++) {
      x[IX(0, i)] = b === 1 ? -x[IX(1, i)] : x[IX(1, i)];
      x[IX(N + 1, i)] = b === 1 ? -x[IX(N, i)] : x[IX(N, i)];
      x[IX(i, 0)] = b === 2 ? -x[IX(i, 1)] : x[IX(i, 1)];
      x[IX(i, N + 1)] = b === 2 ? -x[IX(i, N)] : x[IX(i, N)];
    }
    x[IX(0, 0)] = 0.5 * (x[IX(1, 0)] + x[IX(0, 1)]);
    x[IX(0, N + 1)] = 0.5 * (x[IX(1, N + 1)] + x[IX(0, N)]);
    x[IX(N + 1, 0)] = 0.5 * (x[IX(N, 0)] + x[IX(N + 1, 1)]);
    x[IX(N + 1, N + 1)] = 0.5 * (x[IX(N, N + 1)] + x[IX(N + 1, N)]);
  }

  function linSolve(b, x, x0, a, c) {
    const cRecip = 1 / c;
    for (let k = 0; k < ITER; k++) {
      for (let j = 1; j <= N; j++) {
        for (let i = 1; i <= N; i++) {
          x[IX(i, j)] = (x0[IX(i, j)] + a * (x[IX(i - 1, j)] + x[IX(i + 1, j)] + x[IX(i, j - 1)] + x[IX(i, j + 1)])) * cRecip;
        }
      }
      setBnd(b, x);
    }
  }

  function diffuse(b, x, x0, diff) {
    const a = DT * diff * N * N;
    if (a === 0) { x.set(x0); return; }
    linSolve(b, x, x0, a, 1 + 4 * a);
  }

  function project(vx, vy, p, div) {
    for (let j = 1; j <= N; j++) {
      for (let i = 1; i <= N; i++) {
        div[IX(i, j)] = -0.5 * (vx[IX(i + 1, j)] - vx[IX(i - 1, j)] + vy[IX(i, j + 1)] - vy[IX(i, j - 1)]) / N;
        p[IX(i, j)] = 0;
      }
    }
    setBnd(0, div); setBnd(0, p);
    linSolve(0, p, div, 1, 4);
    for (let j = 1; j <= N; j++) {
      for (let i = 1; i <= N; i++) {
        vx[IX(i, j)] -= 0.5 * (p[IX(i + 1, j)] - p[IX(i - 1, j)]) * N;
        vy[IX(i, j)] -= 0.5 * (p[IX(i, j + 1)] - p[IX(i, j - 1)]) * N;
      }
    }
    setBnd(1, vx); setBnd(2, vy);
  }

  function advect(b, d, d0, vx, vy) {
    let i0, i1, j0, j1;
    const dt0 = DT * N;
    for (let j = 1; j <= N; j++) {
      for (let i = 1; i <= N; i++) {
        let x = i - dt0 * vx[IX(i, j)];
        let y = j - dt0 * vy[IX(i, j)];
        if (x < 0.5) x = 0.5; if (x > N + 0.5) x = N + 0.5;
        i0 = Math.floor(x); i1 = i0 + 1;
        if (y < 0.5) y = 0.5; if (y > N + 0.5) y = N + 0.5;
        j0 = Math.floor(y); j1 = j0 + 1;
        const s1 = x - i0, s0 = 1 - s1;
        const t1 = y - j0, t0 = 1 - t1;
        d[IX(i, j)] = s0 * (t0 * d0[IX(i0, j0)] + t1 * d0[IX(i0, j1)]) + s1 * (t0 * d0[IX(i1, j0)] + t1 * d0[IX(i1, j1)]);
      }
    }
    setBnd(b, d);
  }

  function step() {
    diffuse(1, Vx0, Vx, VISCOSITY);
    diffuse(2, Vy0, Vy, VISCOSITY);
    project(Vx0, Vy0, Vx, Vy);
    advect(1, Vx, Vx0, Vx0, Vy0);
    advect(2, Vy, Vy0, Vx0, Vy0);
    project(Vx, Vy, Vx0, Vy0);

    diffuse(0, density0, density, DIFFUSION);
    advect(0, density, density0, Vx, Vy);

    for (let j = 1; j <= N; j++) {
      for (let i = 1; i <= N; i++) {
        const idx = IX(i, j);
        Vy[idx] -= BUOYANCY * density[idx] * DT; // rises like smoke (canvas +y is down)
        density[idx] *= FADE;
      }
    }
  }

  function addDensity(x, y, amount) {
    const i = clampInt(Math.round(x), 1, N), j = clampInt(Math.round(y), 1, N);
    density[IX(i, j)] += amount;
  }
  function addVelocity(x, y, ax, ay) {
    const i = clampInt(Math.round(x), 1, N), j = clampInt(Math.round(y), 1, N);
    const idx = IX(i, j);
    Vx[idx] += ax; Vy[idx] += ay;
  }
  function clampInt(v, a, b) { return v < a ? a : v > b ? b : v; }

  // ---------- fart emission -------------------------------------------
  let fartTimer = 0;
  let fartDirX = 0, fartDirY = -1;

  function triggerFart(dirX, dirY) {
    const len = Math.hypot(dirX, dirY) || 1;
    fartDirX = dirX / len; fartDirY = dirY / len;
    fartTimer = 0.35;
    const charEl = document.getElementById('fluidChar');
    if (charEl) {
      charEl.classList.add('toot');
      setTimeout(() => charEl.classList.remove('toot'), 140);
    }
    playTootSound();
  }

  function emitFart(dt) {
    if (fartTimer <= 0) return;
    fartTimer -= dt;
    const spread = 0.5;
    for (let k = 0; k < 3; k++) {
      const jitterX = fartDirX + (Math.random() - 0.5) * spread;
      const jitterY = fartDirY + (Math.random() - 0.5) * spread;
      addDensity(emitterX + rand(-1.5, 1.5), emitterY + rand(-1.5, 1.5), rand(2.0, 3.2));
      addVelocity(emitterX, emitterY, jitterX * 11, jitterY * 11);
    }
  }
  function rand(a, b) { return a + Math.random() * (b - a); }

  // ---------- sound (own tiny Web Audio setup, no shared globals) -----
  let fluidAudioCtx = null;
  function ensureFluidAudio() {
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return null;
    if (!fluidAudioCtx) fluidAudioCtx = new AC();
    if (fluidAudioCtx.state === 'suspended') fluidAudioCtx.resume();
    return fluidAudioCtx;
  }
  function playTootSound() {
    const ctx = ensureFluidAudio();
    if (!ctx) return;
    const t0 = ctx.currentTime;
    const osc = ctx.createOscillator();
    const gain = ctx.createGain();
    osc.type = 'sawtooth';
    osc.frequency.setValueAtTime(160, t0);
    osc.frequency.exponentialRampToValueAtTime(55, t0 + 0.35);
    gain.gain.setValueAtTime(0, t0);
    gain.gain.linearRampToValueAtTime(0.12, t0 + 0.02);
    gain.gain.exponentialRampToValueAtTime(0.0001, t0 + 0.38);
    osc.connect(gain).connect(ctx.destination);
    osc.start(t0);
    osc.stop(t0 + 0.4);
  }

  // ---------- rendering -------------------------------------------------
  const canvas = document.getElementById('fluidCanvas');
  const ctx = canvas.getContext('2d', { alpha: false });
  canvas.width = N;
  canvas.height = N;
  const img = ctx.createImageData(N, N);

  // gas color derived from the user's palette (near yellow/green - a "toxic" tint)
  const GAS_R = 200, GAS_G = 214, GAS_B = 96;
  const BG_R = 8, BG_G = 10, BG_B = 14;

  function render() {
    const data = img.data;
    for (let j = 1; j <= N; j++) {
      for (let i = 1; i <= N; i++) {
        const raw = density[IX(i, j)] * 3.2;
        const d = Math.min(1, Math.sqrt(raw)); // sqrt curve: boosts visibility only, sim physics unaffected
        const p = ((j - 1) * N + (i - 1)) * 4;
        data[p] = BG_R + (GAS_R - BG_R) * d;
        data[p + 1] = BG_G + (GAS_G - BG_G) * d;
        data[p + 2] = BG_B + (GAS_B - BG_B) * d;
        data[p + 3] = 255;
      }
    }
    ctx.putImageData(img, 0, 0);
  }

  // ---------- interaction ------------------------------------------------
  function clientToGrid(clientX, clientY) {
    const rect = canvas.getBoundingClientRect();
    return [
      ((clientX - rect.left) / rect.width) * N,
      ((clientY - rect.top) / rect.height) * N,
    ];
  }

  canvas.addEventListener('pointerdown', (ev) => {
    ensureFluidAudio();
    const [gx, gy] = clientToGrid(ev.clientX, ev.clientY);
    triggerFart(gx - emitterX, gy - emitterY);
  });

  document.getElementById('fluidClearBtn').addEventListener('click', () => {
    Vx.fill(0); Vy.fill(0); Vx0.fill(0); Vy0.fill(0);
    density.fill(0); density0.fill(0);
    fartTimer = 0;
  });

  // ---------- main loop (paused while this view is hidden) --------------
  let running = false;
  let lastT = 0;

  function loop(now) {
    if (!running) return;
    if (!lastT) lastT = now;
    let dt = (now - lastT) / 1000;
    lastT = now;
    if (dt > 0.1) dt = 0.1;

    emitFart(dt);
    step();
    render();

    requestAnimationFrame(loop);
  }

  window.pauseFluid = function () { running = false; };
  window.resumeFluid = function () {
    if (running) return;
    running = true;
    lastT = 0;
    requestAnimationFrame(loop);
  };
})();
