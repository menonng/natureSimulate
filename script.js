'use strict';
/* ============================================================
   먹이 피라미드 시뮬레이터 (Food Pyramid Simulator)
   Pure canvas + vanilla JS ecosystem sandbox.
   ============================================================ */

// ---------- CONFIG ----------------------------------------------------
const COLS = 90;
const ROWS = 118;
const TICK_DT = 1 / 20;           // simulation seconds per tick (base)
const MAX_TICKS_PER_FRAME = 40;

const BUCKET_SIZE = 6;
const BUCKET_COLS = Math.ceil(COLS / BUCKET_SIZE);
const BUCKET_ROWS = Math.ceil(ROWS / BUCKET_SIZE);

const BURN_DURATION = 3.5;        // seconds a cell stays actively burning
const BURNT_RECOVERY = 55;        // seconds before burnt land can regrow

const RABBIT_CAP = 240;
const FOX_CAP = 55;
const HAWK_CAP = 12;

const COLORS = {
  landDark: [21, 46, 17],
  grassBright: [85, 187, 68],     // --green
  water: [51, 85, 187],           // --blue
  waterHi: [57, 197, 187],        // --sky
  burning: [255, 126, 0],         // --orange
  burningHot: [255, 0, 69],       // --red
  burnt: [14, 9, 8],
  rabbit: '#f1e9d8',
  fox: '#FF7E00',
  hawk: '#9B6FD8',                // derived from --purple, lightened
};

// ---------- STATE -------------------------------------------------------
const cellType = new Uint8Array(COLS * ROWS);   // 0 land/grass, 1 water, 2 burning, 3 burnt
const grass = new Float32Array(COLS * ROWS);    // 0..1 grass amount (valid on type 0)
const burnTimer = new Float32Array(COLS * ROWS);
const burntTimer = new Float32Array(COLS * ROWS);
const texNoise = new Float32Array(COLS * ROWS); // static texture noise for mottled look

let entities = [];   // {type:'rabbit'|'fox'|'hawk', x,y, vx,vy, energy, cooldown, age}
let nextId = 1;

const params = {
  grassRegrow: 0.006,
  fireSpread: 0.45,
  brushSize: 4,
};

let currentTool = 'grass';
let speedMultiplier = 1;
let simTime = 0;
let lastFrameTime = 0;
let accumulator = 0;

const history = []; // {r,f,h,g}
const HISTORY_MAX = 160;
let sampleAccum = 0;
const SAMPLE_INTERVAL = 0.75; // seconds

// ---------- HELPERS -------------------------------------------------------
function idx(x, y) { return y * COLS + x; }
function inBounds(x, y) { return x >= 0 && x < COLS && y >= 0 && y < ROWS; }
function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
function lerp(a, b, t) { return a + (b - a) * t; }
function rand(a, b) { return a + Math.random() * (b - a); }
function randInt(a, b) { return Math.floor(rand(a, b + 1)); }
function dist2(x1, y1, x2, y2) { const dx = x1 - x2, dy = y1 - y2; return dx * dx + dy * dy; }

function smoothNoise(w, h) {
  const raw = new Float32Array(w * h);
  for (let i = 0; i < raw.length; i++) raw[i] = Math.random();
  const out = new Float32Array(w * h);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      let sum = 0, n = 0;
      for (let dy = -2; dy <= 2; dy++) {
        for (let dx = -2; dx <= 2; dx++) {
          const nx = x + dx, ny = y + dy;
          if (nx >= 0 && nx < w && ny >= 0 && ny < h) { sum += raw[ny * w + nx]; n++; }
        }
      }
      out[y * w + x] = sum / n;
    }
  }
  return out;
}

// ---------- TERRAIN GENERATION -------------------------------------------
function generateTerrainBase() {
  const noise = smoothNoise(COLS, ROWS);
  for (let y = 0; y < ROWS; y++) {
    for (let x = 0; x < COLS; x++) {
      const i = idx(x, y);
      cellType[i] = 0;
      grass[i] = clamp(0.35 + (noise[i] - 0.5) * 1.3, 0, 1);
      burnTimer[i] = 0;
      burntTimer[i] = 0;
      texNoise[i] = Math.random();
    }
  }
}

function carveRiver() {
  // random-walk a winding river band across the map (roughly horizontal, like the reference art)
  const startY = randInt(Math.floor(ROWS * 0.38), Math.floor(ROWS * 0.55));
  let y = startY;
  let vy = 0;
  const baseWidth = rand(2.2, 3.4);
  const points = [];
  for (let x = -2; x <= COLS + 2; x++) {
    vy += rand(-0.35, 0.35);
    vy = clamp(vy, -1.1, 1.1);
    y += vy * 0.6;
    y = clamp(y, ROWS * 0.15, ROWS * 0.85);
    points.push({ x, y });
  }
  for (const p of points) {
    const width = baseWidth + Math.sin(p.x * 0.15) * 0.8;
    for (let dy = -Math.ceil(width); dy <= Math.ceil(width); dy++) {
      const gy = Math.round(p.y + dy);
      const gx = Math.round(p.x);
      if (!inBounds(gx, gy)) continue;
      if (Math.abs(dy) <= width) {
        const i = idx(gx, gy);
        cellType[i] = 1;
        grass[i] = 0;
      }
    }
  }
}

function scatterInitialLife() {
  entities = [];
  spawnBatch('rabbit', 46);
  spawnBatch('fox', 9);
  spawnBatch('hawk', 3);
}

function spawnBatch(type, count) {
  let placed = 0, guard = 0;
  while (placed < count && guard < count * 40) {
    guard++;
    const x = rand(1, COLS - 1);
    const y = rand(1, ROWS - 1);
    const i = idx(Math.floor(x), Math.floor(y));
    if (cellType[i] === 1) continue; // no water spawn
    addEntity(type, x, y);
    placed++;
  }
}

function addEntity(type, x, y) {
  const base = {
    id: nextId++, type, x, y,
    vx: rand(-1, 1), vy: rand(-1, 1),
    age: 0, cooldown: rand(0, 3),
  };
  if (type === 'rabbit') base.energy = rand(4, 7);
  else if (type === 'fox') base.energy = rand(8, 13);
  else base.energy = rand(14, 20);
  entities.push(base);
}

function regenerateWorld() {
  generateTerrainBase();
  carveRiver();
  scatterInitialLife();
  history.length = 0;
  simTime = 0;
}

// ---------- SPATIAL BUCKETS -----------------------------------------------
let buckets = new Map();
function rebuildBuckets() {
  buckets.clear();
  for (let k = 0; k < entities.length; k++) {
    const e = entities[k];
    const bx = Math.floor(e.x / BUCKET_SIZE), by = Math.floor(e.y / BUCKET_SIZE);
    const key = bx + ',' + by;
    let arr = buckets.get(key);
    if (!arr) { arr = []; buckets.set(key, arr); }
    arr.push(k);
  }
}

function findNearest(x, y, radius, predicate) {
  const br = Math.ceil(radius / BUCKET_SIZE);
  const bx0 = Math.floor(x / BUCKET_SIZE), by0 = Math.floor(y / BUCKET_SIZE);
  let best = -1, bestD = radius * radius;
  for (let by = by0 - br; by <= by0 + br; by++) {
    for (let bx = bx0 - br; bx <= bx0 + br; bx++) {
      const arr = buckets.get(bx + ',' + by);
      if (!arr) continue;
      for (const k of arr) {
        const e = entities[k];
        if (!predicate(e)) continue;
        const d = dist2(x, y, e.x, e.y);
        if (d < bestD) { bestD = d; best = k; }
      }
    }
  }
  return best;
}

// ---------- SIMULATION TICK -----------------------------------------------
function tickTerrain(dt) {
  for (let i = 0; i < cellType.length; i++) {
    const t = cellType[i];
    if (t === 0) {
      if (grass[i] < 1) grass[i] = clamp(grass[i] + params.grassRegrow * dt, 0, 1);
    } else if (t === 2) {
      burnTimer[i] -= dt;
      if (burnTimer[i] <= 0) {
        cellType[i] = 3;
        burntTimer[i] = BURNT_RECOVERY;
      }
    } else if (t === 3) {
      burntTimer[i] -= dt;
      if (burntTimer[i] <= 0) {
        cellType[i] = 0;
        grass[i] = 0;
      }
    }
  }
  spreadFire(dt);
}

function spreadFire(dt) {
  // sample burning cells and try to ignite flammable neighbours
  for (let y = 0; y < ROWS; y++) {
    for (let x = 0; x < COLS; x++) {
      const i = idx(x, y);
      if (cellType[i] !== 2) continue;
      for (let dy = -1; dy <= 1; dy++) {
        for (let dx = -1; dx <= 1; dx++) {
          if (dx === 0 && dy === 0) continue;
          const nx = x + dx, ny = y + dy;
          if (!inBounds(nx, ny)) continue;
          const ni = idx(nx, ny);
          if (cellType[ni] !== 0) continue;
          const fuel = grass[ni];
          if (fuel < 0.08) continue;
          const diag = (dx !== 0 && dy !== 0) ? 0.55 : 1;
          const chance = params.fireSpread * fuel * diag * dt * 1.6;
          if (Math.random() < chance) {
            cellType[ni] = 2;
            burnTimer[ni] = BURN_DURATION * rand(0.7, 1.3);
          }
        }
      }
    }
  }
}

function tickEntities(dt) {
  rebuildBuckets();
  const next = [];
  for (const e of entities) {
    e.age += dt;
    e.cooldown = Math.max(0, e.cooldown - dt);
    let alive = true;
    if (e.type === 'rabbit') alive = updateRabbit(e, dt, next);
    else if (e.type === 'fox') alive = updateFox(e, dt, next);
    else alive = updateHawk(e, dt, next);
    if (alive) next.push(e);
  }
  entities = next;
}

function cellAt(x, y) {
  const gx = clamp(Math.floor(x), 0, COLS - 1);
  const gy = clamp(Math.floor(y), 0, ROWS - 1);
  return idx(gx, gy);
}

function steerRandom(e, speed, dt) {
  e.vx += rand(-0.6, 0.6);
  e.vy += rand(-0.6, 0.6);
  const len = Math.hypot(e.vx, e.vy) || 1;
  e.vx = (e.vx / len) * speed;
  e.vy = (e.vy / len) * speed;
  tryMove(e, dt);
}

function tryMove(e, dt) {
  const nx = e.x + e.vx * dt;
  const ny = e.y + e.vy * dt;
  const isHawk = e.type === 'hawk';
  if (nx < 0 || nx >= COLS || ny < 0 || ny >= ROWS) {
    e.vx *= -1; e.vy *= -1;
    return;
  }
  if (!isHawk) {
    const t = cellType[cellAt(nx, ny)];
    if (t === 1) { // water blocks land animals
      e.vx *= -1; e.vy *= -1;
      return;
    }
  }
  e.x = nx; e.y = ny;
}

function updateRabbit(e, dt, spawnList) {
  e.energy -= 0.5 * dt;
  const i = cellAt(e.x, e.y);

  if (cellType[i] === 2) { // standing in fire
    if (Math.random() < 0.5 * dt * 10) return false;
  }
  if (cellType[i] === 0 && grass[i] > 0.04) {
    const eat = Math.min(grass[i], 0.35 * dt);
    grass[i] -= eat;
    e.energy += eat * 3.2;
  }

  // flee foxes
  const foxK = findNearest(e.x, e.y, 7, (o) => o.type === 'fox');
  if (foxK >= 0) {
    const f = entities[foxK];
    const dx = e.x - f.x, dy = e.y - f.y;
    const len = Math.hypot(dx, dy) || 1;
    e.vx = (dx / len) * 3.4;
    e.vy = (dy / len) * 3.4;
    tryMove(e, dt);
  } else {
    // seek grass
    let bestScore = -1, bestX = e.x, bestY = e.y;
    for (let s = 0; s < 4; s++) {
      const sx = clamp(e.x + rand(-4, 4), 0, COLS - 1);
      const sy = clamp(e.y + rand(-4, 4), 0, ROWS - 1);
      const si = cellAt(sx, sy);
      if (cellType[si] !== 0) continue;
      const score = grass[si] + Math.random() * 0.1;
      if (score > bestScore) { bestScore = score; bestX = sx; bestY = sy; }
    }
    const dx = bestX - e.x, dy = bestY - e.y;
    const len = Math.hypot(dx, dy) || 1;
    e.vx = lerp(e.vx, (dx / len) * 1.6, 0.4);
    e.vy = lerp(e.vy, (dy / len) * 1.6, 0.4);
    tryMove(e, dt);
  }

  if (e.energy > 6.5 && e.cooldown <= 0 && countType('rabbit') < RABBIT_CAP) {
    e.energy -= 3;
    e.cooldown = 4.5;
    spawnList.push(makeChild(e, 'rabbit'));
  }
  return e.energy > 0;
}

function updateFox(e, dt, spawnList) {
  e.energy -= 0.32 * dt;
  const i = cellAt(e.x, e.y);
  if (cellType[i] === 2 && Math.random() < 0.4 * dt * 10) return false;

  const preyK = findNearest(e.x, e.y, 10, (o) => o.type === 'rabbit');
  if (preyK >= 0) {
    const p = entities[preyK];
    const d = Math.hypot(p.x - e.x, p.y - e.y);
    if (d < 0.8) {
      entities[preyK]._dead = true;
      e.energy += 6.5;
    } else {
      const dx = p.x - e.x, dy = p.y - e.y;
      e.vx = lerp(e.vx, (dx / d) * 2.6, 0.5);
      e.vy = lerp(e.vy, (dy / d) * 2.6, 0.5);
      tryMove(e, dt);
    }
  } else {
    steerRandom(e, 1.3, dt);
  }

  if (e.energy > 13 && e.cooldown <= 0 && countType('fox') < FOX_CAP) {
    e.energy -= 6;
    e.cooldown = 8;
    spawnList.push(makeChild(e, 'fox'));
  }
  return e.energy > 0;
}

function updateHawk(e, dt, spawnList) {
  e.energy -= 0.18 * dt;

  const preyK = findNearest(e.x, e.y, 14, (o) => (o.type === 'rabbit' || o.type === 'fox'));
  if (preyK >= 0) {
    const p = entities[preyK];
    const d = Math.hypot(p.x - e.x, p.y - e.y);
    if (d < 0.9) {
      if (Math.random() < 0.5) {
        entities[preyK]._dead = true;
        e.energy += p.type === 'rabbit' ? 9 : 13;
      }
    } else {
      const dx = p.x - e.x, dy = p.y - e.y;
      e.vx = lerp(e.vx, (dx / d) * 3.6, 0.5);
      e.vy = lerp(e.vy, (dy / d) * 3.6, 0.5);
    }
  } else {
    e.vx += rand(-0.3, 0.3);
    e.vy += rand(-0.3, 0.3);
    const len = Math.hypot(e.vx, e.vy) || 1;
    e.vx = (e.vx / len) * 1.4;
    e.vy = (e.vy / len) * 1.4;
  }
  tryMove(e, dt);

  if (e.energy > 22 && e.cooldown <= 0 && countType('hawk') < HAWK_CAP) {
    e.energy -= 12;
    e.cooldown = 20;
    spawnList.push(makeChild(e, 'hawk'));
  }
  return e.energy > 0;
}

function makeChild(parent, type) {
  return {
    id: nextId++, type,
    x: clamp(parent.x + rand(-1.5, 1.5), 0, COLS - 1),
    y: clamp(parent.y + rand(-1.5, 1.5), 0, ROWS - 1),
    vx: rand(-1, 1), vy: rand(-1, 1),
    energy: type === 'rabbit' ? 3 : type === 'fox' ? 5 : 8,
    cooldown: 3, age: 0,
  };
}

function countType(type) {
  let n = 0;
  for (const e of entities) if (e.type === type) n++;
  return n;
}

function purgeDead() {
  entities = entities.filter((e) => !e._dead);
}

function tick() {
  tickTerrain(TICK_DT);
  tickEntities(TICK_DT);
  purgeDead();
  simTime += TICK_DT;

  sampleAccum += TICK_DT;
  if (sampleAccum >= SAMPLE_INTERVAL) {
    sampleAccum = 0;
    sampleHistory();
  }
}

function sampleHistory() {
  let r = 0, f = 0, h = 0, gsum = 0, gn = 0;
  for (const e of entities) {
    if (e.type === 'rabbit') r++;
    else if (e.type === 'fox') f++;
    else h++;
  }
  for (let i = 0; i < cellType.length; i += 7) {
    if (cellType[i] === 0) { gsum += grass[i]; gn++; }
  }
  const g = gn ? gsum / gn : 0;
  history.push({ r, f, h, g });
  if (history.length > HISTORY_MAX) history.shift();
  updateCounts(r, f, h, g);
}

// ---------- RENDERING -----------------------------------------------------
const terrainCanvas = document.getElementById('terrainCanvas');
const tctx = terrainCanvas.getContext('2d', { alpha: false });
const entityCanvas = document.getElementById('entityCanvas');
const ectx = entityCanvas.getContext('2d');
const canvasWrap = document.getElementById('canvasWrap');

terrainCanvas.width = COLS;
terrainCanvas.height = ROWS;
const terrainImage = tctx.createImageData(COLS, ROWS);

function resizeEntityCanvas() {
  const rect = canvasWrap.getBoundingClientRect();
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  entityCanvas.width = Math.max(1, Math.round(rect.width * dpr));
  entityCanvas.height = Math.max(1, Math.round(rect.height * dpr));
}
window.addEventListener('resize', resizeEntityCanvas);

function renderTerrain() {
  const data = terrainImage.data;
  const t = simTime;
  for (let y = 0; y < ROWS; y++) {
    for (let x = 0; x < COLS; x++) {
      const i = idx(x, y);
      const p = i * 4;
      const type = cellType[i];
      let r, g, b;
      if (type === 0) {
        const shade = clamp(grass[i], 0, 1);
        const texVar = (texNoise[i] - 0.5) * 18;
        r = lerp(COLORS.landDark[0], COLORS.grassBright[0], shade) + texVar;
        g = lerp(COLORS.landDark[1], COLORS.grassBright[1], shade) + texVar;
        b = lerp(COLORS.landDark[2], COLORS.grassBright[2], shade) + texVar * 0.4;
      } else if (type === 1) {
        const ripple = (Math.sin(x * 0.35 + t * 1.6) + Math.sin(y * 0.3 - t * 1.1)) * 0.5;
        const m = ripple > 0.55 ? 1 : 0;
        r = lerp(COLORS.water[0], COLORS.waterHi[0], m * 0.5);
        g = lerp(COLORS.water[1], COLORS.waterHi[1], m * 0.5);
        b = lerp(COLORS.water[2], COLORS.waterHi[2], m * 0.5);
      } else if (type === 2) {
        const flick = 0.5 + 0.5 * Math.sin(t * 14 + (x * 7 + y * 13) % 17);
        r = lerp(COLORS.burningHot[0], COLORS.burning[0], flick);
        g = lerp(COLORS.burningHot[1], COLORS.burning[1], flick);
        b = lerp(COLORS.burningHot[2], COLORS.burning[2], flick);
      } else {
        const ember = burntTimer[i] > BURNT_RECOVERY - 8 && texNoise[i] > 0.85;
        if (ember) { r = 200; g = 70; b = 20; }
        else { r = COLORS.burnt[0]; g = COLORS.burnt[1]; b = COLORS.burnt[2]; }
      }
      data[p] = clamp(r, 0, 255);
      data[p + 1] = clamp(g, 0, 255);
      data[p + 2] = clamp(b, 0, 255);
      data[p + 3] = 255;
    }
  }
  tctx.putImageData(terrainImage, 0, 0);
}

function renderEntities() {
  const w = entityCanvas.width, h = entityCanvas.height;
  ectx.clearRect(0, 0, w, h);
  const sx = w / COLS, sy = h / ROWS;
  const r = Math.max(1.6, Math.min(sx, sy) * 0.62);

  for (const e of entities) {
    const cx = e.x * sx, cy = e.y * sy;
    if (e.type === 'rabbit') {
      ectx.fillStyle = COLORS.rabbit;
      ectx.beginPath();
      ectx.ellipse(cx, cy, r * 0.9, r * 0.65, 0, 0, Math.PI * 2);
      ectx.fill();
    } else if (e.type === 'fox') {
      ectx.fillStyle = COLORS.fox;
      ectx.beginPath();
      ectx.moveTo(cx, cy - r * 1.1);
      ectx.lineTo(cx + r * 0.95, cy + r * 0.8);
      ectx.lineTo(cx - r * 0.95, cy + r * 0.8);
      ectx.closePath();
      ectx.fill();
    } else {
      const shadowY = cy + r * 0.35;
      ectx.fillStyle = 'rgba(0,0,0,0.28)';
      ectx.beginPath();
      ectx.ellipse(cx, shadowY, r * 1.1, r * 0.35, 0, 0, Math.PI * 2);
      ectx.fill();

      ectx.strokeStyle = COLORS.hawk;
      ectx.lineWidth = Math.max(1.2, r * 0.32);
      ectx.lineCap = 'round';
      const wing = r * 1.35;
      const flap = Math.sin(simTime * 9 + e.id) * r * 0.35;
      ectx.beginPath();
      ectx.moveTo(cx - wing, cy - flap);
      ectx.quadraticCurveTo(cx, cy + r * 0.4, cx + wing, cy - flap);
      ectx.stroke();
    }
  }
}

// ---------- GRAPH -----------------------------------------------------
const graphCanvas = document.getElementById('graphCanvas');
const gctx = graphCanvas.getContext('2d');

function resizeGraph() {
  const rect = graphCanvas.getBoundingClientRect();
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  graphCanvas.width = Math.max(1, Math.round(rect.width * dpr));
  graphCanvas.height = Math.max(1, Math.round(rect.height * dpr));
}
window.addEventListener('resize', resizeGraph);

function drawSeries(values, color, w, h, pad) {
  if (values.length < 2) return;
  let max = 0;
  for (const v of values) if (v > max) max = v;
  max = max * 1.15 || 1;
  gctx.strokeStyle = color;
  gctx.lineWidth = Math.max(1, h * 0.018);
  gctx.beginPath();
  for (let i = 0; i < values.length; i++) {
    const x = pad + (i / (HISTORY_MAX - 1)) * (w - pad * 2);
    const y = h - pad - (values[i] / max) * (h - pad * 2);
    if (i === 0) gctx.moveTo(x, y); else gctx.lineTo(x, y);
  }
  gctx.stroke();
}

function renderGraph() {
  const w = graphCanvas.width, h = graphCanvas.height;
  gctx.clearRect(0, 0, w, h);
  gctx.fillStyle = '#0c0a08';
  gctx.fillRect(0, 0, w, h);
  if (history.length < 2) return;
  const pad = h * 0.08;
  drawSeries(history.map((s) => s.g), '#39C5BB', w, h, pad);
  drawSeries(history.map((s) => s.r), '#55BB44', w, h, pad);
  drawSeries(history.map((s) => s.f), '#FF7E00', w, h, pad);
  drawSeries(history.map((s) => s.h), '#9B6FD8', w, h, pad);
}

function updateCounts(r, f, h, g) {
  document.getElementById('cntRabbit').textContent = `🐇 ${r}`;
  document.getElementById('cntFox').textContent = `🦊 ${f}`;
  document.getElementById('cntHawk').textContent = `🦅 ${h}`;
  document.getElementById('cntGrass').textContent = `🌱 ${Math.round(g * 100)}%`;
}

// ---------- INPUT / TOOLS -----------------------------------------------
const CREATURE_TOOLS = new Set(['rabbit', 'fox', 'hawk']);
let pointerDown = false;

function clientToGrid(clientX, clientY) {
  const rect = entityCanvas.getBoundingClientRect();
  const gx = ((clientX - rect.left) / rect.width) * COLS;
  const gy = ((clientY - rect.top) / rect.height) * ROWS;
  return [gx, gy];
}

function applyTool(gx, gy, isDown) {
  if (CREATURE_TOOLS.has(currentTool)) {
    if (!isDown) return;
    const count = currentTool === 'rabbit' ? RABBIT_CAP : currentTool === 'fox' ? FOX_CAP : HAWK_CAP;
    if (countType(currentTool) < count) addEntity(currentTool, clamp(gx, 0, COLS - 1), clamp(gy, 0, ROWS - 1));
    return;
  }

  const radius = params.brushSize;
  const x0 = Math.max(0, Math.floor(gx - radius));
  const x1 = Math.min(COLS - 1, Math.ceil(gx + radius));
  const y0 = Math.max(0, Math.floor(gy - radius));
  const y1 = Math.min(ROWS - 1, Math.ceil(gy + radius));

  if (currentTool === 'erase') {
    entities = entities.filter((e) => dist2(e.x, e.y, gx, gy) > radius * radius);
    return;
  }

  for (let y = y0; y <= y1; y++) {
    for (let x = x0; x <= x1; x++) {
      if (dist2(x, y, gx, gy) > radius * radius) continue;
      const i = idx(x, y);
      if (currentTool === 'grass') { cellType[i] = 0; grass[i] = 1; }
      else if (currentTool === 'land') { cellType[i] = 0; grass[i] = 0; }
      else if (currentTool === 'water') { cellType[i] = 1; grass[i] = 0; }
      else if (currentTool === 'fire') {
        if (cellType[i] === 0 && grass[i] > 0.04) { cellType[i] = 2; burnTimer[i] = BURN_DURATION; }
      }
    }
  }
}

function bindPointer() {
  entityCanvas.addEventListener('pointerdown', (ev) => {
    pointerDown = true;
    entityCanvas.setPointerCapture(ev.pointerId);
    const [gx, gy] = clientToGrid(ev.clientX, ev.clientY);
    applyTool(gx, gy, true);
  });
  entityCanvas.addEventListener('pointermove', (ev) => {
    if (!pointerDown) return;
    const [gx, gy] = clientToGrid(ev.clientX, ev.clientY);
    applyTool(gx, gy, false);
  });
  window.addEventListener('pointerup', () => { pointerDown = false; });
  window.addEventListener('pointercancel', () => { pointerDown = false; });
}

// ---------- UI BINDINGS -----------------------------------------------
function bindUI() {
  document.querySelectorAll('.toolBtn').forEach((btn) => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('.toolBtn').forEach((b) => b.classList.remove('active'));
      btn.classList.add('active');
      currentTool = btn.dataset.tool;
    });
  });

  document.querySelectorAll('.speedBtn').forEach((btn) => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('.speedBtn').forEach((b) => b.classList.remove('active'));
      btn.classList.add('active');
      speedMultiplier = Number(btn.dataset.speed);
    });
  });

  document.getElementById('genRiverBtn').addEventListener('click', () => {
    carveRiver();
  });

  document.getElementById('resetBtn').addEventListener('click', () => {
    regenerateWorld();
  });

  const grassSlider = document.getElementById('grassRateSlider');
  grassSlider.addEventListener('input', () => {
    params.grassRegrow = lerp(0.0008, 0.02, grassSlider.value / 100);
  });
  params.grassRegrow = lerp(0.0008, 0.02, grassSlider.value / 100);

  const fireSlider = document.getElementById('fireRateSlider');
  fireSlider.addEventListener('input', () => {
    params.fireSpread = lerp(0.05, 1.4, fireSlider.value / 100);
  });
  params.fireSpread = lerp(0.05, 1.4, fireSlider.value / 100);

  const brushSlider = document.getElementById('brushSizeSlider');
  brushSlider.addEventListener('input', () => {
    params.brushSize = Number(brushSlider.value);
  });
  params.brushSize = Number(brushSlider.value);
}

// ---------- MAIN LOOP -----------------------------------------------------
function frame(now) {
  if (!lastFrameTime) lastFrameTime = now;
  let dt = (now - lastFrameTime) / 1000;
  lastFrameTime = now;
  if (dt > 0.25) dt = 0.25; // guard against tab-suspend jumps

  if (speedMultiplier > 0) {
    accumulator += dt * speedMultiplier;
    let n = 0;
    while (accumulator >= TICK_DT && n < MAX_TICKS_PER_FRAME) {
      tick();
      accumulator -= TICK_DT;
      n++;
    }
  }

  renderTerrain();
  renderEntities();
  renderGraph();

  requestAnimationFrame(frame);
}

document.addEventListener('visibilitychange', () => {
  if (!document.hidden) lastFrameTime = 0;
});

// ---------- INIT -----------------------------------------------------
function init() {
  regenerateWorld();
  resizeEntityCanvas();
  resizeGraph();
  bindUI();
  bindPointer();
  sampleHistory();
  requestAnimationFrame(frame);
}

init();
