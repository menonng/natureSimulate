'use strict';
/* ============================================================
   먹이 피라미드 시뮬레이터 (Food Pyramid Simulator)
   Pure canvas + vanilla JS ecosystem sandbox.
   ============================================================ */

// ---------- CONFIG ----------------------------------------------------
const COLS = 135;   // 1.5x wider than the original 90 — the box grows sideways, not taller
const ROWS = 118;
const TICK_DT = 1 / 20;           // simulation seconds per tick (base)
const MAX_TICKS_PER_FRAME = 40;

const BUCKET_SIZE = 6;
const BUCKET_COLS = Math.ceil(COLS / BUCKET_SIZE);
const BUCKET_ROWS = Math.ceil(ROWS / BUCKET_SIZE);

const BURN_DURATION = 3.5;        // seconds a cell stays actively burning
const BURNT_RECOVERY = 55;        // seconds before burnt land can regrow

// No population ceiling - breeding and manual placement are limited only
// by energy/cooldown/food, not an artificial headcount.
const RABBIT_CAP = Infinity;
const FOX_CAP = Infinity;
const HAWK_CAP = Infinity;

const COLORS = {
  landDark: [21, 46, 17],
  grassBright: [85, 187, 68],     // --green
  water: [51, 85, 187],           // --blue
  waterHi: [57, 197, 187],        // --sky
  burning: [255, 126, 0],         // --orange
  burningHot: [255, 0, 69],       // --red
  burnt: [42, 15, 11],            // dark scorched maroon-brown, matched to reference art
  emberGlow: [168, 48, 20],
};

const EMOJI = { rabbit: '🐇', fox: '🦊', hawk: '🦅' };

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
let tickCount = 0;

// Movement-trail toggles: independent per species, multi-select.
const trailVisible = { rabbit: false, fox: false, hawk: false };
const TRAIL_MAX_POINTS = 16;
const TRAIL_RECORD_EVERY = 3; // ticks

// Births/deaths that happened during the current tick, so several
// simultaneous events can be unrolled into one graph point each (see
// sampleHistory) instead of one big vertical jump.
let tickEvents = [];

const history = []; // {r,f,h,g}
// Sample every simulation tick (the smallest time unit the sim has) so the
// graph reflects what actually happened at full resolution regardless of
// the speed multiplier, instead of aliasing/smoothing over a coarser window.
const HISTORY_MAX = 2400; // 2400 * TICK_DT = 120s of simulated time
let sampleAccum = 0;
const SAMPLE_INTERVAL = TICK_DT;

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

// ---------- SOUND EFFECTS -------------------------------------------------
// Tiny synthesized beeps (no audio files) for two events: a catch and a
// birth. Lazily created/resumed on the first user gesture per browser
// autoplay rules.
let audioCtx = null;
function ensureAudio() {
  const AC = window.AudioContext || window.webkitAudioContext;
  if (!AC) return null;
  if (!audioCtx) audioCtx = new AC();
  if (audioCtx.state === 'suspended') audioCtx.resume();
  return audioCtx;
}
document.addEventListener('pointerdown', ensureAudio, { once: true });

function playTone(freq, duration, type, peakGain, startDelay) {
  const ctx = ensureAudio();
  if (!ctx) return;
  const t0 = ctx.currentTime + (startDelay || 0);
  const osc = ctx.createOscillator();
  const gain = ctx.createGain();
  osc.type = type;
  osc.frequency.setValueAtTime(freq, t0);
  gain.gain.setValueAtTime(0, t0);
  gain.gain.linearRampToValueAtTime(peakGain, t0 + 0.008);
  gain.gain.exponentialRampToValueAtTime(0.0001, t0 + duration);
  osc.connect(gain).connect(ctx.destination);
  osc.start(t0);
  osc.stop(t0 + duration + 0.02);
}

// Rate-limited so a fast-forwarded sim (many catches/births per real second)
// doesn't turn into a wall of overlapping noise.
let lastCaptureSound = 0, lastBreedSound = 0;
const SOUND_MIN_GAP = 0.05; // seconds

function playCaptureSound() {
  const now = performance.now() / 1000;
  if (now - lastCaptureSound < SOUND_MIN_GAP) return;
  lastCaptureSound = now;
  playTone(680, 0.09, 'square', 0.07);
  playTone(260, 0.11, 'square', 0.05, 0.03);
}

function playBreedSound() {
  const now = performance.now() / 1000;
  if (now - lastBreedSound < SOUND_MIN_GAP) return;
  lastBreedSound = now;
  playTone(523, 0.08, 'triangle', 0.06);
  playTone(784, 0.10, 'triangle', 0.06, 0.07);
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
  spawnBatch('rabbit', 69);
  spawnBatch('fox', 14);
  spawnBatch('hawk', 5);
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
// Bare ground (including recovering burn scars) never sprouts grass on its
// own. A cell only germinates (grass 0 -> a small sprout) when a seed
// actually arrives: wind carrying it from nearby grass, a land animal
// tracking it in, or - very rarely - a bird dropping one in flight.
// Once a sprout exists it is free to mature/thicken over time.
const SEED_SPROUT = 0.05;

function tickTerrain(dt) {
  for (let i = 0; i < cellType.length; i++) {
    const t = cellType[i];
    if (t === 0) {
      if (grass[i] > 0) {
        if (grass[i] < 1) grass[i] = clamp(grass[i] + params.grassRegrow * dt, 0, 1);
      } else {
        tryWindGerminate(i, dt);
      }
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

function tryWindGerminate(i, dt) {
  const x = i % COLS, y = (i / COLS) | 0;
  let neighborGrass = 0;
  for (let dy = -1; dy <= 1; dy++) {
    for (let dx = -1; dx <= 1; dx++) {
      if (dx === 0 && dy === 0) continue;
      const nx = x + dx, ny = y + dy;
      if (!inBounds(nx, ny)) continue;
      const ni = idx(nx, ny);
      if (cellType[ni] === 0) neighborGrass += grass[ni];
    }
  }
  if (neighborGrass <= 0) return;
  const chance = neighborGrass * params.grassRegrow * dt * 3.5;
  if (Math.random() < chance) grass[i] = SEED_SPROUT;
}

// A land animal passing over bare ground may carry in a seed (fur, droppings).
function trySeedFromAnimal(i, chance) {
  if (cellType[i] === 0 && grass[i] === 0 && Math.random() < chance) {
    grass[i] = SEED_SPROUT;
  }
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
  tickCount++;
  const recordTrails = tickCount % TRAIL_RECORD_EVERY === 0;
  const next = [];
  for (const e of entities) {
    e.age += dt;
    e.cooldown = Math.max(0, e.cooldown - dt);
    let alive = true;
    if (e.type === 'rabbit') alive = updateRabbit(e, dt, next);
    else if (e.type === 'fox') alive = updateFox(e, dt, next);
    else alive = updateHawk(e, dt, next);
    if (alive) {
      if (trailVisible[e.type]) {
        if (recordTrails) {
          if (!e.trail) e.trail = [];
          e.trail.push(e.x, e.y);
          if (e.trail.length > TRAIL_MAX_POINTS * 2) e.trail.splice(0, 2);
        }
      } else if (e.trail && e.trail.length) {
        e.trail.length = 0; // toggled off - stop showing a stale trail
      }
      next.push(e);
    } else {
      tickEvents.push({ type: e.type, delta: -1 }); // starved / burned / drowned
    }
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
  if (nx < 0 || nx >= COLS || ny < 0 || ny >= ROWS) {
    e.vx *= -1; e.vy *= -1;
    return;
  }
  // Land animals can now swim across rivers; drowning risk is handled
  // per-tick in updateRabbit/updateFox while they're in a water cell.
  e.x = nx; e.y = ny;
}

// 20%/sec chance of drowning while a land animal is in a water cell.
const DROWN_CHANCE_PER_SEC = 0.2;
function tryDrown(i, dt) {
  if (cellType[i] !== 1) return false;
  return Math.random() < 1 - Math.pow(1 - DROWN_CHANCE_PER_SEC, dt);
}

function updateRabbit(e, dt, spawnList) {
  e.energy -= 0.5 * dt;
  const i = cellAt(e.x, e.y);

  if (cellType[i] === 2) { // standing in fire
    if (Math.random() < 0.5 * dt * 10) return false;
  }
  if (tryDrown(i, dt)) return false;
  if (cellType[i] === 0 && grass[i] > 0.04) {
    const eat = Math.min(grass[i], 0.35 * dt);
    grass[i] -= eat;
    e.energy += eat * 3.2;
  } else {
    trySeedFromAnimal(i, 0.18 * dt);
  }

  // flee foxes (predator awareness, not food-detection)
  const foxK = findNearest(e.x, e.y, 7, (o) => o.type === 'fox');
  if (foxK >= 0) {
    const f = entities[foxK];
    const dx = e.x - f.x, dy = e.y - f.y;
    const len = Math.hypot(dx, dy) || 1;
    e.vx = (dx / len) * 1.6; // nerfed: slower flee
    e.vy = (dy / len) * 1.6;
    tryMove(e, dt);
  } else {
    // no food-detection range: wanders randomly, only eats grass it happens to be on
    steerRandom(e, 1.0, dt); // nerfed: slower wander speed
  }

  if (e.energy > 6.5 && e.cooldown <= 0 && countType('rabbit') < RABBIT_CAP) {
    e.energy -= 3;
    e.cooldown = 4.5;
    spawnList.push(makeChild(e, 'rabbit'));
    tickEvents.push({ type: 'rabbit', delta: 1 });
    playBreedSound();
  }
  return e.energy > 0;
}

function updateFox(e, dt, spawnList) {
  e.energy -= 0.38 * dt; // nerfed: hungrier
  const i = cellAt(e.x, e.y);
  if (cellType[i] === 2 && Math.random() < 0.4 * dt * 10) return false;
  if (tryDrown(i, dt)) return false;
  trySeedFromAnimal(i, 0.12 * dt);

  // Foxes don't search for prey from afar, but once a rabbit is close enough
  // to be mutually aware of (the same radius a rabbit uses to notice a fox),
  // the fox gives chase - and is fast enough to always run it down.
  const preyK = findNearest(e.x, e.y, 7, (o) => o.type === 'rabbit');
  if (preyK >= 0) {
    const p = entities[preyK];
    const d = Math.hypot(p.x - e.x, p.y - e.y);
    if (d < 0.8) {
      entities[preyK]._dead = true;
      e.energy += 5; // nerfed: less energy per catch
      playCaptureSound();

      // Only meat lets a fox breed - grass just keeps it fed.
      if (e.energy > 12 && e.cooldown <= 0 && countType('fox') < FOX_CAP) {
        e.energy -= 7;
        e.cooldown = 10;
        spawnList.push(makeChild(e, 'fox'));
        tickEvents.push({ type: 'fox', delta: 1 });
        playBreedSound();
      }
    } else {
      const dx = p.x - e.x, dy = p.y - e.y;
      e.vx = (dx / d) * 2.6; // buffed: faster than a fleeing rabbit -> guaranteed catch
      e.vy = (dy / d) * 2.6;
      tryMove(e, dt);
    }
  } else {
    // No rabbit around to chase - foxes are omnivores and will graze to
    // survive, but grass alone never earns them a breeding chance.
    if (cellType[i] === 0 && grass[i] > 0.04) {
      const eat = Math.min(grass[i], 0.15 * dt);
      grass[i] -= eat;
      e.energy += eat * 2.0;
    }
    steerRandom(e, 1.3, dt);
  }
  return e.energy > 0;
}

function updateHawk(e, dt, spawnList) {
  e.energy -= 0.14 * dt; // longer lifespan: burns energy much more slowly

  // A hawk can only take 1-2 kills per dive, then must climb back up
  // (huntCooldown) before it is allowed to strike again.
  if (e.diveCap === undefined) { e.diveCap = Math.random() < 0.5 ? 1 : 2; e.diveKills = 0; e.huntCooldown = 0; }
  if (e.huntCooldown > 0) e.huntCooldown -= dt;

  // Reactive chase within striking range (not a long-distance hunting
  // search): closes in at hunting speed, then strikes once adjacent.
  const preyK = findNearest(e.x, e.y, 7, (o) => (o.type === 'rabbit' || o.type === 'fox'));
  if (preyK >= 0) {
    const p = entities[preyK];
    const d = Math.hypot(p.x - e.x, p.y - e.y);
    if (d < 0.9) {
      if (e.huntCooldown <= 0 && Math.random() < 0.25) {
        entities[preyK]._dead = true;
        e.energy += p.type === 'rabbit' ? 7 : 10; // nerfed: less energy per catch
        playCaptureSound();
        e.diveKills++;

        // Breeding-at-the-kill: a fox catch is worth 2x a rabbit catch's
        // breeding chance. This runs alongside (not instead of) the
        // ordinary energy-threshold breeding check below.
        const breedChance = p.type === 'fox' ? 0.12 : 0.06; // halved, still 2x for a fox catch
        if (e.energy > 14 && e.cooldown <= 0 && countType('hawk') < HAWK_CAP && Math.random() < breedChance) {
          e.energy -= 14;
          e.cooldown = 24;
          spawnList.push(makeChild(e, 'hawk'));
          tickEvents.push({ type: 'hawk', delta: 1 });
          playBreedSound();
        }

        if (e.diveKills >= e.diveCap) {
          e.huntCooldown = rand(28, 49);
          e.diveKills = 0;
          e.diveCap = Math.random() < 0.5 ? 1 : 2;
        }
      }
    } else {
      e.vx = (p.x - e.x) / d * 2.8; // hunting speed: 2x the hawk's previous speed
      e.vy = (p.y - e.y) / d * 2.8;
      tryMove(e, dt);
    }
  } else {
    e.vx += rand(-0.3, 0.3);
    e.vy += rand(-0.3, 0.3);
    const len = Math.hypot(e.vx, e.vy) || 1;
    e.vx = (e.vx / len) * 3.9; // movement speed: 1.5x a fox's hunting speed
    e.vy = (e.vy / len) * 3.9;
    tryMove(e, dt);
  }
  trySeedFromAnimal(cellAt(e.x, e.y), 0.006 * dt); // a dropped seed, very rare

  if (e.energy > 26 && e.cooldown <= 0 && countType('hawk') < HAWK_CAP) { // nerfed: breeds later
    e.energy -= 14;
    e.cooldown = 24;
    spawnList.push(makeChild(e, 'hawk'));
    tickEvents.push({ type: 'hawk', delta: 1 });
    playBreedSound();
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
  entities = entities.filter((e) => {
    if (!e._dead) return true;
    tickEvents.push({ type: e.type, delta: -1 }); // eaten
    return false;
  });
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

  if (tickEvents.length === 0) {
    history.push({ r, f, h, g });
  } else {
    // Several births/deaths can land in the same tick (a wildfire wiping
    // out a dozen rabbits, a breeding burst, ...). Rather than one vertical
    // jump, walk back to the counts from before this tick's events, then
    // replay them one at a time so each individual event gets its own
    // point and the line rises/falls smoothly.
    let cr = r, cf = f, ch = h;
    for (let i = tickEvents.length - 1; i >= 0; i--) {
      const ev = tickEvents[i];
      if (ev.type === 'rabbit') cr -= ev.delta;
      else if (ev.type === 'fox') cf -= ev.delta;
      else ch -= ev.delta;
    }
    for (const ev of tickEvents) {
      if (ev.type === 'rabbit') cr += ev.delta;
      else if (ev.type === 'fox') cf += ev.delta;
      else ch += ev.delta;
      history.push({ r: cr, f: cf, h: ch, g });
    }
    tickEvents = [];
  }
  if (history.length > HISTORY_MAX) history.splice(0, history.length - HISTORY_MAX);
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

// ---------- VIEWPORT FIT -----------------------------------------------
// Sizes #app so the whole UI (toolbar, map, graph, sliders) fits within one
// browser window height at 100% zoom, with no vertical scrolling needed.
const appEl = document.getElementById('app');
const topbarEl = document.getElementById('topbar');
const toolbarEl = document.getElementById('toolbar');
const frameEl = document.getElementById('frame');
const bottomPanelEl = document.getElementById('bottomPanel');
const sliderRowEl = document.getElementById('sliderRow');
const hintEl = document.getElementById('hint');

function fitToViewport() {
  // The toolbar/topbar wrap differently at different widths, which changes
  // their height, which changes the budget left for the canvas, which
  // changes the width again -- so settle it over a few passes.
  for (let i = 0; i < 6; i++) {
    const currentWidth = appEl.getBoundingClientRect().width || 780;
    appEl.classList.toggle('compact', currentWidth < 480);

    const appStyle = getComputedStyle(appEl);
    const padV = parseFloat(appStyle.paddingTop) + parseFloat(appStyle.paddingBottom);
    const gap = parseFloat(appStyle.rowGap || appStyle.gap) || 0;
    const frameStyle = getComputedStyle(frameEl);
    const frameBorderV = parseFloat(frameStyle.borderTopWidth) + parseFloat(frameStyle.borderBottomWidth);

    const fixedHeights = topbarEl.offsetHeight + toolbarEl.offsetHeight +
      bottomPanelEl.offsetHeight + sliderRowEl.offsetHeight + hintEl.offsetHeight +
      frameBorderV + padV + gap * 3; // #app has 4 direct children -> 3 gaps

    const availableForCanvas = window.innerHeight - fixedHeights - 6; // small safety margin
    const canvasHeight = Math.max(160, availableForCanvas);
    const widthFromHeight = canvasHeight * (COLS / ROWS);

    const maxWidth = Math.min(window.innerWidth - 20, 1000);
    const finalWidth = Math.max(280, Math.min(widthFromHeight, maxWidth));

    if (Math.abs(finalWidth - appEl.getBoundingClientRect().width) < 0.5) { appEl.style.width = finalWidth + 'px'; break; }
    appEl.style.width = finalWidth + 'px';
  }
}
window.addEventListener('resize', fitToViewport);

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
        // Flowing water: layered waves that scroll along the river's flow
        // direction and blend smoothly (no hard cutoff), so it reads as a
        // moving current instead of a static spotted/dotted pattern.
        const flow = Math.sin(x * 0.18 - t * 2.4) * 0.4
                   + Math.sin(x * 0.45 + y * 0.10 - t * 3.6) * 0.35
                   + Math.sin(y * 0.3 + t * 1.0) * 0.25;
        const m = clamp(flow * 0.5 + 0.5, 0, 1);
        r = lerp(COLORS.water[0], COLORS.waterHi[0], m * 0.55);
        g = lerp(COLORS.water[1], COLORS.waterHi[1], m * 0.55);
        b = lerp(COLORS.water[2], COLORS.waterHi[2], m * 0.55);
      } else if (type === 2) {
        const flick = 0.5 + 0.5 * Math.sin(t * 14 + (x * 7 + y * 13) % 17);
        r = lerp(COLORS.burningHot[0], COLORS.burning[0], flick);
        g = lerp(COLORS.burningHot[1], COLORS.burning[1], flick);
        b = lerp(COLORS.burningHot[2], COLORS.burning[2], flick);
      } else {
        const ember = burntTimer[i] > BURNT_RECOVERY - 8 && texNoise[i] > 0.85;
        if (ember) { r = COLORS.emberGlow[0]; g = COLORS.emberGlow[1]; b = COLORS.emberGlow[2]; }
        else {
          const texVar = (texNoise[i] - 0.5) * 10;
          r = COLORS.burnt[0] + texVar; g = COLORS.burnt[1] + texVar * 0.6; b = COLORS.burnt[2] + texVar * 0.4;
        }
      }
      data[p] = clamp(r, 0, 255);
      data[p + 1] = clamp(g, 0, 255);
      data[p + 2] = clamp(b, 0, 255);
      data[p + 3] = 255;
    }
  }
  tctx.putImageData(terrainImage, 0, 0);
}

const TRAIL_COLORS = { rabbit: '85,187,68', fox: '255,126,0', hawk: '139,95,201' };

function drawTrails(sx, sy) {
  ectx.lineCap = 'round';
  ectx.lineWidth = Math.max(1, Math.min(sx, sy) * 0.16);
  for (const e of entities) {
    if (!trailVisible[e.type] || !e.trail) continue;
    const n = e.trail.length / 2;
    if (n < 2) continue;
    const color = TRAIL_COLORS[e.type];
    for (let i = 0; i < n - 1; i++) {
      const alpha = 0.05 + 0.5 * (i / (n - 1));
      ectx.strokeStyle = `rgba(${color},${alpha.toFixed(2)})`;
      ectx.beginPath();
      ectx.moveTo(e.trail[i * 2] * sx, e.trail[i * 2 + 1] * sy);
      ectx.lineTo(e.trail[(i + 1) * 2] * sx, e.trail[(i + 1) * 2 + 1] * sy);
      ectx.stroke();
    }
  }
}

function renderEntities() {
  const w = entityCanvas.width, h = entityCanvas.height;
  ectx.clearRect(0, 0, w, h);
  const sx = w / COLS, sy = h / ROWS;
  const cellPx = Math.min(sx, sy);
  drawTrails(sx, sy);
  ectx.textAlign = 'center';
  ectx.textBaseline = 'middle';

  for (const e of entities) {
    const cx = e.x * sx, cy = e.y * sy;
    if (e.type === 'hawk') {
      const size = cellPx * 2.6;
      const shadowY = cy + size * 0.3;
      ectx.fillStyle = 'rgba(0,0,0,0.28)';
      ectx.beginPath();
      ectx.ellipse(cx, shadowY, size * 0.32, size * 0.11, 0, 0, Math.PI * 2);
      ectx.fill();
      ectx.fillStyle = '#000';   // reset so the shadow's alpha doesn't bleed into the emoji glyph
      ectx.globalAlpha = 1;
      ectx.font = `${size}px sans-serif`;
      ectx.fillText(EMOJI.hawk, cx, cy);
    } else {
      const size = cellPx * 2.1;
      ectx.fillStyle = '#000';
      ectx.globalAlpha = 1;
      ectx.font = `${size}px sans-serif`;
      ectx.fillText(EMOJI[e.type], cx, cy);
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
  document.querySelectorAll('.toolBtn:not(.trailBtn)').forEach((btn) => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('.toolBtn:not(.trailBtn)').forEach((b) => b.classList.remove('active'));
      btn.classList.add('active');
      currentTool = btn.dataset.tool;
    });
  });

  // Trail toggles are independent, multi-select switches - one species at a
  // time doesn't apply here, so each button just flips its own state.
  document.querySelectorAll('.trailBtn').forEach((btn) => {
    btn.addEventListener('click', () => {
      const species = btn.dataset.trail;
      trailVisible[species] = !trailVisible[species];
      btn.classList.toggle('active', trailVisible[species]);
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
let ecosystemRunning = true;

function frame(now) {
  if (!ecosystemRunning) return; // paused while the fluid sim view is showing

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

window.pauseEcosystem = function () { ecosystemRunning = false; };
window.resumeEcosystem = function () {
  if (ecosystemRunning) return;
  ecosystemRunning = true;
  lastFrameTime = 0;
  requestAnimationFrame(frame);
};

// ---------- INIT -----------------------------------------------------
function init() {
  regenerateWorld();
  fitToViewport();
  resizeEntityCanvas();
  resizeGraph();
  bindUI();
  bindPointer();
  sampleHistory();
  requestAnimationFrame(frame);
}

init();
