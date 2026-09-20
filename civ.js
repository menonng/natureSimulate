'use strict';
/* ============================================================
   문명 시뮬레이터 (Civilization Simulator)
   Same engine pattern as the ecosystem sim (terrain grid + simple
   rule-based agents + tools + graph), re-skinned for people instead of
   animals, with settlements/nations/leaders/religion/ideology layered
   on top. Wrapped in an IIFE so none of its names collide with
   script.js's globals (both load as classic scripts into one page).
   ============================================================ */
(function () {

  // ---------- SEEDED RNG ---------------------------------------------------
  function hashSeed(str) {
    let h = 1779033703 ^ str.length;
    for (let i = 0; i < str.length; i++) {
      h = Math.imul(h ^ str.charCodeAt(i), 3432918353);
      h = (h << 13) | (h >>> 19);
    }
    return function () {
      h = Math.imul(h ^ (h >>> 16), 2246822507);
      h = Math.imul(h ^ (h >>> 13), 3266489909);
      h ^= h >>> 16;
      return h >>> 0;
    };
  }
  function mulberry32(a) {
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  let rng = Math.random;
  function makeRng(seedStr) {
    const h = hashSeed(String(seedStr));
    return mulberry32(h());
  }
  function rrand(a, b) { return a + rng() * (b - a); }
  function rrandInt(a, b) { return Math.floor(rrand(a, b + 1)); }
  function pick(arr) { return arr[Math.floor(rng() * arr.length)]; }

  // ---------- CONFIG ---------------------------------------------------
  const COLS = 200, ROWS = 150;
  const TICK_DT = 1 / 20;
  const MAX_TICKS_PER_FRAME = 40;

  // cell types
  const T_OCEAN = 0, T_COAST = 1, T_PLAINS = 2, T_HILLS = 3, T_MOUNTAIN = 4, T_SNOW = 5;

  const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
  const lerp = (a, b, t) => a + (b - a) * t;
  const idx = (x, y) => y * COLS + x;
  const inBounds = (x, y) => x >= 0 && x < COLS && y >= 0 && y < ROWS;

  // ---------- STATE ---------------------------------------------------
  let elevation = new Float32Array(COLS * ROWS);
  let cellType = new Uint8Array(COLS * ROWS);
  let isRiver = new Uint8Array(COLS * ROWS);
  let resource = new Float32Array(COLS * ROWS);
  let texNoise = new Float32Array(COLS * ROWS);
  // -1 = unclaimed; otherwise a nation id. One entry per land cell, giving
  // territory hard, pixel-square borders (no smoothing) at the grid's own
  // resolution, recomputed as a per-cell nearest-settlement claim.
  let territory = new Int32Array(COLS * ROWS).fill(-1);
  let territoryAccum = 0;
  const TERRITORY_INTERVAL = 2.5; // simulated seconds between automatic recomputes

  let people = [];      // free-roaming, not yet settled
  let settlements = [];
  let nations = [];
  let nextId = 1;
  let nextNationHue = 0;

  const params = { resourceRegrow: 0.006, growthRate: 0.35, brushSize: 5 };
  let currentTool = 'ocean';
  let speedMultiplier = 1;
  let simTime = 0;
  let lastFrameTime = 0;
  let accumulator = 0;
  let currentSeed = '';

  const history = [];
  const HISTORY_MAX = 600;
  let sampleAccum = 0;
  const SAMPLE_INTERVAL = 1.5;

  // ---------- NAME GENERATION -------------------------------------------
  const SYL_A = ['아', '카', '무', '시', '바', '노', '겔', '루', '단', '오', '테', '란', '조', '페', '힌'];
  const SYL_B = ['란', '도', '리아', '벤', '가르', '문', '자르', '엔', '실', '토', '나', '문드', '샤', '린'];
  function genName(minS, maxS) {
    const n = rrandInt(minS, maxS);
    let s = '';
    for (let i = 0; i < n; i++) s += i === 0 ? pick(SYL_A) : pick(SYL_B);
    return s;
  }
  function genNationName() { return genName(2, 3) + pick(['국', '제국', '연맹', '왕국', '공화국']); }
  function genPersonName() { return genName(2, 3); }
  function genReligionName() { return genName(2, 2) + pick(['교', '신앙', '도']); }
  function genFamilyName() { return genName(1, 2) + '가'; }

  const IDEOLOGIES = ['군주제', '신정', '공화정', '전체주의', '부족연합'];
  const LEADER_TITLE = { 군주제: '왕', 신정: '대사제', 공화정: '대통령', 전체주의: '총통', 부족연합: '족장' };
  const REGIONAL_TITLE = { 군주제: '영주', 신정: '사제', 공화정: '시장', 전체주의: '지구서기', 부족연합: '촌장' };
  const CIV_TIER_NAME = ['', '석기시대', '청동기시대', '고대', '중세', '근대'];

  // Leader flavor, kept separate from the nation's formal government system
  // (ideology): a personal temperament and a personal philosophical leaning,
  // randomly assigned to each leader. Used as flavor now, and as prompt
  // conditioning for the leader-speech LLM later.
  const PERSONALITIES = ['호전적', '경건한', '실용적', '고립주의적', '팽창주의적', '자비로운', '전제적', '이상주의적', '음모적', '검소한'];
  const PHILOSOPHIES = ['자유', '질서', '전통', '혁신', '명예', '부', '신앙', '정복', '평등', '혈통'];
  function genLeader(dynasty) {
    return {
      name: genPersonName(),
      dynasty,
      personality: pick(PERSONALITIES),
      philosophy: pick(PHILOSOPHIES),
      termStart: simTime,
      termLength: rrand(90, 240), // simulated seconds before succession
    };
  }

  const NATION_HUES = [355, 25, 48, 100, 175, 210, 265, 320, 15, 130, 195, 285];
  function hslToRgb(h, s, l) {
    s /= 100; l /= 100;
    const k = (n) => (n + h / 30) % 12;
    const a = s * Math.min(l, 1 - l);
    const f = (n) => l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1)));
    return [Math.round(f(0) * 255), Math.round(f(8) * 255), Math.round(f(4) * 255)];
  }
  function nextNationColor() {
    const hue = NATION_HUES[nextNationHue % NATION_HUES.length];
    nextNationHue++;
    return { css: `hsl(${hue}, 62%, 58%)`, rgb: hslToRgb(hue, 62, 58) };
  }

  // ---------- RACES ------------------------------------------------------
  // Two playable peoples, one per source sprite character. Purely a visual +
  // demographic trait (sprite art, name, territory/nation-list bookkeeping) --
  // it does not affect individual AI behavior.
  const RACES = [
    { id: 0, name: '묘인족', frameSrc: ['assets/sprites/race0_walk0.png', 'assets/sprites/race0_walk1.png'] },
    { id: 1, name: '인간족', frameSrc: ['assets/sprites/race1_walk0.png', 'assets/sprites/race1_walk1.png'] },
  ];
  for (const race of RACES) {
    race.images = race.frameSrc.map((src) => {
      const img = new Image();
      img.src = src;
      return img;
    });
  }
  function randomRace() { return rng() < 0.5 ? 0 : 1; }
  function pickRaceFromComposition(comp) {
    if (!comp) return randomRace();
    let total = 0;
    for (const c of comp) total += c;
    if (total <= 0) return randomRace();
    let r = rng() * total;
    for (let i = 0; i < comp.length; i++) {
      r -= comp[i];
      if (r <= 0) return i;
    }
    return comp.length - 1;
  }

  // ---------- TERRAIN GENERATION -------------------------------------------

  // Value noise: random values on a coarse control-point grid, smoothly
  // interpolated up to full resolution. Summing a few octaves of this (each
  // one spanning the full 0..1 range at its own scale) gives real hills and
  // continents; a box-blur of per-pixel i.i.d. noise (the earlier approach)
  // crushes the variance almost to nothing and produces a flat, blobless mess.
  function valueNoiseLayer(w, h, cellsX, cellsY) {
    const gw = cellsX + 1, gh = cellsY + 1;
    const grid = new Float32Array(gw * gh);
    for (let i = 0; i < grid.length; i++) grid[i] = rng();
    const out = new Float32Array(w * h);
    for (let y = 0; y < h; y++) {
      const gy = (y / h) * cellsY;
      const gy0 = Math.floor(gy), gy1 = Math.min(gy0 + 1, cellsY);
      const ty = gy - gy0;
      const sy = ty * ty * (3 - 2 * ty);
      for (let x = 0; x < w; x++) {
        const gx = (x / w) * cellsX;
        const gx0 = Math.floor(gx), gx1 = Math.min(gx0 + 1, cellsX);
        const tx = gx - gx0;
        const sx = tx * tx * (3 - 2 * tx);
        const v00 = grid[gy0 * gw + gx0], v10 = grid[gy0 * gw + gx1];
        const v01 = grid[gy1 * gw + gx0], v11 = grid[gy1 * gw + gx1];
        const top = v00 + (v10 - v00) * sx;
        const bot = v01 + (v11 - v01) * sx;
        out[y * w + x] = top + (bot - top) * sy;
      }
    }
    return out;
  }

  function generateElevation() {
    const continents = valueNoiseLayer(COLS, ROWS, 7, 5);
    const regions = valueNoiseLayer(COLS, ROWS, 20, 15);
    const detail = valueNoiseLayer(COLS, ROWS, 55, 42);
    const out = new Float32Array(COLS * ROWS);
    for (let i = 0; i < out.length; i++) {
      let v = continents[i] * 0.55 + regions[i] * 0.3 + detail[i] * 0.15;
      v = clamp((v - 0.5) * 1.5 + 0.5, 0, 1); // mild contrast stretch
      out[i] = v;
    }
    return out;
  }

  const T_OCEAN_E = 0.40, T_COAST_E = 0.455, T_PLAINS_E = 0.68, T_HILLS_E = 0.82, T_MOUNTAIN_E = 0.93;
  function classify(e) {
    if (e < T_OCEAN_E) return T_OCEAN;
    if (e < T_COAST_E) return T_COAST;
    if (e < T_PLAINS_E) return T_PLAINS;
    if (e < T_HILLS_E) return T_HILLS;
    if (e < T_MOUNTAIN_E) return T_MOUNTAIN;
    return T_SNOW;
  }

  function carveRivers() {
    const count = rrandInt(10, 18);
    for (let i = 0; i < count; i++) {
      let sx = 0, sy = 0, tries = 0;
      do { sx = rrandInt(0, COLS - 1); sy = rrandInt(0, ROWS - 1); tries++; }
      while (elevation[idx(sx, sy)] < T_HILLS_E && tries < 300);
      if (tries >= 300) continue;
      let x = sx, y = sy;
      for (let step = 0; step < 500; step++) {
        isRiver[idx(x, y)] = 1;
        const e = elevation[idx(x, y)];
        if (e < T_COAST_E) break;
        let bestE = e, bx = x, by = y;
        for (let dy = -1; dy <= 1; dy++) {
          for (let dx = -1; dx <= 1; dx++) {
            if (!dx && !dy) continue;
            const nx = x + dx, ny = y + dy;
            if (!inBounds(nx, ny)) continue;
            const ne = elevation[idx(nx, ny)];
            if (ne < bestE) { bestE = ne; bx = nx; by = ny; }
          }
        }
        if (bx === x && by === y) break;
        x = bx; y = by;
      }
    }
  }

  function generateWorld(seedStr) {
    currentSeed = seedStr;
    rng = makeRng(seedStr);
    elevation = generateElevation();
    cellType = new Uint8Array(COLS * ROWS);
    isRiver = new Uint8Array(COLS * ROWS);
    resource = new Float32Array(COLS * ROWS);
    texNoise = new Float32Array(COLS * ROWS);
    for (let i = 0; i < cellType.length; i++) {
      cellType[i] = classify(elevation[i]);
      texNoise[i] = rng();
      if (cellType[i] === T_PLAINS) resource[i] = rrand(0.3, 0.85);
      else if (cellType[i] === T_COAST) resource[i] = rrand(0.2, 0.55);
      else if (cellType[i] === T_HILLS) resource[i] = rrand(0.15, 0.45);
    }
    carveRivers();

    people = [];
    settlements = [];
    nations = [];
    nextId = 1;
    nextNationHue = 0;
    history.length = 0;
    simTime = 0;
    territory = new Int32Array(COLS * ROWS).fill(-1);
    territoryAccum = 0;

    // scatter starting population on livable land, away from ocean/mountain
    let placed = 0, guard = 0;
    while (placed < 140 && guard < 8000) {
      guard++;
      const x = rrandInt(0, COLS - 1), y = rrandInt(0, ROWS - 1);
      const t = cellType[idx(x, y)];
      if (t !== T_PLAINS && t !== T_COAST) continue;
      addPerson(x + 0.5, y + 0.5, randomRace());
      placed++;
    }
  }

  function addPerson(x, y, race) {
    people.push({
      id: nextId++, x, y, race: race === undefined ? randomRace() : race,
      vx: rrand(-1, 1), vy: rrand(-1, 1),
      energy: rrand(4, 7), age: 0, cooldown: rrand(0, 6),
    });
  }

  // ---------- SPATIAL BUCKETS (for settlement founding density checks) ----
  const BUCKET_SIZE = 6;
  function bucketsFor(list) {
    const m = new Map();
    for (let k = 0; k < list.length; k++) {
      const p = list[k];
      const key = Math.floor(p.x / BUCKET_SIZE) + ',' + Math.floor(p.y / BUCKET_SIZE);
      let arr = m.get(key);
      if (!arr) { arr = []; m.set(key, arr); }
      arr.push(k);
    }
    return m;
  }
  function countNear(buckets, list, x, y, radius) {
    const br = Math.ceil(radius / BUCKET_SIZE);
    const bx0 = Math.floor(x / BUCKET_SIZE), by0 = Math.floor(y / BUCKET_SIZE);
    let n = 0;
    for (let by = by0 - br; by <= by0 + br; by++) {
      for (let bx = bx0 - br; bx <= bx0 + br; bx++) {
        const arr = buckets.get(bx + ',' + by);
        if (!arr) continue;
        for (const k of arr) {
          const p = list[k];
          if (Math.hypot(p.x - x, p.y - y) <= radius) n++;
        }
      }
    }
    return n;
  }

  // ---------- NATIONS -------------------------------------------------
  const NATION_JOIN_RADIUS = 34;
  function foundNation(x, y) {
    const ideology = pick(IDEOLOGIES);
    const dynasty = genFamilyName();
    const colorInfo = nextNationColor();
    const nation = {
      id: nextId++,
      name: genNationName(),
      color: colorInfo.css,
      rgb: colorInfo.rgb,
      ideology,
      dynasty,
      leader: genLeader(dynasty),
      religion: genReligionName(),
      faith: rrand(0.05, 0.15),
      age: 0,
      settlementIds: [],
      civLevel: 1,
      totalPopulation: 0,
      raceTotals: new Array(RACES.length).fill(0),
    };
    nations.push(nation);
    return nation;
  }
  function nearestNation(x, y) {
    let best = null, bestD = NATION_JOIN_RADIUS;
    for (const nation of nations) {
      for (const sid of nation.settlementIds) {
        const s = settlements.find((s) => s.id === sid);
        if (!s) continue;
        const d = Math.hypot(s.x - x, s.y - y);
        if (d < bestD) { bestD = d; best = nation; }
      }
    }
    return best;
  }

  // ---------- TERRITORY ---------------------------------------------------
  // Each settlement claims land within a reach that grows with its
  // population (capitals get a bonus); every land cell is assigned to
  // whichever settlement's claim scores highest there, and inherits that
  // settlement's nation. Ocean is never claimed.
  function recomputeTerritory() {
    territory.fill(-1);
    if (!settlements.length) return;
    for (let y = 0; y < ROWS; y++) {
      for (let x = 0; x < COLS; x++) {
        const i = idx(x, y);
        if (cellType[i] === T_OCEAN) continue;
        const cx = x + 0.5, cy = y + 0.5;
        let bestNationId = -1, bestScore = -Infinity;
        for (const s of settlements) {
          const reach = 10 + Math.sqrt(s.population) * 1.6 + (s.isCapital ? 8 : 0);
          const d = Math.hypot(s.x - cx, s.y - cy);
          if (d > reach) continue;
          const score = reach - d;
          if (score > bestScore) { bestScore = score; bestNationId = s.nationId; }
        }
        territory[i] = bestNationId;
      }
    }
  }

  // ---------- SETTLEMENTS -----------------------------------------------
  const SETTLE_DENSITY = 5;
  const SETTLE_RADIUS = 3;
  const SETTLE_MIN_GAP = 16;
  const CITY_POP = 150;

  function trySettleFrom(buckets) {
    for (let k = 0; k < people.length; k++) {
      const p = people[k];
      const t = cellType[idx(Math.floor(p.x), Math.floor(p.y))];
      if (t !== T_PLAINS && t !== T_COAST && t !== T_HILLS) continue;
      const density = countNear(buckets, people, p.x, p.y, SETTLE_RADIUS);
      if (density < SETTLE_DENSITY) continue;
      let tooClose = false;
      for (const s of settlements) {
        if (Math.hypot(s.x - p.x, s.y - p.y) < SETTLE_MIN_GAP) { tooClose = true; break; }
      }
      if (tooClose) continue;

      // found it: absorb nearby free people into the new settlement's population
      let absorbed = 0;
      const raceCounts = new Array(RACES.length).fill(0);
      const remaining = [];
      for (const person of people) {
        if (Math.hypot(person.x - p.x, person.y - p.y) <= SETTLE_RADIUS && absorbed < 12) {
          absorbed++;
          raceCounts[person.race]++;
        } else remaining.push(person);
      }
      people = remaining;
      if (absorbed === 0) raceCounts[p.race]++;

      let nation = nearestNation(p.x, p.y);
      let isCapital = false;
      if (!nation) { nation = foundNation(p.x, p.y); isCapital = true; }

      const population = Math.max(6, absorbed);
      const raceSum = raceCounts.reduce((a, b) => a + b, 0) || 1;
      const settlement = {
        id: nextId++, x: p.x, y: p.y,
        name: genPersonName() + pick(['성', '촌', '항', '진']),
        nationId: nation.id,
        population,
        raceComposition: raceCounts.map((c) => (c / raceSum) * population),
        isCity: false, isCapital,
        leaderTitle: isCapital ? LEADER_TITLE[nation.ideology] : REGIONAL_TITLE[nation.ideology],
        leaderName: isCapital ? nation.leader.name : genPersonName(),
        founded: simTime,
      };
      settlements.push(settlement);
      nation.settlementIds.push(settlement.id);
      return true; // one new settlement per tick is plenty
    }
    return false;
  }

  function tickSettlements(dt) {
    for (const s of settlements) {
      const cx = Math.floor(s.x), cy = Math.floor(s.y);
      let avgRes = 0, n = 0;
      for (let dy = -2; dy <= 2; dy++) {
        for (let dx = -2; dx <= 2; dx++) {
          const x = cx + dx, y = cy + dy;
          if (!inBounds(x, y)) continue;
          const t = cellType[idx(x, y)];
          if (t === T_PLAINS || t === T_COAST || t === T_HILLS) { avgRes += resource[idx(x, y)]; n++; }
        }
      }
      avgRes = n ? avgRes / n : 0.1;

      const growth = (avgRes - 0.32) * params.growthRate * 0.02; // nerfed relative to ecosystem breeding rates
      const growthFactor = Math.max(0, 1 + growth * dt);
      s.population = Math.max(0, s.population * growthFactor);
      if (s.raceComposition) {
        for (let ri = 0; ri < s.raceComposition.length; ri++) s.raceComposition[ri] *= growthFactor;
      }
      // settlements consume a little local resource as they grow
      for (let dy = -2; dy <= 2; dy++) {
        for (let dx = -2; dx <= 2; dx++) {
          const x = cx + dx, y = cy + dy;
          if (!inBounds(x, y)) continue;
          const i = idx(x, y);
          const t = cellType[i];
          if (t === T_PLAINS || t === T_COAST || t === T_HILLS) {
            resource[i] = clamp(resource[i] - s.population * 0.000006 * dt, 0, 1);
          }
        }
      }
      if (!s.isCity && s.population >= CITY_POP) s.isCity = true;

      // rare emigration: a small group breaks off to found a settlement elsewhere
      if (s.population > 40 && rng() < 0.00025 * dt * 20) {
        const ang = rrand(0, Math.PI * 2);
        const dist = rrand(6, 16);
        const nx = clamp(s.x + Math.cos(ang) * dist, 1, COLS - 2);
        const ny = clamp(s.y + Math.sin(ang) * dist, 1, ROWS - 2);
        if (cellType[idx(Math.floor(nx), Math.floor(ny))] !== T_OCEAN) {
          for (let i = 0; i < 4; i++) {
            addPerson(nx + rrand(-1, 1), ny + rrand(-1, 1), pickRaceFromComposition(s.raceComposition));
          }
          const oldPop = s.population;
          s.population = Math.max(4, s.population - 4);
          if (s.raceComposition && oldPop > 0) {
            const ratio = s.population / oldPop;
            for (let ri = 0; ri < s.raceComposition.length; ri++) s.raceComposition[ri] *= ratio;
          }
        }
      }
    }
    // starved settlements slowly disappear
    settlements = settlements.filter((s) => {
      if (s.population > 1) return true;
      const nation = nations.find((n) => n.id === s.nationId);
      if (nation) nation.settlementIds = nation.settlementIds.filter((id) => id !== s.id);
      return false;
    });
  }

  function tickNations(dt) {
    for (const nation of nations) {
      nation.age += dt;
      let pop = 0;
      const raceTotals = new Array(RACES.length).fill(0);
      for (const sid of nation.settlementIds) {
        const s = settlements.find((s) => s.id === sid);
        if (s) {
          pop += s.population;
          if (s.raceComposition) {
            for (let ri = 0; ri < RACES.length; ri++) raceTotals[ri] += s.raceComposition[ri] || 0;
          }
        }
      }
      nation.totalPopulation = pop;
      nation.raceTotals = raceTotals;
      nation.civLevel = clamp(1 + Math.floor(pop / 180) + Math.floor(nation.age / 260) + Math.floor(nation.settlementIds.length / 3), 1, 5);
      nation.faith = clamp(nation.faith + 0.0004 * dt * (1 + nation.civLevel * 0.2), 0, 1);

      // Leader succession: usually stays within the ruling family (a new
      // name, same dynasty); rarely a rival family seizes power instead,
      // which can also shift the nation's ideology.
      if (simTime - nation.leader.termStart > nation.leader.termLength) {
        const revolution = rng() < 0.12;
        const dynasty = revolution ? genFamilyName() : nation.leader.dynasty;
        if (revolution) {
          nation.dynasty = dynasty;
          nation.ideology = pick(IDEOLOGIES);
        }
        nation.leader = genLeader(dynasty);
      }
    }
    nations = nations.filter((n) => n.settlementIds.length > 0);
  }

  // ---------- PEOPLE (free-roaming) ---------------------------------------
  function cellAt(x, y) { return idx(clamp(Math.floor(x), 0, COLS - 1), clamp(Math.floor(y), 0, ROWS - 1)); }

  function tryMovePerson(p, dt) {
    const nx = p.x + p.vx * dt, ny = p.y + p.vy * dt;
    if (nx < 0 || nx >= COLS || ny < 0 || ny >= ROWS) { p.vx *= -1; p.vy *= -1; return; }
    const t = cellType[cellAt(nx, ny)];
    if (t === T_OCEAN) { p.vx *= -1; p.vy *= -1; return; }
    p.x = nx; p.y = ny;
  }

  function updatePerson(p, dt) {
    p.energy -= 0.32 * dt;
    p.age += dt;
    p.cooldown = Math.max(0, p.cooldown - dt);
    const i = cellAt(p.x, p.y);
    const t = cellType[i];

    if (t === T_PLAINS || t === T_COAST || t === T_HILLS) {
      if (resource[i] > 0.04) {
        const eat = Math.min(resource[i], 0.28 * dt);
        resource[i] -= eat;
        p.energy += eat * 3.0;
      }
    }

    // seek nearby resource-rich land, gentle wander otherwise
    let bestScore = -1, bestX = p.x, bestY = p.y;
    for (let s = 0; s < 4; s++) {
      const sx = clamp(p.x + rrand(-4, 4), 0, COLS - 1);
      const sy = clamp(p.y + rrand(-4, 4), 0, ROWS - 1);
      const si = cellAt(sx, sy);
      const st = cellType[si];
      if (st === T_OCEAN) continue;
      const score = (st === T_PLAINS || st === T_COAST ? resource[si] : 0.05) + rng() * 0.1;
      if (score > bestScore) { bestScore = score; bestX = sx; bestY = sy; }
    }
    const dx = bestX - p.x, dy = bestY - p.y;
    const len = Math.hypot(dx, dy) || 1;
    p.vx = lerp(p.vx, (dx / len) * 1.1, 0.35);
    p.vy = lerp(p.vy, (dy / len) * 1.1, 0.35);
    tryMovePerson(p, dt);

    // reproduction, heavily nerfed vs the ecosystem sim's animals
    if (p.energy > 9 && p.cooldown <= 0) {
      p.energy -= 6;
      p.cooldown = 30;
      addPerson(clamp(p.x + rrand(-1, 1), 0, COLS - 1), clamp(p.y + rrand(-1, 1), 0, ROWS - 1), p.race);
    }
    return p.energy > 0;
  }

  function tickPeople(dt) {
    const next = [];
    for (const p of people) if (updatePerson(p, dt)) next.push(p);
    people = next;

    const buckets = bucketsFor(people);
    trySettleFrom(buckets);
  }

  // ---------- MAIN TICK -----------------------------------------------
  function tickTerrain(dt) {
    for (let i = 0; i < cellType.length; i++) {
      if ((cellType[i] === T_PLAINS || cellType[i] === T_COAST || cellType[i] === T_HILLS) && resource[i] < 1) {
        resource[i] = clamp(resource[i] + params.resourceRegrow * dt, 0, 1);
      }
    }
  }

  function tick() {
    tickTerrain(TICK_DT);
    tickPeople(TICK_DT);
    tickSettlements(TICK_DT);
    tickNations(TICK_DT);
    simTime += TICK_DT;

    territoryAccum += TICK_DT;
    if (territoryAccum >= TERRITORY_INTERVAL) {
      territoryAccum = 0;
      recomputeTerritory();
    }

    sampleAccum += TICK_DT;
    if (sampleAccum >= SAMPLE_INTERVAL) {
      sampleAccum = 0;
      sampleHistory();
    }
  }

  function sampleHistory() {
    let totalPop = people.length;
    for (const s of settlements) totalPop += s.population;
    const avgCiv = nations.length ? nations.reduce((a, n) => a + n.civLevel, 0) / nations.length : 0;
    history.push({ pop: totalPop, settlements: settlements.length, nations: nations.length, civ: avgCiv });
    if (history.length > HISTORY_MAX) history.shift();
    updateCounts(totalPop, settlements.length, nations.length);
    updateNationList();
  }

  // ---------- RENDERING -----------------------------------------------
  const terrainCanvas = document.getElementById('civTerrainCanvas');
  const tctx = terrainCanvas.getContext('2d', { alpha: false });
  const entityCanvas = document.getElementById('civEntityCanvas');
  const ectx = entityCanvas.getContext('2d');
  const canvasWrap = document.getElementById('civCanvasWrap');

  terrainCanvas.width = COLS;
  terrainCanvas.height = ROWS;
  const terrainImage = tctx.createImageData(COLS, ROWS);

  const COL = {
    oceanDeep: [8, 26, 56], oceanShallow: [22, 60, 110], coast: [196, 178, 118],
    plainsLow: [58, 92, 40], plainsHigh: [104, 158, 64],
    hills: [107, 96, 58], mountain: [110, 105, 100], snow: [232, 236, 240],
    river: [46, 110, 190],
  };

  function renderTerrain() {
    const data = terrainImage.data;
    const nationRgbById = new Map();
    for (const n of nations) nationRgbById.set(n.id, n.rgb);
    const TERRITORY_TINT = 0.32;
    for (let i = 0; i < cellType.length; i++) {
      const p = i * 4;
      const t = cellType[i];
      const e = elevation[i];
      const tex = (texNoise[i] - 0.5) * 14;
      let r, g, b;
      if (isRiver[i] && t !== T_OCEAN) {
        r = COL.river[0]; g = COL.river[1]; b = COL.river[2];
      } else if (t === T_OCEAN) {
        const m = clamp((e / T_OCEAN_E), 0, 1);
        r = lerp(COL.oceanDeep[0], COL.oceanShallow[0], m);
        g = lerp(COL.oceanDeep[1], COL.oceanShallow[1], m);
        b = lerp(COL.oceanDeep[2], COL.oceanShallow[2], m);
      } else if (t === T_COAST) {
        r = COL.coast[0] + tex; g = COL.coast[1] + tex; b = COL.coast[2] + tex * 0.5;
      } else if (t === T_PLAINS) {
        const m = clamp(resource[i], 0, 1);
        r = lerp(COL.plainsLow[0], COL.plainsHigh[0], m) + tex;
        g = lerp(COL.plainsLow[1], COL.plainsHigh[1], m) + tex;
        b = lerp(COL.plainsLow[2], COL.plainsHigh[2], m) + tex * 0.4;
      } else if (t === T_HILLS) {
        r = COL.hills[0] + tex; g = COL.hills[1] + tex; b = COL.hills[2] + tex * 0.5;
      } else if (t === T_MOUNTAIN) {
        r = COL.mountain[0] + tex; g = COL.mountain[1] + tex; b = COL.mountain[2] + tex;
      } else {
        r = COL.snow[0]; g = COL.snow[1]; b = COL.snow[2];
      }
      if (territory[i] >= 0) {
        const nrgb = nationRgbById.get(territory[i]);
        if (nrgb) {
          r = r + (nrgb[0] - r) * TERRITORY_TINT;
          g = g + (nrgb[1] - g) * TERRITORY_TINT;
          b = b + (nrgb[2] - b) * TERRITORY_TINT;
        }
      }
      data[p] = clamp(r, 0, 255);
      data[p + 1] = clamp(g, 0, 255);
      data[p + 2] = clamp(b, 0, 255);
      data[p + 3] = 255;
    }
    tctx.putImageData(terrainImage, 0, 0);
  }

  function renderEntities() {
    const w = entityCanvas.width, h = entityCanvas.height;
    ectx.clearRect(0, 0, w, h);
    const sx = w / COLS, sy = h / ROWS;
    const cellPx = Math.min(sx, sy);

    const WALK_FPS = 3.2; // walk-cycle frame swaps per second
    const spriteH = clamp(cellPx * 4.5, 8, 34);
    ectx.fillStyle = '#f1e9d8';
    for (const p of people) {
      const race = RACES[p.race] || RACES[0];
      const frameIdx = Math.floor((simTime + p.id * 0.53) * WALK_FPS) % 2;
      const img = race.images[frameIdx];
      const px = p.x * sx, py = p.y * sy;
      if (img && img.complete && img.naturalWidth) {
        const w = spriteH * (img.naturalWidth / img.naturalHeight);
        ectx.save();
        ectx.translate(px, py);
        if (p.vx > 0.02) ectx.scale(-1, 1); // sprites face left by default
        ectx.drawImage(img, -w / 2, -spriteH, w, spriteH);
        ectx.restore();
      } else {
        // fallback dot while the sprite images are still loading
        ectx.beginPath();
        ectx.arc(px, py, Math.max(1, cellPx * 0.5), 0, Math.PI * 2);
        ectx.fill();
      }
    }

    for (const s of settlements) {
      const nation = nations.find((n) => n.id === s.nationId);
      const cx = s.x * sx, cy = s.y * sy;
      const r = Math.max(2.5, cellPx * (s.isCity ? 2.2 : 1.4));
      ectx.fillStyle = nation ? nation.color : '#999';
      ectx.beginPath();
      ectx.arc(cx, cy, r, 0, Math.PI * 2);
      ectx.fill();
      ectx.strokeStyle = 'rgba(0,0,0,0.45)';
      ectx.lineWidth = 1;
      ectx.stroke();
      if (s.isCapital) {
        ectx.fillStyle = '#FFCC11';
        ectx.beginPath();
        ectx.arc(cx, cy - r - 3, 1.6, 0, Math.PI * 2);
        ectx.fill();
      }
    }
  }

  // ---------- GRAPH -----------------------------------------------
  const graphCanvas = document.getElementById('civGraphCanvas');
  const gctx = graphCanvas.getContext('2d');

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
    drawSeries(history.map((s) => s.pop), '#55BB44', w, h, pad);
    drawSeries(history.map((s) => s.settlements * 20), '#FF7E00', w, h, pad);
    drawSeries(history.map((s) => s.nations * 40), '#39C5BB', w, h, pad);
  }

  function updateCounts(pop, settlementCount, nationCount) {
    document.getElementById('civCntPeople').textContent = `🧍 ${Math.round(pop)}`;
    document.getElementById('civCntSettlements').textContent = `🏘️ ${settlementCount}`;
    document.getElementById('civCntNations').textContent = `🏳️ ${nationCount}`;
  }

  function updateNationList() {
    const list = document.getElementById('civNationList');
    if (!nations.length) {
      list.innerHTML = '<li class="civNationEmpty">아직 형성된 국가가 없습니다.</li>';
      return;
    }
    const sorted = [...nations].sort((a, b) => b.totalPopulation - a.totalPopulation);
    list.innerHTML = sorted.slice(0, 12).map((n) => {
      const tier = CIV_TIER_NAME[n.civLevel] || '';
      const L = n.leader;
      const raceTotals = n.raceTotals || [];
      let domIdx = 0, raceSum = 0;
      for (let ri = 0; ri < raceTotals.length; ri++) {
        raceSum += raceTotals[ri];
        if (raceTotals[ri] > (raceTotals[domIdx] || 0)) domIdx = ri;
      }
      const domRacePct = raceSum > 0 ? Math.round((raceTotals[domIdx] / raceSum) * 100) : 0;
      const domRaceName = RACES[domIdx] ? RACES[domIdx].name : '';
      return `<li><span class="civSwatch" style="background:${n.color}"></span>` +
        `<span><b>${n.name}</b> (${n.dynasty}) · ${LEADER_TITLE[n.ideology]} ${L.name} · ${n.ideology} · ${n.religion}(${Math.round(n.faith * 100)}%)` +
        `<br><span class="civMeta">${L.personality}·${L.philosophy}주의 지도자 · Lv.${n.civLevel} ${tier} · 인구 ${Math.round(n.totalPopulation)} · 정착지 ${n.settlementIds.length}` +
        (raceSum > 0 ? ` · 다수종족 ${domRaceName} ${domRacePct}%` : '') +
        `</span></span></li>`;
    }).join('');
  }

  // ---------- VIEWPORT SIZING ----------------------------------------------
  function resizeEntityCanvas() {
    const rect = canvasWrap.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    entityCanvas.width = Math.max(1, Math.round(rect.width * dpr));
    entityCanvas.height = Math.max(1, Math.round(rect.height * dpr));
  }
  function resizeGraph() {
    const rect = graphCanvas.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    graphCanvas.width = Math.max(1, Math.round(rect.width * dpr));
    graphCanvas.height = Math.max(1, Math.round(rect.height * dpr));
  }
  window.addEventListener('resize', () => { resizeEntityCanvas(); resizeGraph(); });

  // ---------- INPUT / TOOLS -----------------------------------------------
  let pointerDown = false;
  function clientToGrid(clientX, clientY) {
    const rect = entityCanvas.getBoundingClientRect();
    return [((clientX - rect.left) / rect.width) * COLS, ((clientY - rect.top) / rect.height) * ROWS];
  }
  function applyTool(gx, gy) {
    if (currentTool === 'person') {
      addPerson(clamp(gx, 0, COLS - 1), clamp(gy, 0, ROWS - 1));
      return;
    }
    if (currentTool === 'settle') {
      const x = clamp(Math.floor(gx), 1, COLS - 2), y = clamp(Math.floor(gy), 1, ROWS - 2);
      if (cellType[idx(x, y)] === T_OCEAN) return;
      let nation = nearestNation(x, y);
      let isCapital = false;
      if (!nation) { nation = foundNation(x, y); isCapital = true; }
      const settlement = {
        id: nextId++, x: x + 0.5, y: y + 0.5,
        name: genPersonName() + pick(['성', '촌', '항', '진']),
        nationId: nation.id, population: 10,
        raceComposition: [5, 5],
        isCity: false, isCapital,
        leaderTitle: isCapital ? LEADER_TITLE[nation.ideology] : REGIONAL_TITLE[nation.ideology],
        leaderName: isCapital ? nation.leader.name : genPersonName(),
        founded: simTime,
      };
      settlements.push(settlement);
      nation.settlementIds.push(settlement.id);
      recomputeTerritory();
      return;
    }
    if (currentTool === 'erase') {
      const radius = params.brushSize;
      people = people.filter((p) => Math.hypot(p.x - gx, p.y - gy) > radius);
      settlements = settlements.filter((s) => {
        if (Math.hypot(s.x - gx, s.y - gy) > radius) return true;
        const nation = nations.find((n) => n.id === s.nationId);
        if (nation) nation.settlementIds = nation.settlementIds.filter((id) => id !== s.id);
        return false;
      });
      recomputeTerritory();
      return;
    }
    // terrain paint tools
    const radius = params.brushSize;
    const x0 = Math.max(0, Math.floor(gx - radius)), x1 = Math.min(COLS - 1, Math.ceil(gx + radius));
    const y0 = Math.max(0, Math.floor(gy - radius)), y1 = Math.min(ROWS - 1, Math.ceil(gy + radius));
    for (let y = y0; y <= y1; y++) {
      for (let x = x0; x <= x1; x++) {
        if (Math.hypot(x - gx, y - gy) > radius) continue;
        const i = idx(x, y);
        if (currentTool === 'ocean') { cellType[i] = T_OCEAN; isRiver[i] = 0; resource[i] = 0; }
        else if (currentTool === 'plains') { cellType[i] = T_PLAINS; resource[i] = 0.6; isRiver[i] = 0; }
        else if (currentTool === 'mountain') { cellType[i] = T_MOUNTAIN; resource[i] = 0; isRiver[i] = 0; }
      }
    }
  }
  function bindPointer() {
    entityCanvas.addEventListener('pointerdown', (ev) => {
      pointerDown = true;
      entityCanvas.setPointerCapture(ev.pointerId);
      const [gx, gy] = clientToGrid(ev.clientX, ev.clientY);
      applyTool(gx, gy);
    });
    entityCanvas.addEventListener('pointermove', (ev) => {
      if (!pointerDown) return;
      if (currentTool === 'person' || currentTool === 'settle') return; // one at a time
      const [gx, gy] = clientToGrid(ev.clientX, ev.clientY);
      applyTool(gx, gy);
    });
    window.addEventListener('pointerup', () => { pointerDown = false; });
    window.addEventListener('pointercancel', () => { pointerDown = false; });
  }

  function randomSeedString() {
    return Math.random().toString(36).slice(2, 8);
  }

  function bindUI() {
    document.querySelectorAll('.civToolBtn').forEach((btn) => {
      btn.addEventListener('click', () => {
        document.querySelectorAll('.civToolBtn').forEach((b) => b.classList.remove('active'));
        btn.classList.add('active');
        currentTool = btn.dataset.civtool;
      });
    });
    document.querySelectorAll('.civSpeedBtn').forEach((btn) => {
      btn.addEventListener('click', () => {
        document.querySelectorAll('.civSpeedBtn').forEach((b) => b.classList.remove('active'));
        btn.classList.add('active');
        speedMultiplier = Number(btn.dataset.speed);
      });
    });

    const seedInput = document.getElementById('civSeedInput');
    document.getElementById('civNewSeedBtn').addEventListener('click', () => {
      const seed = seedInput.value.trim() || randomSeedString();
      seedInput.value = seed;
      generateWorld(seed);
    });
    document.getElementById('civResetBtn').addEventListener('click', () => {
      generateWorld(currentSeed || randomSeedString());
    });

    const resourceSlider = document.getElementById('civResourceRateSlider');
    resourceSlider.addEventListener('input', () => { params.resourceRegrow = lerp(0.0008, 0.02, resourceSlider.value / 100); });
    params.resourceRegrow = lerp(0.0008, 0.02, resourceSlider.value / 100);

    const growthSlider = document.getElementById('civGrowthRateSlider');
    growthSlider.addEventListener('input', () => { params.growthRate = lerp(0.1, 3, growthSlider.value / 100); });
    params.growthRate = lerp(0.1, 3, growthSlider.value / 100);

    const brushSlider = document.getElementById('civBrushSizeSlider');
    brushSlider.addEventListener('input', () => { params.brushSize = Number(brushSlider.value); });
    params.brushSize = Number(brushSlider.value);
  }

  // ---------- MAIN LOOP (paused while this view is hidden) -----------------
  let running = false;

  function frame(now) {
    if (!running) return;
    if (!lastFrameTime) lastFrameTime = now;
    let dt = (now - lastFrameTime) / 1000;
    lastFrameTime = now;
    if (dt > 0.25) dt = 0.25;

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

  window.pauseCiv = function () { running = false; };
  window.resumeCiv = function () {
    if (running) return;
    running = true;
    lastFrameTime = 0;
    resizeEntityCanvas();
    resizeGraph();
    requestAnimationFrame(frame);
  };

  // ---------- INIT -----------------------------------------------------
  const initialSeed = randomSeedString();
  document.getElementById('civSeedInput').value = initialSeed;
  generateWorld(initialSeed);
  resizeEntityCanvas();
  resizeGraph();
  bindUI();
  bindPointer();
  sampleHistory();
  renderTerrain();
  renderEntities();
  renderGraph();
})();
