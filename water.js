// ============================================================
// 3D 수조 물리 시뮬레이터 (3D water-tank physics simulator)
// Three.js scene + a classic discrete-wave-equation height field for the
// water surface. Pressing and holding a point in the tank pushes the
// surface down there, and the impulse propagates outward as real waves -
// the longer you hold, the stronger the push.
// ES module: its scope is naturally private, no globals leak except the
// window.pauseWater/resumeWater hooks the switch script calls.
// ============================================================

// window.resumeWater/pauseWater must exist the instant this module starts,
// even before (or if) the three.js setup below finishes, so the app
// switcher never gets stuck waiting on a hook that doesn't exist yet.
let running = false;
let readyResumeRequested = false;
window.pauseWater = function () { running = false; };
window.resumeWater = function () {
  readyResumeRequested = true;
  if (window.__waterBootFailed) return;
  if (!window.__waterReady) return; // will be honored once setup finishes (see 'water-ready' below)
  if (running) return;
  running = true;
  if (typeof window.__waterResize === 'function') window.__waterResize();
  requestAnimationFrame(window.__waterLoop);
};

try {
  await initWaterTank();
} catch (err) {
  console.error('3D water tank failed to initialize:', err);
  window.__waterBootFailed = true;
  const wrap = document.querySelector('#waterApp .simCanvasWrap');
  if (wrap) {
    const msg = document.createElement('div');
    msg.style.cssText = 'position:absolute;inset:0;display:flex;align-items:center;justify-content:center;text-align:center;padding:24px;color:#b9ac93;font-size:.85rem;';
    msg.textContent = '이 브라우저에서는 3D 수조 시뮬레이터를 실행할 수 없습니다 (WebGL 필요).';
    wrap.appendChild(msg);
  }
}

async function initWaterTank() {
  const THREE = await import('three');
  const { OrbitControls } = await import('./vendor/three/OrbitControls.js');

  const GRID = 72;                 // water height-field resolution (GRID x GRID)
  const TANK_SIZE = 6;             // world units, water surface spans -TANK_SIZE/2..+TANK_SIZE/2
  const TANK_HEIGHT = 3.2;
  const WATER_REST_Y = 0.4;        // height of the still water surface inside the tank
  const DAMPING = 0.985;

  // ---------- height-field wave simulation -------------------------------
  let curr = new Float32Array(GRID * GRID);
  let prev = new Float32Array(GRID * GRID);
  function hIndex(x, z) { return x + z * GRID; }

  function stepWaves() {
    const next = prev; // reuse the older buffer as scratch for the new frame
    for (let z = 1; z < GRID - 1; z++) {
      for (let x = 1; x < GRID - 1; x++) {
        const i = hIndex(x, z);
        next[i] = (
          (curr[hIndex(x - 1, z)] + curr[hIndex(x + 1, z)] +
           curr[hIndex(x, z - 1)] + curr[hIndex(x, z + 1)]) / 2
          - prev[i]
        ) * DAMPING;
      }
    }
    prev = curr;
    curr = next;
  }

  function splashAt(gx, gz, strength) {
    const R = 2;
    for (let dz = -R; dz <= R; dz++) {
      for (let dx = -R; dx <= R; dx++) {
        const x = Math.round(gx) + dx, z = Math.round(gz) + dz;
        if (x < 1 || x >= GRID - 1 || z < 1 || z >= GRID - 1) continue;
        const d = Math.hypot(dx, dz);
        if (d > R) continue;
        const falloff = 1 - d / R;
        curr[hIndex(x, z)] -= strength * falloff;
      }
    }
  }

  // ---------- sound (own tiny Web Audio setup, no shared globals) --------
  let waterAudioCtx = null;
  function ensureWaterAudio() {
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return null;
    if (!waterAudioCtx) waterAudioCtx = new AC();
    if (waterAudioCtx.state === 'suspended') waterAudioCtx.resume();
    return waterAudioCtx;
  }
  function playSplashSound(strength) {
    const ctx = ensureWaterAudio();
    if (!ctx) return;
    const t0 = ctx.currentTime;
    const osc = ctx.createOscillator();
    const gain = ctx.createGain();
    const peak = Math.min(0.22, 0.08 + strength * 0.05);
    osc.type = 'sine';
    osc.frequency.setValueAtTime(520 - strength * 30, t0);
    osc.frequency.exponentialRampToValueAtTime(70, t0 + 0.24);
    gain.gain.setValueAtTime(0, t0);
    gain.gain.linearRampToValueAtTime(peak, t0 + 0.01);
    gain.gain.exponentialRampToValueAtTime(0.0001, t0 + 0.3);
    osc.connect(gain).connect(ctx.destination);
    osc.start(t0);
    osc.stop(t0 + 0.32);
  }

  // ---------- three.js scene ----------------------------------------------
  const canvas = document.getElementById('waterCanvas');
  const renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x050608);

  const camera = new THREE.PerspectiveCamera(45, 1, 0.1, 100);
  camera.position.set(TANK_SIZE * 1.1, TANK_HEIGHT * 1.5, TANK_SIZE * 1.35);

  const controls = new OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true;
  controls.dampingFactor = 0.08;
  controls.target.set(0, WATER_REST_Y, 0);
  controls.minDistance = 3;
  controls.maxDistance = 20;
  controls.maxPolarAngle = Math.PI * 0.49; // don't let the camera dip below the floor

  // lighting
  scene.add(new THREE.AmbientLight(0x8892a8, 0.7));
  const sun = new THREE.DirectionalLight(0xfff2d9, 1.1);
  sun.position.set(4, 7, 3);
  scene.add(sun);
  const rim = new THREE.PointLight(0x39c5bb, 0.6, 20);
  rim.position.set(-3, 2, -3);
  scene.add(rim);

  // tank frame (wireframe box, gold to match the site's theme)
  const tankGeo = new THREE.BoxGeometry(TANK_SIZE, TANK_HEIGHT, TANK_SIZE);
  tankGeo.translate(0, TANK_HEIGHT / 2 - 0.4, 0);
  const tankEdges = new THREE.LineSegments(
    new THREE.EdgesGeometry(tankGeo),
    new THREE.LineBasicMaterial({ color: 0xd9a62b, transparent: true, opacity: 0.55 })
  );
  scene.add(tankEdges);

  // floor
  const floor = new THREE.Mesh(
    new THREE.PlaneGeometry(TANK_SIZE * 3, TANK_SIZE * 3),
    new THREE.MeshStandardMaterial({ color: 0x14110d, roughness: 0.95 })
  );
  floor.rotation.x = -Math.PI / 2;
  floor.position.y = -0.4;
  scene.add(floor);

  // water surface
  const waterGeo = new THREE.PlaneGeometry(TANK_SIZE * 0.94, TANK_SIZE * 0.94, GRID - 1, GRID - 1);
  waterGeo.rotateX(-Math.PI / 2);
  const waterMat = new THREE.MeshPhysicalMaterial({
    color: 0x2a6fb0,
    transparent: true,
    opacity: 0.82,
    roughness: 0.15,
    metalness: 0,
    clearcoat: 0.6,
    side: THREE.DoubleSide,
  });
  const waterMesh = new THREE.Mesh(waterGeo, waterMat);
  waterMesh.position.y = WATER_REST_Y;
  scene.add(waterMesh);

  // invisible plane used purely for raycasting clicks at the water's rest height
  const rayPlane = new THREE.Plane(new THREE.Vector3(0, 1, 0), -WATER_REST_Y);

  function applyHeightsToMesh() {
    const pos = waterGeo.attributes.position;
    for (let z = 0; z < GRID; z++) {
      for (let x = 0; x < GRID; x++) {
        pos.setY(hIndex(x, z), curr[hIndex(x, z)]);
      }
    }
    pos.needsUpdate = true;
    waterGeo.computeVertexNormals();
  }

  // ---------- interaction: press-and-hold charges up the splash strength --
  const raycaster = new THREE.Raycaster();
  const pointerNdc = new THREE.Vector2();
  const hitPoint = new THREE.Vector3();
  const half = (TANK_SIZE * 0.94) / 2;

  let pressing = false;
  let pressStart = 0;
  let pressGX = 0, pressGZ = 0;
  const MAX_HOLD_SECONDS = 2.2;
  const MIN_STRENGTH = 0.5, MAX_STRENGTH = 4.2;

  function raycastToGrid(clientX, clientY) {
    const rect = canvas.getBoundingClientRect();
    pointerNdc.x = ((clientX - rect.left) / rect.width) * 2 - 1;
    pointerNdc.y = -((clientY - rect.top) / rect.height) * 2 + 1;
    raycaster.setFromCamera(pointerNdc, camera);
    if (!raycaster.ray.intersectPlane(rayPlane, hitPoint)) return null;
    if (Math.abs(hitPoint.x) > half || Math.abs(hitPoint.z) > half) return null;
    return [
      ((hitPoint.x + half) / (half * 2)) * (GRID - 1),
      ((hitPoint.z + half) / (half * 2)) * (GRID - 1),
    ];
  }

  canvas.addEventListener('pointerdown', (ev) => {
    const hit = raycastToGrid(ev.clientX, ev.clientY);
    if (!hit) return;
    ensureWaterAudio();
    pressing = true;
    pressStart = performance.now();
    [pressGX, pressGZ] = hit;
    canvas.setPointerCapture(ev.pointerId);
  });
  canvas.addEventListener('pointermove', (ev) => {
    if (!pressing) return;
    const hit = raycastToGrid(ev.clientX, ev.clientY);
    if (hit) [pressGX, pressGZ] = hit; // drag while holding to stir a different spot
  });
  function release() {
    if (!pressing) return;
    pressing = false;
    const held = (performance.now() - pressStart) / 1000;
    const t = Math.min(1, held / MAX_HOLD_SECONDS);
    const strength = MIN_STRENGTH + (MAX_STRENGTH - MIN_STRENGTH) * t;
    splashAt(pressGX, pressGZ, strength);
    playSplashSound(strength);
  }
  window.addEventListener('pointerup', release);
  window.addEventListener('pointercancel', release);

  document.getElementById('waterClearBtn').addEventListener('click', () => {
    curr.fill(0); prev.fill(0);
    pressing = false;
  });

  // ---------- responsive sizing --------------------------------------------
  function resize() {
    const rect = canvas.parentElement.getBoundingClientRect();
    if (rect.width < 1 || rect.height < 1) return; // view is hidden right now
    renderer.setSize(rect.width, rect.height, false);
    camera.aspect = rect.width / rect.height;
    camera.updateProjectionMatrix();
  }
  window.addEventListener('resize', resize);
  window.__waterResize = resize;

  // ---------- main loop (paused while this view is hidden) -----------------
  function loop() {
    if (!running) return;
    stepWaves();
    applyHeightsToMesh();
    controls.update();
    renderer.render(scene, camera);
    requestAnimationFrame(loop);
  }
  window.__waterLoop = loop;

  window.__waterReady = true;
  window.dispatchEvent(new Event('water-ready'));
  if (readyResumeRequested) window.resumeWater();
}
