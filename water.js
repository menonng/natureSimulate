// ============================================================
// 3D 수조 물리 시뮬레이터 (3D water-tank physics simulator)
// Three.js scene + a classic discrete-wave-equation height field for the
// water surface. Clicking a point in the tank pushes the surface down
// there, and the impulse propagates outward as real ripples/waves.
// ES module: its scope is naturally private, no globals leak except the
// window.pauseWater/resumeWater hooks the switch script calls.
// ============================================================
import * as THREE from 'three';
import { OrbitControls } from './vendor/three/OrbitControls.js';

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
function playSplashSound() {
  const ctx = ensureWaterAudio();
  if (!ctx) return;
  const t0 = ctx.currentTime;
  const osc = ctx.createOscillator();
  const gain = ctx.createGain();
  osc.type = 'sine';
  osc.frequency.setValueAtTime(500, t0);
  osc.frequency.exponentialRampToValueAtTime(90, t0 + 0.22);
  gain.gain.setValueAtTime(0, t0);
  gain.gain.linearRampToValueAtTime(0.14, t0 + 0.01);
  gain.gain.exponentialRampToValueAtTime(0.0001, t0 + 0.28);
  osc.connect(gain).connect(ctx.destination);
  osc.start(t0);
  osc.stop(t0 + 0.3);
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

// ---------- interaction --------------------------------------------------
const raycaster = new THREE.Raycaster();
const pointerNdc = new THREE.Vector2();
const hitPoint = new THREE.Vector3();

canvas.addEventListener('pointerdown', (ev) => {
  ensureWaterAudio();
  const rect = canvas.getBoundingClientRect();
  pointerNdc.x = ((ev.clientX - rect.left) / rect.width) * 2 - 1;
  pointerNdc.y = -((ev.clientY - rect.top) / rect.height) * 2 + 1;
  raycaster.setFromCamera(pointerNdc, camera);
  if (!raycaster.ray.intersectPlane(rayPlane, hitPoint)) return;

  const half = (TANK_SIZE * 0.94) / 2;
  if (Math.abs(hitPoint.x) > half || Math.abs(hitPoint.z) > half) return; // clicked outside the tank

  const gx = ((hitPoint.x + half) / (half * 2)) * (GRID - 1);
  const gz = ((hitPoint.z + half) / (half * 2)) * (GRID - 1);
  splashAt(gx, gz, 1.1);
  playSplashSound();
});

document.getElementById('waterClearBtn').addEventListener('click', () => {
  curr.fill(0); prev.fill(0);
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

// ---------- main loop (paused while this view is hidden) -----------------
let running = false;

function loop() {
  if (!running) return;
  stepWaves();
  applyHeightsToMesh();
  controls.update();
  renderer.render(scene, camera);
  requestAnimationFrame(loop);
}

window.pauseWater = function () { running = false; };
window.resumeWater = function () {
  if (running) return;
  running = true;
  resize();
  requestAnimationFrame(loop);
};
