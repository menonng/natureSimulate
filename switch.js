'use strict';
(function () {
  const ecoApp = document.getElementById('app');
  const fluidApp = document.getElementById('fluidApp');
  const btn = document.getElementById('appSwitchBtn');
  let onFluid = false;
  let fluidStarted = false;

  btn.addEventListener('click', () => {
    onFluid = !onFluid;
    ecoApp.classList.toggle('hidden', onFluid);
    fluidApp.classList.toggle('hidden', !onFluid);
    btn.textContent = onFluid ? '🌿 생태계 시뮬레이터' : '💨 유체 시뮬레이터';
    btn.title = onFluid ? '먹이 피라미드 시뮬레이터로 전환' : '유체 시뮬레이터로 전환';

    if (onFluid) {
      window.pauseEcosystem();
      if (!fluidStarted) { fluidStarted = true; }
      window.resumeFluid();
    } else {
      window.pauseFluid();
      window.resumeEcosystem();
    }
  });
})();
