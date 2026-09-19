'use strict';
(function () {
  const views = {
    eco: { el: document.getElementById('app'), pause: () => window.pauseEcosystem(), resume: () => window.resumeEcosystem() },
    fluid: { el: document.getElementById('fluidApp'), pause: () => window.pauseFluid(), resume: () => window.resumeFluid() },
    water: { el: document.getElementById('waterApp'), pause: () => window.pauseWater(), resume: () => window.resumeWater() },
  };
  // Order the switch button cycles through, and what it's labeled with
  // (the label always shows the mode you'd switch TO next).
  const order = ['eco', 'fluid', 'water'];
  const labels = {
    eco: '🌿 생태계 시뮬레이터',
    fluid: '💨 유체 시뮬레이터',
    water: '🌊 수조 시뮬레이터',
  };

  let current = 'eco';
  const btn = document.getElementById('appSwitchBtn');

  function show(mode) {
    for (const key of order) {
      views[key].el.classList.toggle('hidden', key !== mode);
    }
    views[current].pause();
    views[mode].resume();
    current = mode;
    const next = order[(order.indexOf(current) + 1) % order.length];
    btn.textContent = labels[next];
    btn.title = labels[next] + '로 전환';
  }

  btn.textContent = labels[order[1]];
  btn.addEventListener('click', () => {
    const next = order[(order.indexOf(current) + 1) % order.length];
    show(next);
  });
})();
