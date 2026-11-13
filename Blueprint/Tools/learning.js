// The plots sample explicit formulas. The accompanying links lead to the
// mathematical statements; moving a slider does not run a proof assistant.

export const initialTime = 0.75;

export function modeState(k, t) {
  if (!Number.isInteger(k) || k < 1 || k > 5 || !Number.isFinite(t) || t < 0 || t > 3) {
    throw new RangeError("The explorer uses modes 1–5 and times 0–3.");
  }
  return {
    heat: Math.exp(-k * k * t),
    wave: Math.cos(k * t),
    heatEnergy: Math.exp(-2 * k * k * t),
    waveEnergy: 1,
  };
}

export function modePath(k, amplitude) {
  return Array.from({ length: 161 }, (_, i) => {
    const x = Math.PI * i / 160;
    return `${i ? "L" : "M"}${(32 + 316 * i / 160).toFixed(2)},` +
      `${(100 - 66 * amplitude * Math.sin(k * x)).toFixed(2)}`;
  }).join(" ");
}

export function energyPath(k, heat) {
  return Array.from({ length: 181 }, (_, i) => {
    const t = 3 * i / 180;
    const y = heat ? modeState(k, t).heatEnergy : 1;
    return `${i ? "L" : "M"}${(40 + 640 * i / 180).toFixed(2)},${(122 - 90 * y).toFixed(2)}`;
  }).join(" ");
}

export function displayNumber(value) {
  if (value !== 0 && Math.abs(value) < 0.001) return value.toExponential(2).replace("e-", "e−");
  return value.toFixed(3).replace("-", "−");
}

function initializeModes(root) {
  const time = root.querySelector("[data-mode-time]");
  const mode = root.querySelector("[data-mode-number]");
  const play = root.querySelector("[data-mode-play]");
  let animation = 0;
  let lastFrame;
  let animationTime = 0;

  function render() {
    const k = Number(mode.value), t = Number(time.value);
    const state = modeState(k, t);
    root.querySelector("[data-time-output]").textContent = t.toFixed(2);
    root.querySelector("[data-mode-output]").textContent = k;
    for (const kind of ["heat", "wave"]) {
      root.querySelector(`[data-${kind}-curve]`).setAttribute("d", modePath(k, state[kind]));
      root.querySelector(`[data-${kind}-initial]`).setAttribute("d", modePath(k, 1));
      root.querySelector(`[data-${kind}-amplitude]`).textContent = displayNumber(state[kind]);
      root.querySelector(`[data-${kind}-plot]`).setAttribute("aria-label",
        `${kind === "heat" ? "Heat" : "Wave"} mode ${k} at time ${t.toFixed(2)}`);
    }
    root.querySelector("[data-heat-energy]").textContent = displayNumber(state.heatEnergy);
    root.querySelector("[data-heat-energy-curve]").setAttribute("d", energyPath(k, true));
    const x = 40 + 640 * t / 3;
    const marker = root.querySelector("[data-energy-time]");
    marker.setAttribute("x1", x);
    marker.setAttribute("x2", x);
    const dot = root.querySelector("[data-energy-dot]");
    dot.setAttribute("cx", x);
    dot.setAttribute("cy", 122 - 90 * state.heatEnergy);
    root.querySelector("[data-mode-observation]").textContent = k === 1
      ? "The heat profile flattens. The string keeps vibrating, exchanging motion and strain."
      : `Mode ${k} loses heat amplitude ${k * k} times as fast as mode 1. The string oscillates ${k} times as fast.`;
  }

  function stop() {
    cancelAnimationFrame(animation);
    animation = 0;
    lastFrame = undefined;
    play.textContent = "Play";
    play.setAttribute("aria-pressed", "false");
  }
  function frame(now) {
    if (lastFrame !== undefined) animationTime = Math.min(3, animationTime + (now - lastFrame) / 3500);
    time.value = animationTime;
    lastFrame = now;
    render();
    if (animationTime >= 3) stop();
    else animation = requestAnimationFrame(frame);
  }
  play.addEventListener("click", () => {
    if (animation) { stop(); return; }
    if (Number(time.value) >= 3) time.value = 0;
    animationTime = Number(time.value);
    play.textContent = "Pause";
    play.setAttribute("aria-pressed", "true");
    animation = requestAnimationFrame(frame);
  });
  for (const input of [time, mode]) input.addEventListener("input", () => { stop(); render(); });
  root.querySelector("[data-mode-reset]").addEventListener("click", () => {
    stop(); time.value = 0; mode.value = 1; render();
  });
  document.addEventListener("visibilitychange", () => { if (document.hidden) stop(); });
  // Motion is always reader-initiated. Stop an active animation if their
  // accessibility preference changes while the page is open.
  const reducedMotion = matchMedia("(prefers-reduced-motion: reduce)");
  reducedMotion.addEventListener("change", () => { if (reducedMotion.matches) stop(); });
  root.querySelector("[data-mode-controls]").hidden = false;
  render();
}

function initializeWalk(root) {
  const buttons = [...root.querySelectorAll("[data-walk-select]")];
  const panels = [...root.querySelectorAll("[data-walk-panel]")];
  function select(index) {
    panels.forEach((panel, i) => { panel.hidden = i !== index; });
    buttons.forEach((button, i) => button.setAttribute("aria-pressed", String(i === index)));
    root.querySelector("[data-walk-count]").textContent = `${index + 1} of ${panels.length}`;
    root.querySelector("[data-walk-next]").disabled = index === panels.length - 1;
    root.querySelector("[data-walk-back]").disabled = index === 0;
    root.dataset.walkIndex = index;
  }
  function selectFragment() {
    const index = panels.findIndex(panel => `#${panel.id}` === location.hash);
    if (index >= 0) select(index);
  }
  buttons.forEach((button, index) => button.addEventListener("click", () => select(index)));
  root.querySelector("[data-walk-next]").addEventListener("click", () => select(Number(root.dataset.walkIndex) + 1));
  root.querySelector("[data-walk-back]").addEventListener("click", () => select(Number(root.dataset.walkIndex) - 1));
  select(0);
  selectFragment();
  window.addEventListener("hashchange", selectFragment);
  root.querySelector("[data-walk-controls]").hidden = false;
  root.querySelector("[data-walk-navigation]").hidden = false;
  window.addEventListener("beforeprint", () => panels.forEach(panel => { panel.hidden = false; }));
  window.addEventListener("afterprint", () => select(Number(root.dataset.walkIndex)));
}

if (typeof document !== "undefined") {
  for (const root of document.querySelectorAll("[data-learning-modes]")) initializeModes(root);
  for (const root of document.querySelectorAll("[data-learning-walk]")) initializeWalk(root);
}
