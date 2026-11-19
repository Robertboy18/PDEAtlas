// Fill the book's explicit learning markers. The statements are linked through
// the rendered Blueprint graph, so a renamed or missing theorem stops the build.
import { copyFile, mkdir, readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { scanElements } from "./defer-html.mjs";
import { notebookMathRenderer } from "./opening-notebook.mjs";
import { displayNumber, energyPath, initialTime, modePath, modeState } from "./learning.js";

const toolsDir = path.dirname(fileURLToPath(import.meta.url));
const assetRoot = "-verso-data/leanpde-learning";
const escape = text => String(text).replaceAll("&", "&amp;").replaceAll("<", "&lt;")
  .replaceAll(">", "&gt;").replaceAll('"', "&quot;");

function curveSvg(kind, amplitude) {
  return `<svg viewBox="0 0 380 192" role="img" data-${kind}-plot
    aria-label="${kind === "heat" ? "Heat" : "Wave"} mode 1 at time ${initialTime}">
    <path class="learning-axis" d="M32 30V170 M32 100H348"/>
    <text x="19" y="38" text-anchor="end">1</text>
    <text x="19" y="169" text-anchor="end">−1</text>
    <text x="32" y="188" text-anchor="middle">0</text>
    <text x="190" y="188" text-anchor="middle">π/2</text>
    <text x="348" y="188" text-anchor="middle">π</text>
    <text x="367" y="104">x</text>
    <path class="learning-initial" data-${kind}-initial d="${modePath(1, 1)}"/>
    <path class="learning-${kind}-curve" data-${kind}-curve d="${modePath(1, amplitude)}"/>
  </svg>`;
}

function modeExplorer(math, heatEnergyLink) {
  const state = modeState(1, initialTime);
  return `<section class="leanpde-learning" data-learning-modes aria-labelledby="explore-modes">
    <p class="learning-eyebrow">Try an example</p>
    <h2 id="explore-modes">A warm rod and a vibrating string</h2>
    <p>Both begin with the same sine-shaped profile and fixed ends. Heat spreads out;
    the string oscillates. Move through time, then try a finer initial shape.</p>
    <div class="learning-controls" data-mode-controls hidden>
      <label for="learning-time"><span>Time t = <output id="learning-time-value" for="learning-time" data-time-output>0.75</output></span>
        <input id="learning-time" data-mode-time type="range" min="0" max="3" step="0.01" value="0.75"></label>
      <label for="learning-mode"><span>Mode k = <output id="learning-mode-value" for="learning-mode" data-mode-output>1</output></span>
        <input id="learning-mode" data-mode-number type="range" min="1" max="5" step="1" value="1"></label>
      <div class="learning-buttons"><button type="button" data-mode-play aria-pressed="false">Play</button>
        <button type="button" data-mode-reset>Reset</button></div>
    </div>
    <div class="learning-mode-pair">
      <div class="learning-mode"><h3>Heat · diffusion</h3>
        <div class="learning-math">${math(String.raw`u_t=u_{xx},\quad u=e^{-k^2t}\sin(kx)`)}</div>
        ${curveSvg("heat", state.heat)}
        <p>Amplitude ≈ <output data-heat-amplitude>${displayNumber(state.heat)}</output></p>
      </div>
      <div class="learning-mode"><h3>Waves · vibration</h3>
        <div class="learning-math">${math(String.raw`u_{tt}=u_{xx},\quad u=\cos(kt)\sin(kx)`)}</div>
        ${curveSvg("wave", state.wave)}
        <p>Displacement factor ≈ <output data-wave-amplitude>${displayNumber(state.wave)}</output></p>
      </div>
    </div>
    <p class="learning-observation" data-mode-observation>The heat profile flattens. The string keeps vibrating, exchanging motion and strain.</p>
    <div class="learning-energy"><h3>What happens to the energy?</h3>
      <div class="learning-legend"><span>Heat: temperature squared</span><span>Wave: motion + strain</span></div>
      <svg viewBox="0 0 720 157" role="img" aria-label="Relative heat energy decays; relative wave energy remains one.">
        <path class="learning-axis" d="M40 25V122H680"/>
        <text x="27" y="36" text-anchor="end">1</text><text x="27" y="126" text-anchor="end">0</text>
        <text x="40" y="144" text-anchor="middle">0</text><text x="253" y="144" text-anchor="middle">1</text>
        <text x="467" y="144" text-anchor="middle">2</text><text x="680" y="144" text-anchor="middle">3</text>
        <text x="699" y="126">t</text>
        <path class="learning-wave-curve" d="${energyPath(1, false)}"/>
        <path class="learning-heat-curve" data-heat-energy-curve d="${energyPath(1, true)}"/>
        <line class="learning-energy-marker" data-energy-time x1="200" x2="200" y1="25" y2="122"/>
        <circle class="learning-energy-dot" data-energy-dot cx="200" cy="${122 - 90 * state.heatEnergy}" r="4"/>
      </svg>
      <p class="learning-note">Each energy is divided by its own initial value. Heat ≈
        <output data-heat-energy>${displayNumber(state.heatEnergy)}</output>; wave = 1.</p>
    </div>
    <details><summary>Why does one energy fall while the other stays constant?</summary>
      <p>For the heat mode, the squared temperature is</p>
      <div class="learning-math">${math(String.raw`E_h(t)=\int_0^\pi u^2\,dx=\frac\pi2 e^{-2k^2t},\qquad E_h'=-2\int_0^\pi u_x^2\,dx.`)}</div>
      <p>A larger spatial gradient makes the temperature decay faster. For the string,
      motion and strain contribute together:</p>
      <div class="learning-math">${math(String.raw`E_w(t)=\int_0^\pi(u_t^2+u_x^2)\,dx=\frac{\pi k^2}{2}.`)}</div>
      <p>The sine and cosine factors exchange their contributions while their squared sum stays one.</p>
      <p>The integer mode matters: sin(kπ) = 0 keeps the right endpoint fixed.
      A noninteger frequency still satisfies the differential equation, but it
      generally fails this boundary condition.</p>
    </details>
    <p class="learning-note">Here 0 ≤ x ≤ π, k is a positive integer, and the string starts at rest.
      Time and length are scaled so the diffusivity and wave speed are one.
      The plots illustrate the formulas; the dashed curves show the initial shape.</p>
    <div class="learning-proof-links">
      <a href="Introduction/#notebook-heat">Heat calculation and Lean proof ↗</a>
      <a href="${escape(heatEnergyLink)}">Heat energy estimate ↗</a>
      <a href="Hyperbolic-Equations/">Wave equations ↗</a>
    </div>
  </section>`;
}

function readingRoutes() {
  const routes = [
    ["01", "Study Evans", "Start with the heat equation, then build the weak calculus needed for elliptic and evolution problems.",
      "Introduction → Sobolev spaces → elliptic, parabolic, and hyperbolic equations", "Introduction/", "Start reading"],
    ["02", "Explore CAS and CEGA", "Follow a symbolic calculation into its analytic meaning. Keep the domain conditions, then use an exact identity or a certified bound in a proof.",
      "Symbolic calculus → interval bounds → integration → PDE residuals", "Verified-Symbolic-and-Continuous-Computation/", "Try the calculations"],
  ];
  return `<section class="leanpde-learning" aria-labelledby="reading-routes">
    <p class="learning-eyebrow">Find a starting point</p><h2 id="reading-routes">Where to start</h2>
    <div class="learning-routes">${routes.map(([number, title, text, topics, href, action]) =>
      `<div class="learning-route"><span aria-hidden="true">${number}</span><div>
        <h3><a href="${href}">${title}</a></h3><p>${text}</p><p class="learning-route-topics">${topics}</p>
      </div><a href="${href}">${action} <span aria-hidden="true">→</span></a></div>`).join("")}</div>
  </section>`;
}

export async function buildLearningFeatures(dataDir) {
  const manifest = JSON.parse(await readFile(path.join(dataDir, "blueprint-manifest.json"), "utf8"));
  const nodes = new Map(manifest.graphs.flatMap(graph => graph.nodes)
    .map(node => [node.label.replace(/^«|»$/g, ""), node]));
  const theoremLink = label => {
    const node = nodes.get(label);
    if (!node?.href) throw new Error(`Learning feature: missing statement link for ${label}`);
    return node.href;
  };
  const math = await notebookMathRenderer(dataDir);
  const destination = path.join(dataDir, "leanpde-learning");
  await mkdir(destination, { recursive: true });
  await Promise.all(["learning.css", "learning.js"].map(file => copyFile(path.join(toolsDir, file), path.join(destination, file))));
  return {
    modes: modeExplorer(math, theoremLink("parabolic.energy_decay")),
    routes: readingRoutes(),
  };
}

export function insertLearningFeatures(html, features) {
  const markers = [], mains = [], heads = [];
  scanElements(html, element => {
    if (element.name === "main") mains.push(element);
    if (element.name === "head") heads.push(element);
    if (element.name !== "div") return;
    const marker = element.attrs().find(attr => attr.name === "data-leanpde-learning");
    if (marker) markers.push({ ...element, kind: marker.value });
  });
  if (!markers.length) return html;
  if (heads.length !== 1 || mains.length !== 1) throw new Error("Learning markers require one main and head.");
  const seen = new Set();
  for (const marker of markers) {
    if (!Object.hasOwn(features, marker.kind) || seen.has(marker.kind) ||
        marker.tagStart < mains[0].contentStart || marker.end > mains[0].contentEnd ||
        html.slice(marker.contentStart, marker.contentEnd).trim()) {
      throw new Error(`Invalid, repeated, or nonempty learning marker: ${marker.kind}`);
    }
    seen.add(marker.kind);
  }
  for (const marker of markers.sort((a, b) => b.tagStart - a.tagStart)) {
    html = html.slice(0, marker.tagStart) + features[marker.kind] + html.slice(marker.end);
  }
  const assets = `<link rel="stylesheet" href="${assetRoot}/learning.css">` +
    `<script type="module" src="${assetRoot}/learning.js"></script>`;
  return html.slice(0, heads[0].contentEnd) + assets + html.slice(heads[0].contentEnd);
}
