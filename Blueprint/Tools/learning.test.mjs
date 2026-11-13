// node --test Blueprint/Tools/learning.test.mjs
import assert from "node:assert/strict";
import test from "node:test";
import { modeState } from "./learning.js";
import { insertLearningFeatures } from "./learning.mjs";

// Integrate the spatial profiles independently of the chart's energy formula.
function integral(f) {
  const n = 2048, h = Math.PI / n;
  let sum = 0;
  for (let i = 0; i < n; i++) sum += f((i + 0.5) * h);
  return sum * h;
}
const close = (actual, expected) => assert.ok(Math.abs(actual - expected) < 1e-9,
  `${actual} differs from ${expected}`);

test("the displayed energies agree with the spatial heat and wave profiles", () => {
  for (const k of [1, 3, 5]) for (const t of [0, 0.75, 2, 3]) {
    const state = modeState(k, t);
    const heatEnergy = integral(x => (state.heat * Math.sin(k * x)) ** 2);
    const waveEnergy = integral(x =>
      (-k * Math.sin(k * t) * Math.sin(k * x)) ** 2 +
      (k * state.wave * Math.cos(k * x)) ** 2);
    close(heatEnergy / (Math.PI / 2), state.heatEnergy);
    close(waveEnergy / (Math.PI * k * k / 2), state.waveEnergy);
  }
});

test("heat loses energy and waves can reverse their displacement", () => {
  for (const k of [1, 2, 5]) {
    assert.ok(modeState(k, 0.5).heatEnergy > modeState(k, 1).heatEnergy);
    assert.ok(modeState(k, 1).heatEnergy > modeState(k, 2).heatEnergy);
  }
  assert.ok(modeState(1, 3).wave < 0);
  assert.ok(modeState(5, 1).heat < modeState(1, 1).heat);
  for (const [k, t] of [[0, 1], [6, 1], [1.5, 1], [1, -1], [1, 4], [1, NaN]]) {
    assert.throws(() => modeState(k, t), RangeError);
  }
});

const marker = kind => `<div data-leanpde-learning="${kind}"></div>`;
const page = content => `<html><head><title>Book</title></head><body>` +
  `<aside><a href="Chapter/#proof">Proof</a></aside><main>${content}</main></body></html>`;
const features = { modes: "<section>Modes</section>", blowup: "<section>Blowup</section>" };

test("learning markers preserve surrounding prose, figures, scripts and source links", () => {
  const fake = `<script>const s = '${marker("modes")}';</script><!-- ${marker("blowup")} -->`;
  const content = fake + `<p>Before.</p>${marker("modes")}<svg></svg>${marker("blowup")}<p>After.</p>`;
  const html = insertLearningFeatures(page(content), features);
  assert.ok(html.includes(fake + "<p>Before.</p><section>Modes</section><svg></svg><section>Blowup</section><p>After.</p>"));
  assert.ok(html.includes('<a href="Chapter/#proof">Proof</a>'));
  assert.equal((html.match(/src="-verso-data\/leanpde-learning\/learning.js"/g) ?? []).length, 1);
  assert.equal(insertLearningFeatures(page("<p>No marker.</p>"), features), page("<p>No marker.</p>"));
});

test("unknown, duplicate, nonempty and misplaced learning markers are refused", () => {
  for (const content of [marker("missing"), marker("modes") + marker("modes"),
    marker("modes").replace("</div>", "Keep this prose</div>")]) {
    assert.throws(() => insertLearningFeatures(page(content), features), /learning marker/);
  }
  assert.throws(() => insertLearningFeatures(page("").replace("<main>", marker("modes") + "<main>"), features), /learning marker/);
});
