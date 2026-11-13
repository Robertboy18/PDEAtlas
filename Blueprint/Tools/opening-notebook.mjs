// The opening notebook is a view of source proofs, not an evaluator. Extract the
// declarations from the same checkout as the renderer, and ship their provenance
// even when there is no public repository URL.
import { createHash } from "node:crypto";
import { copyFile, mkdir, readFile, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { runInNewContext } from "node:vm";
import path from "node:path";
import { scanElements } from "./defer-html.mjs";

const toolsDir = path.dirname(fileURLToPath(import.meta.url));
const sourceRoot = path.resolve(toolsDir, "../..");
const assetRoot = "-verso-data/leanpde-notebook";

const examples = [
  {
    id: "heat",
    label: "Heat equation",
    title: "A separated heat mode",
    equation: String.raw`u(t,x)=e^{-t}\sin x,\qquad u_t=u_{xx}`,
    result: String.raw`u_t-u_{xx}=0`,
    explanation:
      "The time derivative and the second spatial derivative agree. " +
      "This theorem checks the symbolic residual on all of spacetime.",
    note: "In the Lean definitions, x is time and y is the spatial coordinate.",
    file: "PDE/Parabolic/Symbolic/Heat/SeparationOfVariables.lean",
    declarations: [
      "def separatedHeatMode1DAnsatz : Verified.Expr (Fin 2) :=",
      "def separatedHeatMode1DResidual : Verified.Expr (Fin 2) :=",
      "theorem separatedHeatMode1D_closed_residual_eq_zero :",
    ],
    supportingDeclarations: [
      "private theorem separatedHeatMode1D_analytic_side_condition",
      "theorem separatedHeatMode1D_analytic_residual_eq_zero :",
    ],
    bridge:
      "The analytic bridge transfers this identity to ordinary Euclidean derivatives.",
  },
  {
    id: "rational",
    label: "Rational identity",
    title: "Cancel a factor, keep the condition",
    equation: String.raw`\frac{x^4-1}{x^2-1},\qquad x^2-1\ne 0`,
    result: String.raw`\frac{x^4-1}{x^2-1}=x^2+1`,
    explanation:
      "The nonzero denominator is part of the theorem. " +
      "The cancellation is justified under that hypothesis.",
    file: "PDE/Examples/Symbolic/CAS/Basic.lean",
    declarations: ["example (x : ℝ) (hx : x ^ 2 - 1 ≠ 0) :"],
  },
  {
    id: "enclosure",
    label: "CEGA enclosure",
    title: "Bound a whole interval",
    equation: String.raw`f(x)=\frac{x}{1+x},\qquad 0\le x\le 1`,
    result: String.raw`0\le \frac{x}{1+x}\le \frac12`,
    explanation:
      "CEGA proves that every value on the stated interval lies in [0, ½]. " +
      "The conclusion is an exact bound.",
    file: "PDE/Examples/Symbolic/CEGA/BoxInequalities.lean",
    declarations: [
      "example (x : ℝ) (h0 : x ≥ 0) (h1 : x ≤ 1) : x / (1 + x) ∈ Set.Icc (0 : ℝ) (1 / 2) := by",
    ],
  },
];

function escapeHtml(value) {
  return String(value).replaceAll("&", "&amp;").replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;").replaceAll('"', "&quot;");
}

// These short declarations have no internal blank lines. Refuse a missing or
// ambiguous selector instead of silently publishing a stale, hand-copied proof.
export function extractDeclaration(source, start, file) {
  const lines = source.split("\n");
  const matches = lines.flatMap((line, index) => line === start ? [index] : []);
  if (matches.length !== 1) {
    throw new Error(`Opening notebook: expected one ${JSON.stringify(start)} in ${file}.`);
  }
  const first = matches[0];
  let end = first + 1;
  while (end < lines.length && lines[end].trim() !== "") end += 1;
  return { firstLine: first + 1, lastLine: end, text: lines.slice(first, end).join("\n") };
}

function codeCell(text, label) {
  return `<pre tabindex="0" aria-label="${escapeHtml(label)}"><code>${escapeHtml(text)}</code></pre>`;
}

// Use the renderer's vendored KaTeX, with its matching CSS and fonts. The output
// includes MathML and needs no browser script; do not give it the .math class,
// which would make Verso's math.js render the already-rendered contents again.
export async function notebookMathRenderer(dataDir) {
  const filename = path.join(dataDir, "katex/katex.js");
  const module = { exports: {} };
  runInNewContext(await readFile(filename, "utf8"), { module, exports: module.exports }, { filename });
  if (typeof module.exports.renderToString !== "function") {
    throw new Error("Opening notebook: vendored KaTeX has no renderToString.");
  }
  return (tex) => module.exports.renderToString(tex, {
    displayMode: true, output: "htmlAndMathml", throwOnError: true, strict: "error", trust: false,
  });
}

function exampleHtml(example, excerpts, renderMath) {
  const proof = excerpts.at(-1);
  const setup = excerpts.slice(0, -1);
  const definitions = setup.length
    ? '<details class="leanpde-notebook-definitions"><summary>Definitions used in this cell</summary>' +
      `<p>${escapeHtml(example.note)}</p>` +
      codeCell(setup.map((entry) => entry.text).join("\n\n"), "Lean definitions") + "</details>"
    : "";
  const bridge = example.bridge
    ? `<p class="leanpde-notebook-bridge"><a href="${assetRoot}/${example.id}.txt">` +
      `${escapeHtml(example.bridge)}</a></p>`
    : "";
  return (
    `<article class="leanpde-notebook-example" id="notebook-${example.id}"` +
    ` aria-label="${escapeHtml(example.title)}">` +
    `<h3>${escapeHtml(example.title)}</h3>` +
    `<div class="leanpde-notebook-math">${renderMath(example.equation)}</div>` +
    '<div class="leanpde-notebook-cell leanpde-notebook-input">' +
    '<p class="leanpde-notebook-label">Lean input</p>' +
    codeCell(proof.text, `${example.label}: Lean proof`) +
    definitions + "</div>" +
    '<div class="leanpde-notebook-cell leanpde-notebook-result">' +
    '<p class="leanpde-notebook-label">Proved result</p>' +
    `<div class="leanpde-notebook-math">${renderMath(example.result)}</div>` +
    `<p>${escapeHtml(example.explanation)}</p>${bridge}</div>` +
    '<p class="leanpde-notebook-source">' +
    `<a href="${assetRoot}/${example.id}.txt">Source excerpt` +
    ` <span aria-hidden="true">↗</span><span class="leanpde-notebook-source-path">` +
    `${escapeHtml(example.file)}:${proof.firstLine}</span></a>` +
    "</p></article>"
  );
}

/** Build static cells and their local source references. No Lean commands run here. */
export async function buildOpeningNotebook(dataDir, revision, renderMath) {
  renderMath ??= await notebookMathRenderer(dataDir);
  const destination = path.join(dataDir, "leanpde-notebook");
  const records = await Promise.all(examples.map(async (example) => {
    const source = await readFile(path.join(sourceRoot, example.file), "utf8");
    const excerpts = example.declarations.map((start) =>
      extractDeclaration(source, start, example.file));
    const supportingExcerpts = (example.supportingDeclarations ?? []).map((start) =>
      extractDeclaration(source, start, example.file));
    return {
      example, excerpts, supportingExcerpts,
      sourceSha256: createHash("sha256").update(source).digest("hex"),
    };
  }));
  await mkdir(destination, { recursive: true });
  for (const { example, excerpts, supportingExcerpts, sourceSha256 } of records) {
    const text = [
      "LeanPDE opening notebook — source excerpt",
      `Module: ${example.file}`,
      `Build revision: ${revision}`,
      `Source SHA-256: ${sourceSha256}`,
      "",
      "These declarations are excerpts, with the imports and surrounding namespace omitted.",
      "Read them in the context of the source module; this is not a standalone Lean file.",
      "",
      ...[...excerpts, ...supportingExcerpts].flatMap((entry) => [
        `Lines ${entry.firstLine}–${entry.lastLine}:`, entry.text, "",
      ]),
    ].join("\n");
    // A plain-text server may omit the charset. The BOM keeps Lean's Unicode
    // readable when the reader opens this excerpt directly in a browser.
    await writeFile(path.join(destination, `${example.id}.txt`), "\ufeff" + text);
  }
  await Promise.all(["opening-notebook.css", "opening-notebook.js"].map((asset) =>
    copyFile(path.join(toolsDir, asset), path.join(destination, asset))));
  const manifest = records.map(({ example, excerpts, supportingExcerpts, sourceSha256 }) => ({
    id: example.id, file: example.file, sourceSha256, excerpts, supportingExcerpts,
    mathematics: [example.equation, example.result],
  }));
  await writeFile(path.join(destination, "sources.json"),
    JSON.stringify({ revision, examples: manifest }, null, 2) + "\n");
  const buttons = examples.map((example) =>
    `<button type="button" aria-pressed="false" aria-controls="notebook-${example.id}"` +
    ` data-notebook-select="${example.id}">${escapeHtml(example.label)}</button>`).join("");
  return (
    '<section class="leanpde-notebook" aria-labelledby="opening-notebook">' +
    '<header><p class="leanpde-notebook-kicker">PDE / CAS notebook</p>' +
    '<h2 id="opening-notebook">A calculation, with its proof</h2>' +
    '<p>Three recorded examples from the library. Each cell shows the Lean proof and its result.</p>' +
    '</header><div class="leanpde-notebook-controls" role="group"' +
    ` aria-label="Choose a worked example" hidden>${buttons}</div>` +
    records.map(({ example, excerpts }) => exampleHtml(example, excerpts, renderMath)).join("") +
    "</section>"
  );
}

/**
 * Introduction contract: one empty <div data-leanpde-notebook="opening"></div>.
 * This is a structural match: quoted attributes, comments and inline JS cannot
 * supply the marker. Refuse to place the notebook somewhere else by accident.
 */
export function insertOpeningNotebook(html, notebook) {
  const markers = [];
  const mains = [];
  const heads = [];
  scanElements(html, (element) => {
    if (element.name === "head") heads.push(element);
    if (element.name === "main") mains.push(element);
    if (element.name !== "div") return;
    const attrs = new Map(element.attrs().map(({ name, value }) => [name, value]));
    if (attrs.get("data-leanpde-notebook") === "opening") markers.push(element);
  });
  if (heads.length !== 1 || mains.length !== 1 || markers.length !== 1) {
    throw new Error("Opening notebook: expected one head, one main and exactly one insertion marker.");
  }
  const head = heads[0];
  const anchor = markers[0];
  if (anchor.tagStart < mains[0].contentStart || anchor.end > mains[0].contentEnd) {
    throw new Error("Opening notebook: no unique insertion anchor inside main.");
  }
  if (html.slice(anchor.contentStart, anchor.contentEnd).trim() !== "") {
    throw new Error("Opening notebook: insertion marker must be empty; refusing to discard content.");
  }
  const body = html.slice(0, anchor.tagStart) + notebook + html.slice(anchor.end);
  const assets = `<link rel="stylesheet" href="${assetRoot}/opening-notebook.css">` +
    `<script defer src="${assetRoot}/opening-notebook.js"></script>`;
  return {
    html: body.slice(0, head.contentEnd) + assets + body.slice(head.contentEnd),
    anchor: "explicit marker",
  };
}
