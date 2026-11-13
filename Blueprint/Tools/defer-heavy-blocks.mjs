#!/usr/bin/env node
/*!
Move content that nobody has asked for yet out of the rendered pages.

Round 5 renders each chapter as one continuous route. Summed per chapter the old
per-section pages come to 15.5, 14.1, 13.9, 13.9, 10.5, 9.9, 7.3 and 6.8 MB, and a 15 MB
page with 150,000 elements locks the tab instead of reading like a book. Almost all of that
weight is content behind a click nobody has made: the closed `<details class="bp_code_block">`
panels alone hold 46 MB of highlighted Lean, and the hover surfaces hold another 27 MB.

This step runs after `optimize-site.mjs`, writes the hidden markup into per-page JSON
sidecars, and leaves behind enough of each element for the page to keep working:

  1. closed code panels keep their `<details>` and `<summary>`, plus one stub element per id
     that lived in the body, so `Ctrl-F` still finds the label and fragment links still
     resolve. The body arrives on the first open, or when a link points into it.
  2. `<template>` preview payloads and `.bp_relation_panel` bodies keep their host element,
     including the exact `class` string two audits match on, and arrive on the first pointer
     or focus that could open them.
  3. relation chips keep `data-bp-preview-id`, which is their trigger selector, and trade
     their five heavy `data-bp-preview-*` attributes for one index attribute.

`defer-runtime.mjs` is copied next to the generated data as `-verso-data/leanpde-defer.mjs`
and does the client half. Everything it needs is either an attribute this step writes or a
documented export of `blueprint-preview-api.mjs`.

Usage:
  node Blueprint/Tools/defer-heavy-blocks.mjs <site-dir> [--only=code,hover,attrs]
                                              [--chunk-bytes=N] [--quiet]
*/

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { applyEdits, classSet, scanElements } from "./defer-html.mjs";

const toolsRoot = path.dirname(fileURLToPath(import.meta.url));

const DEFAULT_CHUNK_BYTES = 512 * 1024;
const RUNTIME_NAME = "leanpde-defer.mjs";
/*
The chip attributes worth moving out. `data-bp-preview-id` stays because the rendered-site audit
counts citation chips by it, and `data-bp-preview-key` stays because the same audit reads the
landing page's pointers out of it. Both are also what a person greps for when a preview
misbehaves. What is left is the display payload: a title, a header label and href, and a footer
of escaped markup, none of it read before the reader hovers.
*/
const HEAVY_CHIP_ATTR = /^data-bp-preview-(title|header-label|header-href|footer-html)$/;

const STATUS_TEXT = "Loading the Lean code…";
const OFFLINE_TEXT =
  "We fetch the Lean code when you open a panel, so this part needs JavaScript. The rest of the page does not.";
const PANEL_STATUS_TEXT = "Loading this panel…";
const PANEL_OFFLINE_TEXT =
  "We fetch what is inside a panel when you open it, so this part needs JavaScript. The rest of the page does not.";
const SUMMARY_HINT = " (needs JavaScript)";
/*
Closed disclosures other than the Lean code panels are worth deferring too, and on the collapsed
chapters they matter: chapter 9 alone carries 928 nested `<details class="trace">` from the
elaborator, plus the `lean-output` blocks and the Taylor-model cards, and they are the reason that
page stayed over 4 MB after the code panels left. Small ones stay where they are, because a body
under a kilobyte costs less to ship than the request that would fetch it.
*/
const MIN_PANEL_BYTES = 1024;
/*
Disclosures the rendered-site audit reads as page content. The textbook map check wants every card
it cites to be linked from the CEGA chapter's own HTML, and the bibliography check counts the uses
it lists there, so those bodies stay in the page. Together they are half a megabyte, which is a
price worth paying to keep two audits honest.
*/
const KEEP_PANEL_CLASSES = ["leanpde-tm-cards", "leanpde-cp-theorems", "bp_bibliography_uses"];

const DEFER_STYLE =
  '<style>.bp_code_panel_deferred{margin:0;padding:.4rem .7rem}' +
  ".bp_defer_status,.bp_defer_offline{margin:0;font-size:.9em;font-style:italic;opacity:.7}" +
  ".bp_defer_offline{display:none}" +
  "</style>";
const DEFER_NOSCRIPT_STYLE =
  "<noscript><style>.bp_defer_status{display:none}.bp_defer_offline{display:block}</style></noscript>";

/*
Verso installs Lean token hovers once, on `load`, over the tokens present at that moment,
so declarations that arrive later have no docstring hovers and no binding highlights. This
one line publishes the closure values the installer built, and the client module reuses
them for inserted markup. Fail loudly if the generated script stops providing any of them:
a silent miss would cost every hover inside a code panel.
*/
const HOVER_KIT_NAMES = [
  "defaultTippyProps",
  "tokenSelector",
  "tacticTippySelector",
  "closedTactics",
  "isInsideClosedTactic",
  "blockedByTactic",
  "bindingCache",
];
const HOVER_KIT_PATCH =
  "\n    globalThis.leanpdeLeanHoverKit = { " +
  HOVER_KIT_NAMES.join(", ") +
  " };\n";

function fail(message) {
  process.stderr.write(`defer-heavy-blocks: ${message}\n`);
  process.exit(1);
}

function decodeHtml(value) {
  return String(value ?? "")
    .replace(/&#x([0-9a-f]+);/gi, (_m, hex) => String.fromCodePoint(Number.parseInt(hex, 16)))
    .replace(/&#([0-9]+);/g, (_m, dec) => String.fromCodePoint(Number.parseInt(dec, 10)))
    .replace(/&quot;/g, '"')
    .replace(/&apos;/g, "'")
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&nbsp;/g, " ")
    .replace(/&amp;/g, "&");
}

function htmlPages(dir) {
  const out = [];
  const walk = (current) => {
    for (const entry of fs.readdirSync(current, { withFileTypes: true })) {
      if (entry.name.startsWith("-verso")) continue;
      const full = path.join(current, entry.name);
      if (entry.isDirectory()) walk(full);
      else if (entry.name.endsWith(".html")) out.push(full);
    }
  };
  walk(dir);
  out.sort();
  return out;
}

/** Group payloads into chunk files so one open never drags in a whole chapter. */
function assignChunks(entries, chunkBytes) {
  let chunk = 0;
  let used = 0;
  for (const entry of entries) {
    const size = entry.payload.length;
    if (used > 0 && used + size > chunkBytes) {
      chunk += 1;
      used = 0;
    }
    entry.chunk = chunk;
    entry.ref = `${chunk}/${entry.key}`;
    used += size;
  }
  return entries.length === 0 ? 0 : chunk + 1;
}

function collect(html, only) {
  const regions = [];
  const chips = [];
  const previewRoots = [];
  const idPositions = [];
  const namePositions = [];
  const wantCode = only.has("code");
  const wantHover = only.has("hover");
  const wantAttrs = only.has("attrs");

  const leftover = scanElements(html, (el) => {
    if (el.name === "details") {
      let classValue = null;
      let isOpen = false;
      for (const attr of el.attrs()) {
        if (attr.name === "class") classValue = attr.value;
        else if (attr.name === "open") isOpen = true;
      }
      if (!wantCode || isOpen) return;
      const classes = classSet(classValue);
      const isCodePanel = classes.has("bp_code_block");
      if (!isCodePanel && KEEP_PANEL_CLASSES.some((name) => classes.has(name))) return;
      /*
      The label has to be the first thing inside, or the `</summary>` we find could belong to a
      nested disclosure and we would cut the outer one in the wrong place. A code panel that is
      not shaped that way means the renderer changed under us, so we stop; anything else we leave
      alone.
      */
      const firstTag = html.indexOf("<", el.contentStart);
      const summaryFirst =
        firstTag !== -1 && firstTag < el.contentEnd && /^<summary[\s>]/i.test(html.slice(firstTag, firstTag + 9));
      const summaryClose = summaryFirst ? html.indexOf("</summary>", firstTag) : -1;
      if (summaryClose === -1 || summaryClose >= el.contentEnd) {
        if (isCodePanel) {
          fail("a closed bp_code_block panel has no summary; refusing to guess where its body starts");
        }
        return;
      }
      const bodyStart = summaryClose + "</summary>".length;
      if (!isCodePanel && el.contentEnd - bodyStart < MIN_PANEL_BYTES) return;
      regions.push({
        kind: "code",
        label: isCodePanel ? "code" : "panel",
        start: bodyStart,
        end: el.contentEnd,
        summaryClose,
      });
      return;
    }
    if (el.name === "template") {
      if (!wantHover) return;
      regions.push({ kind: "tpl", start: el.contentStart, end: el.contentEnd, tagEnd: el.tagEnd });
      return;
    }
    if (wantHover) {
      for (const attr of el.attrs()) {
        if (attr.name !== "data-bp-template-preview-root") continue;
        previewRoots.push({ start: el.tagStart, end: el.end, attr });
        break;
      }
    }
    if (el.name === "div") {
      if (!wantHover) return;
      for (const attr of el.attrs()) {
        if (attr.name === "class" && classSet(attr.value).has("bp_relation_panel")) {
          regions.push({ kind: "rel", start: el.contentStart, end: el.contentEnd, tagEnd: el.tagEnd });
          return;
        }
      }
      return;
    }
    if (el.name === "span" && wantAttrs) {
      let isChip = false;
      const heavy = [];
      for (const attr of el.attrs()) {
        if (attr.name === "class" && classSet(attr.value).has("bp_inline_preview_ref")) isChip = true;
        else if (HEAVY_CHIP_ATTR.test(attr.name)) {
          heavy.push(attr);
        }
      }
      if (isChip && heavy.length > 0) {
        chips.push({ tagStart: el.tagStart, tagEnd: el.tagEnd, heavy });
      }
    }
  });
  if (leftover !== 0) fail(`unbalanced markup: ${leftover} elements never closed`);

  // Ids and names, in document order, so each region can list what it takes away.
  for (const match of html.matchAll(/\s(id|name)="([^"]*)"/g)) {
    const at = match.index + match[0].length;
    if (match[1] === "id") idPositions.push({ at, raw: match[2] });
    else namePositions.push({ at, raw: match[2] });
  }

  regions.sort((a, b) => a.start - b.start || b.end - a.end);
  const kept = [];
  let barrier = -1;
  for (const region of regions) {
    if (region.start < barrier) continue;
    kept.push(region);
    barrier = region.end;
  }
  return { kept, chips, previewRoots, idPositions, namePositions };
}

function inRegion(kept, at) {
  let low = 0;
  let high = kept.length - 1;
  while (low <= high) {
    const mid = (low + high) >> 1;
    if (kept[mid].end <= at) low = mid + 1;
    else if (at < kept[mid].start) high = mid - 1;
    else return kept[mid];
  }
  return null;
}

function transformPage(html, options) {
  const { relDir, only, chunkBytes, relativeFile } = options;
  const { kept, chips, previewRoots, idPositions, namePositions } = collect(html, only);
  if (kept.length === 0 && chips.length === 0) return null;

  const codeEntries = [];
  const hoverEntries = [];
  const edits = [];
  const idIndex = {};
  const stats = {
    codePanels: 0,
    codeBytes: 0,
    hoverHosts: 0,
    hoverBytes: 0,
    chips: 0,
    chipBytes: 0,
    stubs: 0,
    previewRoots: 0,
  };

  for (const name of namePositions) {
    if (inRegion(kept, name.at)) {
      fail(`${relativeFile}: a deferred region declares name="${name.raw}"; only ids are stubbed`);
    }
  }

  let idCursor = 0;
  for (const region of kept) {
    const payload = html.slice(region.start, region.end);
    if (region.kind === "code") {
      const key = `c${codeEntries.length}`;
      const ids = [];
      while (idCursor < idPositions.length && idPositions[idCursor].at < region.start) idCursor += 1;
      while (idCursor < idPositions.length && idPositions[idCursor].at < region.end) {
        ids.push(idPositions[idCursor].raw);
        idCursor += 1;
      }
      const entry = { key, payload, ids, region };
      codeEntries.push(entry);
      stats.codePanels += 1;
      stats.codeBytes += payload.length;
      stats.stubs += ids.length;
    } else {
      const key = `h${hoverEntries.length}`;
      hoverEntries.push({ key, payload, region });
      stats.hoverHosts += 1;
      stats.hoverBytes += payload.length;
    }
  }

  const attrEntries = [];
  for (const chip of chips) {
    if (inRegion(kept, chip.tagStart)) continue;
    const bundle = {};
    let bytes = 0;
    for (const attr of chip.heavy) {
      bundle[attr.name.slice("data-bp-preview-".length)] = decodeHtml(attr.value);
      bytes += attr.end - attr.start;
    }
    attrEntries.push({ key: `a${attrEntries.length}`, payload: JSON.stringify(bundle), bundle, chip });
    stats.chips += 1;
    stats.chipBytes += bytes;
  }

  const codeChunks = assignChunks(codeEntries, chunkBytes);
  const hoverChunks = assignChunks(hoverEntries.concat(attrEntries), chunkBytes);

  for (const entry of codeEntries) {
    const stubs = entry.ids.map((raw) => `<span id="${raw}"></span>`).join("");
    for (const raw of entry.ids) idIndex[decodeHtml(raw)] = entry.ref;
    edits.push({
      start: entry.region.start,
      end: entry.region.end,
      text:
        `<div class="bp_code_panel_deferred" data-bp-defer-code="${entry.ref}">` +
        `<p class="bp_defer_status">${entry.region.label === "code" ? STATUS_TEXT : PANEL_STATUS_TEXT}</p>` +
        `<p class="bp_defer_offline">${entry.region.label === "code" ? OFFLINE_TEXT : PANEL_OFFLINE_TEXT}</p>` +
        stubs +
        "</div>",
    });
    edits.push({
      start: entry.region.summaryClose,
      end: entry.region.summaryClose,
      text: `<noscript>${SUMMARY_HINT}</noscript>`,
    });
  }

  /*
  A preview surface whose body we took away has to stay unbound until the body comes back.
  `bindTemplatePreview` moves the panel to `document.body` before it checks whether the template
  holds anything, so a bind against an empty template moves the panel out of the descriptor root
  and then declines; every later bind looks for the panel inside the root, cannot find it, and
  declines too. The surface would be dead for the rest of the page's life. So we rename the
  descriptor attribute here, which makes the page's own first pass skip the root, and the runtime
  renames it back once the body has arrived and binds it then.
  */
  const deferredRoots = previewRoots.filter((root) =>
    kept.some(
      (region) => region.kind !== "code" && region.start >= root.start && region.end <= root.end,
    ),
  );
  for (const root of deferredRoots) {
    edits.push({
      start: root.attr.start,
      end: root.attr.end,
      text: `data-bp-defer-preview-root="${root.attr.value}"`,
    });
  }
  stats.previewRoots = deferredRoots.length;

  for (const entry of hoverEntries) {
    const region = entry.region;
    if (html[region.tagEnd - 1] !== ">") fail(`${relativeFile}: malformed start tag for a hover surface`);
    edits.push({ start: region.start, end: region.end, text: "" });
    edits.push({
      start: region.tagEnd - 1,
      end: region.tagEnd - 1,
      text: ` data-bp-defer-hover="${entry.ref}" data-bp-defer-kind="${region.kind}"`,
    });
  }

  for (const entry of attrEntries) {
    const chip = entry.chip;
    for (const attr of chip.heavy) {
      const from = /\s/.test(html[attr.start - 1]) ? attr.start - 1 : attr.start;
      edits.push({ start: from, end: attr.end, text: "" });
    }
    edits.push({
      start: chip.tagEnd - 1,
      end: chip.tagEnd - 1,
      text: ` data-bp-defer-attrs="${entry.ref}"`,
    });
  }

  /*
  Page-level wiring: where the sidecars are, and who loads them. The descriptors ride on the
  module's own script tag rather than on `<html>`, because `optimize-site.mjs` writes
  `<html lang="en">` and the rendered-site audit matches that string literally.
  */
  const headClose = html.toLowerCase().lastIndexOf("</head>");
  if (headClose === -1) fail(`${relativeFile}: no </head>`);
  edits.push({
    start: headClose,
    end: headClose,
    text:
      DEFER_STYLE +
      DEFER_NOSCRIPT_STYLE +
      `<script type="module" src="-verso-data/${RUNTIME_NAME}"` +
      ` data-bp-defer-dir="${relDir}"` +
      ` data-bp-defer-code-chunks="${codeChunks}"` +
      ` data-bp-defer-hover-chunks="${hoverChunks}"></script>`,
  });

  const hoverKit = patchHoverKit(html, relativeFile);
  if (hoverKit) edits.push(hoverKit);

  const output = applyEdits(html, edits);

  const sidecars = new Map();
  for (let chunk = 0; chunk < codeChunks; chunk += 1) {
    const body = {};
    for (const entry of codeEntries) if (entry.chunk === chunk) body[entry.key] = entry.payload;
    sidecars.set(`-deferred-code-${chunk}.json`, JSON.stringify(body));
  }
  for (let chunk = 0; chunk < hoverChunks; chunk += 1) {
    const body = {};
    for (const entry of hoverEntries) if (entry.chunk === chunk) body[entry.key] = entry.payload;
    for (const entry of attrEntries) if (entry.chunk === chunk) body[entry.key] = entry.bundle;
    sidecars.set(`-deferred-hover-${chunk}.json`, JSON.stringify(body));
  }
  if (Object.keys(idIndex).length > 0) {
    sidecars.set("-deferred-index.json", JSON.stringify({ ids: idIndex }));
  }

  return { output, sidecars, stats, codeChunks, hoverChunks };
}

/** Publish the Lean hover closure so inserted declarations can be bound later. */
function patchHoverKit(html, relativeFile) {
  const pattern = /<script\b[^>]*>([\s\S]*?)<\/script>/gi;
  for (const match of html.matchAll(pattern)) {
    const body = match[1];
    if (!body.includes("const tokenSelector") || !body.includes("window.onload")) continue;
    if (body.includes("leanpdeLeanHoverKit")) return null;
    for (const name of HOVER_KIT_NAMES) {
      if (!new RegExp(`\\b${name}\\b`).test(body)) {
        fail(
          `${relativeFile}: the generated Lean hover script no longer defines ${name}, ` +
            "so hovers inside deferred panels would silently stop working",
        );
      }
    }
    const bodyStart = match.index + match[0].indexOf(body);
    const lastBrace = body.lastIndexOf("}");
    if (lastBrace === -1) fail(`${relativeFile}: cannot find the end of the Lean hover script`);
    const at = bodyStart + lastBrace;
    return { start: at, end: at, text: HOVER_KIT_PATCH };
  }
  return null;
}

function main() {
  const args = process.argv.slice(2);
  let siteDir = null;
  let chunkBytes = DEFAULT_CHUNK_BYTES;
  let quiet = false;
  let only = new Set(["code", "hover", "attrs"]);
  for (const arg of args) {
    if (arg === "--quiet") quiet = true;
    else if (arg.startsWith("--chunk-bytes=")) chunkBytes = Number(arg.slice("--chunk-bytes=".length));
    else if (arg.startsWith("--only=")) only = new Set(arg.slice("--only=".length).split(",").filter(Boolean));
    else if (arg.startsWith("--")) fail(`unknown option ${arg}`);
    else if (siteDir === null) siteDir = arg;
    else fail("pass one site directory");
  }
  if (!siteDir) fail("usage: defer-heavy-blocks.mjs <site-dir> [--only=code,hover,attrs]");
  siteDir = path.resolve(siteDir);
  if (!fs.existsSync(path.join(siteDir, "-verso-data"))) {
    fail(`${siteDir} does not look like a rendered blueprint site`);
  }
  if (!Number.isFinite(chunkBytes) || chunkBytes < 1024) fail("--chunk-bytes must be at least 1024");

  const runtimeSource = path.join(toolsRoot, "defer-runtime.mjs");
  if (!fs.existsSync(runtimeSource)) fail(`missing ${runtimeSource}`);

  const pages = htmlPages(siteDir);
  const report = { chunkBytes, pages: [], totals: {} };
  const totals = {
    before: 0,
    after: 0,
    codePanels: 0,
    codeBytes: 0,
    hoverHosts: 0,
    hoverBytes: 0,
    chips: 0,
    chipBytes: 0,
    stubs: 0,
    previewRoots: 0,
    sidecarBytes: 0,
    touched: 0,
  };

  for (const file of pages) {
    const relativeFile = path.relative(siteDir, file);
    const html = fs.readFileSync(file, "utf8");
    const relDir = path.relative(siteDir, path.dirname(file)).split(path.sep).filter(Boolean).join("/");
    const result = transformPage(html, {
      relDir: relDir ? `${relDir}/` : "",
      only,
      chunkBytes,
      relativeFile,
    });
    const before = Buffer.byteLength(html);
    totals.before += before;
    if (!result) {
      totals.after += before;
      report.pages.push({ file: relativeFile, before, after: before, deferred: 0 });
      continue;
    }
    const after = Buffer.byteLength(result.output);
    let sidecarBytes = 0;
    fs.writeFileSync(file, result.output);
    for (const [name, body] of result.sidecars) {
      const target = path.join(path.dirname(file), name);
      fs.writeFileSync(target, body);
      sidecarBytes += Buffer.byteLength(body);
    }
    totals.after += after;
    totals.sidecarBytes += sidecarBytes;
    totals.touched += 1;
    for (const key of ["codePanels", "codeBytes", "hoverHosts", "hoverBytes", "chips", "chipBytes", "stubs", "previewRoots"]) {
      totals[key] += result.stats[key];
    }
    report.pages.push({
      file: relativeFile,
      before,
      after,
      sidecarBytes,
      codeChunks: result.codeChunks,
      hoverChunks: result.hoverChunks,
      ...result.stats,
    });
  }

  fs.copyFileSync(runtimeSource, path.join(siteDir, "-verso-data", RUNTIME_NAME));
  report.totals = totals;
  fs.writeFileSync(
    path.join(siteDir, "-verso-data", "leanpde-defer-report.json"),
    `${JSON.stringify(report, null, 2)}\n`,
  );

  if (!quiet) {
    const mb = (n) => (n / 1048576).toFixed(2);
    const worst = report.pages.slice().sort((a, b) => b.after - a.after).slice(0, 5);
    process.stdout.write(
      `deferred ${totals.codePanels} code panels (${mb(totals.codeBytes)} MB), ` +
        `${totals.hoverHosts} hover surfaces (${mb(totals.hoverBytes)} MB), ` +
        `${totals.chips} chip bundles (${mb(totals.chipBytes)} MB) ` +
        `across ${totals.touched} of ${pages.length} pages\n` +
        `site HTML ${mb(totals.before)} MB -> ${mb(totals.after)} MB, ` +
        `sidecars ${mb(totals.sidecarBytes)} MB, ${totals.stubs} id stubs kept in place\n` +
        `heaviest pages now: ${worst.map((p) => `${p.file} ${mb(p.after)} MB`).join(", ")}\n`,
    );
  }
}

main();
