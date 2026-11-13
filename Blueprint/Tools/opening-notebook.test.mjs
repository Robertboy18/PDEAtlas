// node --test Blueprint/Tools/opening-notebook.test.mjs
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import test from "node:test";
import {
  buildOpeningNotebook, extractDeclaration, insertOpeningNotebook,
} from "./opening-notebook.mjs";

const sourceRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..");
const page = (content) => `<html><head><title>Book</title></head><body>` +
  `<aside><a href="Chapter/#proof">Existing source link</a></aside>` +
  `<main><p>Opening paragraph.</p>${content}<p>Later prose.</p></main></body></html>`;
const marker = '<div data-leanpde-notebook="opening"></div>';
const figure = '<figure data-leanpde-figure="formalization-routes"><svg></svg></figure>';
const notebook = '<section class="leanpde-notebook">Notebook</section>';

test("explicit marker replaces only the empty placeholder, preserving later figures and links", () => {
  const html = page(marker + figure);
  const result = insertOpeningNotebook(html, notebook);
  assert.equal(result.anchor, "explicit marker");
  assert.ok(result.html.includes(`<p>Opening paragraph.</p>${notebook}${figure}<p>Later prose.</p>`));
  assert.ok(result.html.includes('<aside><a href="Chapter/#proof">Existing source link</a></aside>'));
  assert.ok(result.html.includes("opening-notebook.css"));
  assert.ok(result.html.includes("opening-notebook.js"));
  assert.ok(!result.html.includes(marker));
});

test("structural insertion handles reordered attributes and ignores JS, comments and quoted markup", () => {
  const fake = `<script>const s = '${marker}';</script><!-- ${marker} -->`;
  const html = page(fake + `<div title="a > b" data-leanpde-notebook='opening'>\n</div>` + figure);
  const result = insertOpeningNotebook(html, notebook);
  assert.equal(result.anchor, "explicit marker");
  assert.ok(result.html.includes(fake + notebook + figure));
});

test("a figure cannot stand in for the required explicit marker", () => {
  assert.throws(() => insertOpeningNotebook(page(figure), notebook), /exactly one insertion marker/);
});

test("missing, duplicate, nonempty or misplaced anchors are refused", () => {
  for (const content of ["", marker + marker, figure + figure, marker.replace("</div>", "Keep me</div>")]) {
    assert.throws(() => insertOpeningNotebook(page(content), notebook), /Opening notebook:/);
  }
  assert.throws(() => insertOpeningNotebook(
    page("").replace("<main>", marker + "<main>"), notebook), /inside main/);
});

test("source selector refuses ambiguity and records exact lines", () => {
  const declaration = "example : True := by\n  trivial";
  assert.deepEqual(extractDeclaration(`-- lead\n${declaration}\n\n-- tail`, "example : True := by", "test"),
    { firstLine: 2, lastLine: 3, text: declaration });
  assert.throws(() => extractDeclaration("", "example : True := by", "test"), /expected one/);
  assert.throws(() => extractDeclaration(`${declaration}\n\n${declaration}`, "example : True := by", "test"),
    /expected one/);
});

test("published cells and local excerpts match the checkout, with proofs visible before JS", async () => {
  const temporary = await mkdtemp(path.join(os.tmpdir(), "leanpde-notebook-test-"));
  try {
    // This test checks source extraction, not typography. The rendered-page
    // browser check uses the site's actual KaTeX bundle, including without JS.
    const html = await buildOpeningNotebook(temporary, "test-revision", (tex) => tex);
    const directory = path.join(temporary, "leanpde-notebook");
    const manifest = JSON.parse(await readFile(path.join(directory, "sources.json"), "utf8"));
    assert.equal(manifest.examples.length, 3);
    assert.equal((html.match(/class="leanpde-notebook-example"/g) ?? []).length, 3);
    assert.ok(html.includes('aria-label="Choose a worked example" hidden'));
    assert.ok(!/class="leanpde-notebook-example"[^>]*\bhidden\b/.test(html));
    for (const record of manifest.examples) {
      const source = await readFile(path.join(sourceRoot, record.file), "utf8");
      assert.equal(record.sourceSha256, createHash("sha256").update(source).digest("hex"));
      const excerptFile = await readFile(path.join(directory, `${record.id}.txt`), "utf8");
      assert.ok(excerptFile.startsWith("\ufeff"), "Source excerpts identify UTF-8 without HTTP headers");
      for (const excerpt of [...record.excerpts, ...record.supportingExcerpts]) {
        assert.equal(excerpt.text,
          source.split("\n").slice(excerpt.firstLine - 1, excerpt.lastLine).join("\n"));
        assert.ok(excerptFile.includes(excerpt.text));
      }
      assert.ok(html.includes(`href="-verso-data/leanpde-notebook/${record.id}.txt"`));
    }
    assert.match(manifest.examples[0].excerpts.at(-1).text, /Exact\.zeroFn Set\.univ := by\n  cas$/);
    assert.match(manifest.examples[0].supportingExcerpts.at(-1).text,
      /theorem separatedHeatMode1D_analytic_residual_eq_zero :/);
    assert.match(manifest.examples[1].excerpts[0].text, /hx : x \^ 2 - 1 ≠ 0/);
    assert.match(manifest.examples[2].excerpts[0].text, /Set\.Icc.*:= by\n  cega$/);
  } finally {
    await rm(temporary, { recursive: true, force: true });
  }
});
