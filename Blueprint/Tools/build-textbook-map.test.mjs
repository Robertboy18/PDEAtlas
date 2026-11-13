// node --test Blueprint/Tools/build-textbook-map.test.mjs
import assert from "node:assert/strict";
import { execFile } from "node:child_process";
import { copyFile, mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { promisify } from "node:util";
import test from "node:test";
import { textbookMapCitationErrors } from "./textbook-map-citations.mjs";

const run = promisify(execFile);
const tools = path.dirname(fileURLToPath(import.meta.url));
const overview = `
:::source_document "evans-pde"
%%%
title := "Partial Differential Equations"
%%%
:::
:::source_document "other"
%%%
title := "Another source"
%%%
:::
`;

function card(label, spans, document = "evans-pde") {
  return `:::theorem "${label}"
%%%
source := {
  document := "${document}"
  spans := #[${spans}]
}
%%%
A statement.
:::
`;
}

async function generate(source) {
  const temporary = await mkdtemp(path.join(os.tmpdir(), "leanpde-textbook-test-"));
  try {
    await mkdir(path.join(temporary, "Blueprint/Tools"), { recursive: true });
    await mkdir(path.join(temporary, "Blueprint/Chapters"), { recursive: true });
    const generator = path.join(temporary, "Blueprint/Tools/build-textbook-map.mjs");
    await copyFile(path.join(tools, "build-textbook-map.mjs"), generator);
    await writeFile(path.join(temporary, "Blueprint/Chapters/Overview.lean"), overview);
    await writeFile(path.join(temporary, "Blueprint/Chapters/Fixture.lean"), source);
    const json = path.join(temporary, "map.json");
    await run(process.execPath, [generator, "--json", json]);
    const before = await readFile(json, "utf8");
    await run(process.execPath, [generator, "--check", "--json", json]);
    assert.equal(await readFile(json, "utf8"), before);
    return JSON.parse(before);
  } finally {
    await rm(temporary, { recursive: true, force: true });
  }
}

function entries(document) {
  return [
    ...document.units.flatMap((unit) => unit.sections.flatMap((section) => section.cards)),
    ...document.locations.flatMap((location) => location.cards),
    ...document.unplaced,
  ];
}

test("verified second-edition boundaries keep nearby citations in their result sections", async () => {
  const map = await generate(
    card("regularity", '{ page := "487" }')
    + card("control", '{ page := "600" }')
    + card("wave_problems", '{ page := "694" }'),
  );
  const sections = map.documents[0].units.flatMap((unit) => unit.sections);
  for (const [label, number] of [
    ["regularity", "8.3"], ["control", "10.3"], ["wave_problems", "12.6"],
  ]) {
    assert.equal(sections.find((section) => section.cards.some((entry) => entry.label === label)).number,
      number);
  }
  assert.equal(sections.some((section) => section.approx), false);
});

test("page, citation and mixed spans remain distinct, with no invented page", async () => {
  const map = await generate(card("mixed", `{
    page := "75-76"
    citation := "§2.4.2"
    text := some { path := "a{b}.md", startLine := 1, endLine := 9 }
  }, {
    citation := "§2.4.2"
    text := some { path := "a.md", startLine := 1, endLine := 9 }
  }, {
    page := "77"
  }`));
  assert.equal(map.schemaVersion, 2);
  assert.equal(map.summary.citations, 3);
  assert.equal(map.summary.cards, 1);
  const evans = map.documents[0];
  assert.deepEqual(entries(evans).map(({ page, citation }) => ({ page, citation })), [
    { page: "75-76", citation: "§2.4.2" },
    { page: "77", citation: null },
    { page: null, citation: "§2.4.2" },
  ]);
  assert.equal(evans.unplaced.length, 1);
  assert.equal(evans.unplaced[0].label, "mixed");
  assert.equal(evans.unplaced[0].file, "Blueprint/Chapters/Fixture.lean");
  assert.equal(evans.unplaced[0].line, 1);
});

test("non-Evans locations group by both page and citation", async () => {
  const map = await generate(
    card("section", '{ citation := "Theorem 2.1", text := some { path := "a.md", startLine := 1, endLine := 2 } }', "other")
    + card("page", '{ page := "5" }', "other")
    + card("both", '{ citation := "Theorem 2.1", page := "5" }', "other")
    + card("same", '{ citation := "Theorem 2.1", text := some { path := "b.md", startLine := 3, endLine := 4 } }', "other"),
  );
  const locations = map.documents[0].locations;
  assert.equal(locations.length, 3);
  assert.deepEqual(locations.map(({ page, citation }) => ({ page, citation })), [
    { page: "5", citation: null },
    { page: "5", citation: "Theorem 2.1" },
    { page: null, citation: "Theorem 2.1" },
  ]);
  assert.equal(locations[2].cards.length, 2);
});

test("the authored Duhamel citation survives extraction unchanged", async () => {
  const source = await readFile(path.join(tools, "../Chapters/Hyperbolic/ClassicalWave.lean"), "utf8");
  const map = await generate(source);
  const matches = entries(map.documents[0]).filter((entry) => entry.label === "hyperbolic.wave.duhamel_solution");
  assert.equal(matches.length, 1);
  assert.equal(matches[0].page, null);
  assert.equal(matches[0].citation, "§2.4.2");
  assert.match(source.split("\n")[matches[0].line - 1], /^:::theorem "hyperbolic.wave.duhamel_solution"/);
});

test("unknown source documents are still rejected", async () => {
  await assert.rejects(generate(card("bad", '{\n  page := "75"\n}', "unknown")), /not registered/);
});

test("spans without a page or citation are rejected rather than silently omitted", async () => {
  await assert.rejects(generate(card("bad", '{ text := some { path := "a.md", startLine := 1, endLine := 9 } }')), /page or citation/);
  await assert.rejects(generate(card("bad", '{ citation := " " }')), /page or citation/);
});

test("rendered audit preserves section citations and checks every repeated span", () => {
  const cards = [
    { label: "fixture", page: "75", citation: "§2.4.2" },
    { label: "fixture", page: null, citation: "§2.4.2 & Lemma 1" },
  ];
  const hrefs = new Map([["fixture", "/wave/#fixture"]]);
  const page = `<li data-leanpde-map-card="fixture"><a href="/wave/#fixture">fixture</a>
    <span class="leanpde-tm-page">p. 75</span>
    <span class="leanpde-tm-citation">§2.4.2</span></li>`;
  const section = `<li data-leanpde-map-card="fixture"><a href="/wave/#fixture">fixture</a>
    <span class="leanpde-tm-citation">§2.4.2 &amp; Lemma 1</span></li>`;
  const html = page + section;
  assert.deepEqual(textbookMapCitationErrors(cards, html, hrefs), []);
  for (const broken of [
    page, // The unplaced section-only card disappeared.
    html.replace("§2.4.2 &amp; Lemma 1", ""), // Citation text disappeared.
    html.replace('class="leanpde-tm-citation">§2.4.2 &amp; Lemma 1',
      'class="leanpde-tm-page">p. §2.4.2 &amp; Lemma 1'), // A fake page.
    html.replace('href="/wave/#fixture"', 'href="/wrong"'),
    html + section, // Duplicating a span must not inflate the inventory.
  ]) assert.notDeepEqual(textbookMapCitationErrors(cards, broken, hrefs), []);
  assert.notDeepEqual(textbookMapCitationErrors(cards, html, new Map()), []);
});
