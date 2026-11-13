#!/usr/bin/env node

// Post-process the rendered multi-page site.
//
// 1. Vendor Marked and keep the full-text search index off ordinary pages.
// 2. Strip the DOT sources embedded on the atlas page (the views are
//    pre-rendered by `build-dependency-atlas.py`).
// 3. Build the site shell that Verso's page template does not offer: a
//    subtitle under the sidebar title, an "Overview" entry for the landing
//    page, the "Contents" label, and a sidebar footer with the theme button.
//    The revision comes from the build-metadata chips that VersoBlueprint
//    writes into the landing page; LEANPDE_SOURCE_REVISION supplies it when
//    Git metadata is absent. The revision is kept in generated
//    metadata; the chips themselves are removed from the reading view.
//    When LEANPDE_PUBLIC_REPOSITORY_URL names a public repository, the footer
//    links to it. The Lean
//    renderers read the same variable for source references.
// 4. Add a "Proof map" action to every statement card whose group has a
//    pre-rendered atlas view. The atlas page selects a view from the URL hash.
// 5. Supply the page metadata that Verso's template leaves out: the document
//    language, a title that names the page's place in the book (section and
//    chapter, or chapter and book), and a description taken from the first
//    sentence of the page's lead paragraph.
// 6. Continue the page's heading sequence inside the textbook coverage map,
//    whose renderer cannot see the level of the heading above it.
// 7. Insert the Introduction's notebook with excerpts from the checkout's Lean proofs.
//
// Usage: node Blueprint/Tools/optimize-site.mjs <html-multi-dir> <marked.umd.min.js>

import { copyFile, mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { buildOpeningNotebook, insertOpeningNotebook } from "./opening-notebook.mjs";
import { buildLearningFeatures, insertLearningFeatures } from "./learning.mjs";
import { figureMathRenderer } from "./figure-math.mjs";

const [siteArg, markedArg] = process.argv.slice(2);

if (!siteArg || !markedArg) {
  console.error(
    "Usage: node Blueprint/Tools/optimize-site.mjs <html-multi-dir> <marked.umd.min.js>",
  );
  process.exit(2);
}

const siteDir = path.resolve(siteArg);
const markedSource = path.resolve(markedArg);
const dataDir = path.join(siteDir, "-verso-data");
const markedDestination = path.join(dataDir, "marked.min.js");
const sourceRevision = (process.env.LEANPDE_SOURCE_REVISION ?? "").trim();
// The public repository, if there is one. Unset or empty means the repository
// is not public, and nothing in the site shell links to it.
const publicRepositoryUrl = (process.env.LEANPDE_PUBLIC_REPOSITORY_URL ?? "")
  .trim()
  .replace(/\/+$/, "")
  .replace(/\.git$/, "");

// The landing page under its own name: the sidebar's first row and the label on
// the back button of the first chapter, which both lead there.
const landingEntryName = "Overview";
// The same short description accompanies the name in the sidebar and overview.
const siteSubtitle = "Partial differential equations in Lean";
const brandSource = fileURLToPath(new URL("../Assets/Brand/", import.meta.url));
const brandFiles = ["logo-light.webp", "logo-dark.webp", "favicon.png"];
// The heading supplies the accessible name; both image variants are decorative.
const wordmark =
  '<span class="leanpde-wordmark" aria-hidden="true">' +
  '<span>LeanP</span><span class="leanpde-brand-symbol">' +
  ["light", "dark"].map((theme) =>
    `<img class="leanpde-logo-${theme}" src="-verso-data/leanpde-brand/logo-${theme}.webp" ` +
    'width="1352" height="318" alt="" decoding="async">',
  ).join("") +
  '</span><span>E</span></span>';
// The meta description of the landing page.
const landingDescription =
  "LeanPDE develops partial differential equations in Lean 4. Its CAS and CEGA tactics " +
  "produce proofs of symbolic identities and numerical bounds. Explore worked examples " +
  "and the classical, weak, and variational theory behind them.";

const markedCdnTag =
  '<script src="https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js" integrity="sha384-zbcZAIxlvJtNE3Dp5nxLXdXtXyxwOdnILY1TDPVmKFhl4r4nSUG1r8bcFXGVa4Te" crossorigin="anonymous"></script>';
const localMarkedTag =
  '<script defer="defer" src="-verso-data/marked.min.js"></script>';
const elasticlunrTag =
  '    <script defer="defer" src="-verso-search/elasticlunr.min.js"></script>\n';
const searchIndexTag =
  '    <script defer="defer" src="-verso-search/searchIndex.js"></script>\n';

async function collectHtmlFiles(directory) {
  const files = [];
  for (const entry of await readdir(directory, { withFileTypes: true })) {
    const entryPath = path.join(directory, entry.name);
    if (entry.isDirectory()) {
      files.push(...(await collectHtmlFiles(entryPath)));
    } else if (entry.isFile() && entry.name.endsWith(".html")) {
      files.push(entryPath);
    }
  }
  return files;
}

function escapeHtml(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}

function decodeHtml(value) {
  const named = new Map([
    ["amp", "&"],
    ["lt", "<"],
    ["gt", ">"],
    ["quot", '"'],
    ["apos", "'"],
    ["nbsp", "\u00a0"],
  ]);
  return value.replace(/&(#x[0-9a-f]+|#[0-9]+|[a-z]+);/gi, (entity, body) => {
    if (/^#x/i.test(body)) return String.fromCodePoint(Number.parseInt(body.slice(2), 16));
    if (body.startsWith("#")) return String.fromCodePoint(Number.parseInt(body.slice(1), 10));
    return named.get(body.toLowerCase()) ?? entity;
  });
}

function escapeRegExp(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function readTitle(html) {
  const match = html.match(/<title>([\s\S]*?)<\/title>/);
  return match ? match[1].trim() : "";
}

// The chapter a route belongs to, read from the sidebar's chapter list.
function chapterTitleFor(html, chapterSlug) {
  const pattern = new RegExp(
    `<td><a href="${escapeRegExp(chapterSlug)}/#[^"]*">([^<]*)</a></td>`,
  );
  const match = html.match(pattern);
  return match ? match[1].trim() : "";
}

// Section pages are titled by section and chapter, top-level pages by page and
// book; the landing page keeps the book title.
function pageTitle(html, relativePath, bookTitle) {
  const own = readTitle(html);
  const segments = relativePath.split("/");
  if (segments.length <= 1 || !own) return own;
  if (segments.length === 2) return `${own} \u00b7 ${bookTitle}`;
  const chapter = chapterTitleFor(html, segments[0]);
  return `${own} \u00b7 ${chapter || bookTitle}`;
}

function firstSentence(text, limit = 220) {
  const match = text.match(/^[\s\S]*?[.!?](?=\s|$)/);
  let sentence = (match ? match[0] : text).trim();
  if (sentence.length > limit) {
    sentence = sentence.slice(0, limit);
    sentence = sentence.slice(0, Math.max(sentence.lastIndexOf(" "), 1));
  }
  return sentence.trim();
}

// The document's own <main> element. The search starts at <body> because the
// head carries the site's inline scripts, and a script may name the tag in a
// comment or a selector.
function mainRange(html) {
  const body = html.indexOf("<body");
  const open = html.indexOf("<main", body < 0 ? 0 : body);
  const inner = open < 0 ? -1 : html.indexOf(">", open);
  const end = open < 0 ? -1 : html.indexOf("</main", open);
  if (open < 0 || inner < 0 || end < 0) return null;
  return { open, inner: inner + 1, end };
}

// The first sentence of the first paragraph of prose (without mathematics or
// code) on the page. A chapter page has no prose of its own, only its list of
// sections, so it is described by that list. Pages with neither get nothing.
function pageDescription(html, relativePath, bookTitle) {
  if (relativePath === "index.html") return landingDescription;
  const range = mainRange(html);
  const main = range ? html.slice(range.inner, range.end) : "";
  for (const paragraph of main.matchAll(/<p>([\s\S]*?)<\/p>/g)) {
    if (/<code\b/.test(paragraph[1])) continue;
    const text = decodeHtml(paragraph[1].replace(/<[^>]+>/g, "")).replace(/\s+/g, " ").trim();
    if (text.length < 60) continue;
    return firstSentence(text);
  }
  const heading = main.match(/<h1>([\s\S]*?)<\/h1>/);
  const sections = [...main.matchAll(/<ol class="section-toc">([\s\S]*?)<\/ol>/g)]
    .flatMap((list) => [...list[1].matchAll(/<a href="[^"]*">([\s\S]*?)<\/a>/g)])
    .map((link) => decodeHtml(link[1].replace(/<[^>]+>/g, "")).replace(/\s+/g, " ").trim())
    .map((title) => title.replace(/^[0-9.]+\s*/, ""))
    .filter((title) => title.length > 0);
  if (heading && sections.length > 0) {
    const chapter = decodeHtml(heading[1].replace(/<[^>]+>/g, "")).replace(/\s+/g, " ").trim();
    return firstSentence(`${chapter}, a chapter of ${bookTitle}: ${sections.join("; ")}.`, 240);
  }
  return "";
}

function addPageMetadata(html, relativePath, bookTitle) {
  html = html.replace(/<html>/, '<html lang="en">');
  // Permit zoom even when JavaScript is disabled; Verso's viewport caps the scale.
  html = html.replace(
    /<meta\b(?=[^>]*\bname="viewport")[^>]*>/i,
    '<meta name="viewport" content="width=device-width, initial-scale=1">',
  );
  const title = pageTitle(html, relativePath, bookTitle);
  if (title) html = html.replace(/<title>[\s\S]*?<\/title>/, `<title>${title}</title>`);
  const description = pageDescription(html, relativePath, bookTitle);
  if (description) {
    const charset = html.match(/<meta charset="utf-8"\s*\/?>/);
    if (!charset) {
      throw new Error(`${relativePath}: no charset declaration to place the description after.`);
    }
    html = html.replace(
      charset[0],
      `${charset[0]}\n        <meta name="description" content="${escapeHtml(description)}">`,
    );
  }
  return html;
}

// The textbook coverage map renders its Evans-chapter and document headings
// as <h4> whatever heading precedes it. Continue the page's heading sequence.
function continueHeadingSequence(html) {
  if (!/<h[1-6] class="leanpde-tm-/.test(html)) return html;
  let previousLevel = 0;
  return html.replace(
    /<h([1-6])( class="leanpde-tm-[^"]*")?([^>]*)>([\s\S]*?)<\/h\1>/g,
    (whole, level, mapClass, attributes, body) => {
      if (!mapClass) {
        previousLevel = Number.parseInt(level, 10);
        return whole;
      }
      const target = Math.min(6, Math.max(2, previousLevel + 1));
      return `<h${target}${mapClass}${attributes}>${body}</h${target}>`;
    },
  );
}

// A single button cycles through the three preferences. The head script sets
// the initial theme before painting; the page script labels and enables it.
function themeControlHtml() {
  return (
    '<button type="button" class="leanpde-theme"' +
    ' aria-label="Theme: system. Switch to light theme.">Theme: system</button>'
  );
}

// The reading-progress line and the corner readout, which doubles as the way
// back to the top. Both start hidden; the page script shows them on a page that
// is taller than the window.
function readingShellHtml() {
  return (
    '<div class="leanpde-progress" hidden="hidden" aria-hidden="true">' +
    '<div class="leanpde-progress-fill"></div>' +
    "</div>" +
    '<button type="button" class="leanpde-top" hidden="hidden" data-leanpde-shown="false"' +
    ' data-leanpde-clear="true" aria-label="Back to the top of the page">' +
    '<span class="leanpde-top-pct" aria-hidden="true">0%</span>' +
    '<span class="leanpde-top-arrow" aria-hidden="true">↑</span>' +
    "</button>"
  );
}

function addReadingShell(html, relativePath) {
  const at = html.lastIndexOf("</body>");
  if (at < 0) {
    throw new Error(`${relativePath}: no </body> to place the reading progress in.`);
  }
  return html.slice(0, at) + readingShellHtml() + html.slice(at);
}

// The headings of one page, in document order, as the rail and the sidebar need
// them: the anchor, the section number that Verso writes into the heading text,
// and the title without it. Headings without an id cannot be linked to and are
// left out; the coverage map's headings are the ones that have none.
function pageSections(html, relativePath) {
  const range = mainRange(html);
  if (!range) {
    throw new Error(`${relativePath}: no <main> element.`);
  }
  const main = html.slice(range.inner, range.end);
  const sections = [];
  for (const heading of main.matchAll(/<h([2-4])\b([^>]*)>([\s\S]*?)<\/h\1>/g)) {
    const id = /\bid="([^"]*)"/.exec(heading[2]);
    if (!id) continue;
    const text = decodeHtml(
      heading[3]
        .split('<span class="permalink-widget')[0]
        // Drop KaTeX's MathML twin so a heading with mathematics in it does not
        // read as the TeX source followed by the rendered glyphs.
        .replace(/<span class="katex-mathml">[\s\S]*?<\/math><\/span>/g, "")
        .replace(/<[^>]+>/g, ""),
    )
      .replace(/\s+/g, " ")
      .trim();
    const numbered = /^((?:\d+\.)+)\s*([\s\S]*)$/.exec(text);
    sections.push({
      level: Number.parseInt(heading[1], 10),
      id: id[1],
      number: numbered ? numbered[1] : "",
      title: numbered ? numbered[2] : text,
    });
  }
  return sections;
}

// Past forty entries a rail is a wall of text, so the deepest level is dropped
// until it fits. A chapter of forty sections keeps all forty: they are the
// coarsest level there is.
function railSections(sections) {
  let deepest = 4;
  while (deepest > 2 && sections.filter((section) => section.level <= deepest).length > 40) {
    deepest -= 1;
  }
  return sections.filter((section) => section.level <= deepest);
}

// "On this page", as the first child of <main> so that a narrow screen reads it
// before the text and a wide screen can put it in a column of its own.
function sectionRailHtml(sections, chapterTitle, routePrefix) {
  const items = sections.map((section) => {
    const number = section.number
      ? `<span class="leanpde-rail-num">${escapeHtml(section.number)}</span>`
      : "";
    return (
      `<li class="leanpde-rail-item leanpde-rail-level-${section.level}"` +
      ` data-leanpde-target="${escapeHtml(section.id)}"` +
      ` data-leanpde-short="${escapeHtml(section.title)}">` +
      `<a href="${escapeHtml(routePrefix)}#${escapeHtml(section.id)}">` +
      `${number}${escapeHtml(section.title)}</a></li>`
    );
  });
  const count = `${sections.length} section${sections.length === 1 ? "" : "s"}`;
  return (
    '<nav class="leanpde-rail" data-leanpde-open="false" aria-labelledby="leanpde-rail-label">' +
    '<div class="leanpde-rail-box">' +
    (chapterTitle ? `<p class="leanpde-rail-chapter">${escapeHtml(chapterTitle)}</p>` : "") +
    '<p class="leanpde-rail-head">' +
    '<span class="leanpde-rail-label" id="leanpde-rail-label">On this page</span>' +
    '<span class="leanpde-rail-here" aria-hidden="true"></span>' +
    '<button type="button" class="leanpde-rail-toggle" hidden="hidden" aria-expanded="false"' +
    ' aria-controls="leanpde-rail-list">' +
    `<span>${count}</span><span class="leanpde-rail-chevron" aria-hidden="true">▾</span>` +
    "</button>" +
    "</p>" +
    `<ul class="leanpde-rail-list" id="leanpde-rail-list">${items.join("")}</ul>` +
    "</div></nav>"
  );
}

function addSectionRail(html, sections, chapterTitle, routePrefix, relativePath) {
  if (sections.length < 2) return html;
  const range = mainRange(html);
  if (!range) {
    throw new Error(`${relativePath}: no <main> to place the section rail in.`);
  }
  const at = range.inner;
  return html.slice(0, at) + sectionRailHtml(sections, chapterTitle, routePrefix) + html.slice(at);
}

// Verso renders the previous and next buttons for the root part as a live-looking
// link to nowhere, and labels them with the root title, which carries the space
// that separated it from an absent section number. Going back from the first
// chapter belongs on the landing page, under the name the sidebar gives it; the
// full title stays available in the tooltip. Chapter buttons use the same
// short labels as the sidebar. The last chapter has no forward button.
function fixPrevNextButtons(html, bookTitle) {
  const chapterLabels = new Map(
    [...html.matchAll(/<tr class="numbered"><td class="num">([^<]+)<\/td><td><a href="([^"]+)">([^<]*)<\/a><\/td><\/tr>/g)]
      .map((row) => [decodeHtml(row[2]), `${decodeHtml(row[1]).trim()} ${decodeHtml(row[3]).trim()}`]),
  );
  let repaired = 0;
  const result = html.replace(/<nav class="prev-next-buttons">[\s\S]*?<\/nav>/g, (nav) =>
    nav.replace(/<a\b([^>]*)>([\s\S]*?)<\/a>/g, (anchor, attributes, body) => {
      const rel = /\brel="(prev|next)"/.exec(attributes);
      if (!rel) return anchor;
      const dead = /\bhref="#?"/.test(attributes);
      if (dead && rel[1] === "next") {
        repaired += 1;
        return "<div></div>";
      }
      let head = attributes;
      let label = body;
      if (dead) {
        head = head.replace(/\bhref="#?"/, 'href="index.html"');
        head = head.replace(/\btitle="[^"]*"/, `title="${escapeHtml(bookTitle)}"`);
        label = label.replace(
          /(<span class="where">)[\s\S]*?(<\/span>)/,
          `$1${escapeHtml(landingEntryName)}$2`,
        );
      }
      if (!dead) {
        const href = /\bhref="([^"]*)"/.exec(attributes)?.[1];
        const shortLabel = chapterLabels.get(decodeHtml(href ?? ""));
        if (shortLabel) {
          label = label.replace(
            /(<span class="where">)[\s\S]*?(<\/span>)/,
            (whole, open, close) => open + escapeHtml(shortLabel) + close,
          );
        }
      }
      const trimmedHead = head.replace(
        /\btitle="([^"]*)"/,
        (whole, value) => `title="${value.trim()}"`,
      );
      const trimmedLabel = label.replace(
        /(<span class="where">)([\s\S]*?)(<\/span>)/,
        (whole, open, text, close) => open + text.trim() + close,
      );
      if (trimmedHead !== attributes || trimmedLabel !== body) repaired += 1;
      return `<a${trimmedHead}>${trimmedLabel}</a>`;
    }),
  );
  return { html: result, repaired };
}

// The atlas page embeds Verso's graph JSON, including the DOT source of every
// render variant, for the in-browser renderer. LeanPDE renders those variants
// offline (`Blueprint/Tools/build-dependency-atlas.py`), so the DOT strings are dead
// weight on the page; the manifest keeps them for audits and standalone clients.
function stripAtlasDotSources(html) {
  const pattern =
    /(<script type="application\/json" class="bp-graph-data">)([\s\S]*?)(<\/script>)/g;
  let stripped = 0;
  const result = html.replace(pattern, (whole, open, body, close) => {
    let data;
    try {
      data = JSON.parse(body);
    } catch (error) {
      throw new Error(`Malformed embedded graph JSON on the atlas page: ${error.message}`);
    }
    if (!Array.isArray(data.variants)) return whole;
    for (const variant of data.variants) {
      if (typeof variant.dot === "string") {
        stripped += variant.dot.length;
        variant.dot = "";
      }
    }
    data.leanpdePrerenderedVariants = true;
    return open + JSON.stringify(data) + close;
  });
  return { html: result, stripped };
}

// VersoBlueprint writes one block of build-metadata chips into the landing
// page, after the title. Read the project revision from it.
function readBuildMetadata(rootHtml) {
  const block = rootHtml.match(/\n?<div class="bp_build_metadata"[^>]*>[\s\S]*?<\/div>\n?/);
  if (!block) {
    throw new Error("The landing page carries no build-metadata block.");
  }
  const project = block[0].match(
    /(?:<span class="bp_build_metadata_label">|<a class="bp_build_metadata_label bp_build_metadata_link" href="([^"]*)">)Project<\/(?:span|a)>\s*(?:<a class="bp_build_metadata_commit_link" href="([^"]*)">)?<code class="bp_build_metadata_commit">([^<]*)<\/code>/,
  );
  if (!project) {
    throw new Error("The build-metadata block names no project revision.");
  }
  const [, repositoryUrl, commitUrl, commit] = project;
  return {
    block: block[0],
    repositoryUrl: repositoryUrl || null,
    commitUrl: commitUrl || null,
    commit: commit.trim(),
  };
}

// The repository URL of the build metadata (the clone's `origin`) is not used
// for links: a clone can name a repository that is not public. Only the URL
// given through the environment is.
function shellLinks(metadata) {
  const repositoryUrl = /^https:\/\//.test(publicRepositoryUrl) ? publicRepositoryUrl : null;
  const metadataIsRevision = /^[0-9a-f]{7,40}$/.test(metadata.commit);
  const suppliedIsRevision = /^[0-9a-f]{7,40}$/.test(sourceRevision);
  const commit = metadataIsRevision
    ? metadata.commit
    : suppliedIsRevision
      ? sourceRevision
      : metadata.commit;
  return { repositoryUrl, commit };
}

function sidebarFooterHtml(links) {
  const repository = links.repositoryUrl
    ? `<p class="leanpde-toc-links"><a href="${escapeHtml(links.repositoryUrl)}">Repository</a></p>`
    : "";
  return (
    '<div class="leanpde-toc-footer">' +
    themeControlHtml() +
    repository +
    "</div>"
  );
}

// Site shell of one page: logo, subtitle, "Contents" label, "Overview" entry and
// the footer. Every page uses Verso's template, so each replacement must apply
// exactly once.
function buildSiteShell(html, relativePath, footer) {
  const isLanding = relativePath === "index.html";
  const replaceOnce = (source, pattern, replacement, what) => {
    const result = source.replace(pattern, replacement);
    if (result === source) {
      throw new Error(`${relativePath}: could not place the ${what}.`);
    }
    return result;
  };
  if (isLanding) {
    // Keep the generated heading and its permalink, including the stable tag.
    html = replaceOnce(
      html,
      /(<div class="titlepage">\s*<h1\b[^>]*>)\s*LeanPDE([\s\S]*?<\/h1>)/,
      `$1<span class="leanpde-brand-name">LeanPDE</span>${wordmark}$2` +
        `<p class="leanpde-title-subtitle">${escapeHtml(siteSubtitle)}</p>`,
      "overview logo and subtitle",
    );
    html = replaceOnce(
      html,
      /(<div class="authors">[\s\S]*?<\/div>)/,
      '$1<p class="leanpde-affiliation">California Institute of Technology (Caltech)</p>',
      "authors' affiliation",
    );
  }
  // Verso's find page is a redirect utility with its own title.
  if (relativePath !== "find/index.html") {
    for (const titleClass of ["toc-title", "header-title"]) {
      html = replaceOnce(
        html,
        new RegExp(`(<a href="[^"]*" class="${titleClass}"><h1>)\\s*LeanPDE(</h1>)`),
        `$1<span class="leanpde-brand-name">LeanPDE</span>${wordmark}$2`,
        `${titleClass} logo`,
      );
    }
  }
  html = replaceOnce(
    html,
    /(<a href="[^"]*" class="toc-title">[\s\S]*?<\/a>)/,
    `$1<p class="leanpde-toc-subtitle">${escapeHtml(siteSubtitle)}</p>`,
    "sidebar subtitle",
  );
  html = replaceOnce(
    html,
    /(<div class="split-toc book">[\s\S]*?<span class="">)Table of Contents(<\/span>)/,
    "$1Contents$2",
    "Contents label",
  );
  // Verso collapses the chapter list on any route below a chapter and expands
  // that chapter's section list in its place. Listing the sections is the rail's
  // job, so the chapter list stays open on every route; the label that would
  // close it is hidden by the stylesheet.
  const chapterList = /<input type="checkbox" class="toggle-split-toc" id="[^"]*bookRoot"[^>]*>/;
  if (!chapterList.test(html)) {
    throw new Error(`${relativePath}: the sidebar has no chapter list to open.`);
  }
  html = html.replace(chapterList, (tag) =>
    tag.includes("checked") ? tag : tag.replace(/>$/, ' checked="checked">'),
  );
  const landingClass = isLanding
    ? "unnumbered leanpde-toc-preface current"
    : "unnumbered leanpde-toc-preface";
  html = replaceOnce(
    html,
    /(<div class="split-toc book">[\s\S]*?<table>)/,
    `$1<tr class="${landingClass}"><td class="num"></td><td>` +
      `<a href="">${escapeHtml(landingEntryName)}</a></td></tr>`,
    "Overview entry",
  );
  html = replaceOnce(
    html,
    /(<div class="last">)([\s\S]*?)(<\/div>\s*<\/nav>)/,
    `$1$2${footer}$3`,
    "sidebar footer",
  );
  return html;
}

// Index of the `</div>` that closes the `<div` opening at `openIndex`.
function closingDivIndex(html, openIndex) {
  const tags = /<div\b|<\/div>/g;
  tags.lastIndex = openIndex;
  let depth = 0;
  for (let match; (match = tags.exec(html)); ) {
    if (match[0] === "<div") {
      depth += 1;
    } else {
      depth -= 1;
      if (depth === 0) return match.index;
    }
  }
  throw new Error("Unbalanced <div> while looking for the end of a card header.");
}

// Append the "Proof map" action to the header chips of every statement card
// whose group has a pre-rendered atlas view.
function addProofMapActions(html, groupOfCard, atlasViews) {
  const wrappers =
    /<div class="bp_wrapper bp_kind_(?:theorem|definition)_wrapper[^"]*" title="«([^»]+)»" id="[^"]*--statement">/g;
  let result = "";
  let cursor = 0;
  let added = 0;
  const skipped = [];
  for (const match of html.matchAll(wrappers)) {
    const label = match[1];
    const group = groupOfCard.get(label);
    const viewKey = group ? `parent:«${group}»` : "";
    if (!viewKey || !atlasViews.has(viewKey)) {
      skipped.push(label);
      continue;
    }
    const extrasStart = html.indexOf('<div class="bp_extras', match.index);
    const nextCard = html.indexOf('<div class="bp_wrapper', match.index + match[0].length);
    if (extrasStart < 0 || (nextCard >= 0 && extrasStart > nextCard)) {
      throw new Error(`${label}: statement card without header chips.`);
    }
    const extrasEnd = closingDivIndex(html, extrasStart);
    const href = `Dependency-Atlas/#view=${encodeURIComponent(viewKey)}`;
    const slot =
      '<span class="bp_extra_slot leanpde-extra-slot-map">' +
      `<a class="leanpde-proof-map" href="${href}" title="Open the dependency atlas at the group of this card">Proof map</a>` +
      "</span>";
    result += html.slice(cursor, extrasEnd) + slot;
    cursor = extrasEnd;
    added += 1;
  }
  return { html: result + html.slice(cursor), added, skipped };
}

// Name the chapter heading after the section it is.
//
// Verso gives an id to every heading it renders inside a page, but the heading a
// page is named after gets none: the chapter title on `Foundations/index.html`
// carries no `id`, while the sidebar, the table of contents and every citation
// back-link address it as `Foundations/#CEGA___-...--Foundations`. On separate
// short routes that hardly showed, since the link still opened the right page at
// the top. On one continuous chapter it means clicking the chapter in the sidebar
// leaves the reader wherever they were. The name is not guessed: the permalink
// widget beside the heading already spells it out.
function nameOwnHeading(html) {
  const permalink = /find\/\?domain=Verso\.Genre\.Manual\.section&amp;name=([^"&]+)"/;
  const ids = new Set([...html.matchAll(/\sid="([^"]+)"/g)].map((match) => match[1]));
  let named = 0;
  const result = html.replace(/<h1([^>]*)>([\s\S]*?)<\/h1>/g, (whole, attributes, body) => {
    if (/\bid="/.test(attributes)) return whole;
    const name = permalink.exec(body);
    if (!name) return whole;
    const id = decodeURIComponent(name[1]);
    // Verso may already put this anchor on the enclosing section.
    if (ids.has(id)) return whole;
    ids.add(id);
    named += 1;
    return `<h1${attributes} id="${id}">${body}</h1>`;
  });
  return { html: result, named };
}

// Point a same-page fragment link at the page's own route.
//
// Verso gives every page `<base href="./../">`, and a fragment-only URL resolves
// against the base, not against the document that carries it: `href="#x"` on a
// chapter page sends the reader to the landing page rather than to `#x` a few
// paragraphs down. Certified plots write one such link per bar, so clicking a bar
// to read its theorem left the chapter entirely. Repeating the route in front of
// the fragment resolves it back to this page. Fragments that name nothing here are
// left alone: the atlas `#view=` state hashes are read by its script, and the
// citation back-link on the bibliography page really does point at the landing page.
function anchorLocalFragments(html, routePrefix) {
  if (!routePrefix) return { html, repointed: 0 };
  const ids = new Set([...html.matchAll(/\s(?:id|name)="([^"]+)"/g)].map((match) => match[1]));
  let repointed = 0;
  const result = html.replace(/href="#([^"]+)"/g, (whole, fragment) => {
    let decoded = fragment;
    try {
      decoded = decodeURIComponent(fragment);
    } catch (_err) {
      decoded = fragment;
    }
    if (!ids.has(fragment) && !ids.has(decoded)) return whole;
    repointed += 1;
    return `href="${routePrefix}#${fragment}"`;
  });
  return { html: result, repointed };
}

await mkdir(dataDir, { recursive: true });
await copyFile(markedSource, markedDestination);
await mkdir(path.join(dataDir, "leanpde-brand"), { recursive: true });
for (const filename of brandFiles) {
  await copyFile(path.join(brandSource, filename), path.join(dataDir, "leanpde-brand", filename));
}

const cardIndex = JSON.parse(await readFile(path.join(dataDir, "leanpde-cards.json"), "utf8"));
const groupOfCard = new Map(
  Object.entries(cardIndex.cards ?? {}).map(([label, entry]) => [label, entry.g ?? ""]),
);
const atlasIndex = JSON.parse(
  await readFile(path.join(dataDir, "leanpde-dependency-atlas.json"), "utf8"),
);
const atlasViews = new Set((atlasIndex.variants ?? []).map((variant) => variant.key));

const htmlFiles = await collectHtmlFiles(siteDir);
const landingPath = path.join(siteDir, "index.html");
const landingHtml = await readFile(landingPath, "utf8");
const bookTitle = readTitle(landingHtml);
if (!bookTitle) {
  throw new Error("The landing page has no <title>.");
}
const metadata = readBuildMetadata(landingHtml);
const links = shellLinks(metadata);
const footer = sidebarFooterHtml(links);
const notebook = await buildOpeningNotebook(dataDir, links.commit);
const learning = await buildLearningFeatures(dataDir);
const introductionPath = path.join(siteDir, "Introduction/index.html");
const introductionHtml = await readFile(introductionPath, "utf8");
const opening = insertOpeningNotebook(introductionHtml, notebook);
const typesetFigures = await figureMathRenderer(siteDir);

let lightweightPages = 0;
let mathLabels = 0;
let captionEquations = 0;
let strippedDotBytes = 0;
let proofMapActions = 0;
let describedPages = 0;
let railedPages = 0;
let repairedButtons = 0;
let repointedFragments = 0;
let namedHeadings = 0;
const skippedCards = new Set();

for (const htmlFile of htmlFiles) {
  const relativePath = path.relative(siteDir, htmlFile).split(path.sep).join("/");
  const isSearchPage = relativePath === "search/index.html";
  const routePrefix = relativePath.replace(/index\.html$/, "");
  let html = await readFile(htmlFile, "utf8");
  if (htmlFile === introductionPath) html = opening.html;
  html = insertLearningFeatures(html, learning);
  const figures = typesetFigures(html, relativePath);
  html = figures.html;
  mathLabels += figures.labels;
  captionEquations += figures.captionEquations;

  if (!html.includes(markedCdnTag)) {
    throw new Error(`Missing expected Marked CDN tag in ${relativePath}`);
  }
  html = html.replace(markedCdnTag, localMarkedTag);

  if (!isSearchPage) {
    if (!html.includes(elasticlunrTag) || !html.includes(searchIndexTag)) {
      throw new Error(`Missing expected full-text search assets in ${relativePath}`);
    }
    html = html.replace(elasticlunrTag, "").replace(searchIndexTag, "");
    lightweightPages += 1;
  }

  if (relativePath === "Dependency-Atlas/index.html") {
    const atlas = stripAtlasDotSources(html);
    if (atlas.stripped === 0) {
      throw new Error("The atlas page carries no embedded DOT sources to strip.");
    }
    html = atlas.html;
    strippedDotBytes = atlas.stripped;
  }

  if (relativePath === "index.html") {
    html = html.replace(metadata.block, "\n");
  }
  html = buildSiteShell(html, relativePath, footer);
  html = addPageMetadata(html, relativePath, bookTitle);
  if (html.includes('<meta name="description"')) describedPages += 1;
  html = continueHeadingSequence(html);

  const buttons = fixPrevNextButtons(html, bookTitle);
  html = buttons.html;
  repairedButtons += buttons.repaired;

  // After the heading levels are settled, so the rail reads the levels the
  // reader sees, and after the description, so it reads the page's own prose.
  if (!isSearchPage && relativePath !== "find/index.html") {
    const segments = relativePath.split("/");
    const sections = railSections(pageSections(html, relativePath));
    if (sections.length >= 2) {
      const chapter = segments.length > 1 ? chapterTitleFor(html, segments[0]) : "";
      html = addSectionRail(html, sections, chapter, routePrefix, relativePath);
      railedPages += 1;
    }
  }
  html = addReadingShell(html, relativePath);

  const actions = addProofMapActions(html, groupOfCard, atlasViews);
  html = actions.html;
  proofMapActions += actions.added;
  for (const label of actions.skipped) skippedCards.add(label);

  const named = nameOwnHeading(html);
  html = named.html;
  namedHeadings += named.named;

  const local = anchorLocalFragments(html, routePrefix);
  html = local.html;
  repointedFragments += local.repointed;

  await writeFile(htmlFile, html);
}

console.log(
  `Blueprint site optimization: ${lightweightPages} pages use lightweight title search; ` +
    "full-text search remains on search/index.html; " +
    `${strippedDotBytes.toLocaleString("en-US")} bytes of pre-rendered DOT removed from the atlas page; ` +
    `site shell built from revision ${links.commit} on ${htmlFiles.length} pages; ` +
    `${describedPages} pages carry a description; ` +
    `${railedPages} pages carry a section rail; ` +
    `${repairedButtons} chapter buttons repaired; ` +
    `${proofMapActions} Proof map actions added; ` +
    `${repointedFragments} same-page links repointed at their own route; ` +
    `${mathLabels} diagram labels and ${captionEquations} caption equations typeset; ` +
    `Introduction notebook inserted at ${opening.anchor}; ` +
    `${namedHeadings} page headings named after their own section` +
    `${skippedCards.size > 0 ? ` (${skippedCards.size} cards without a group view)` : ""}.`,
);
