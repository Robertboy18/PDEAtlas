// Typeset diagram equations at build time, using the KaTeX bundled with Verso.
// The SVG keeps the drawing's coordinate system; the HTML label supplies real
// fractions, integrals, and scripts, together with KaTeX's MathML alternative.

import { readFile } from "node:fs/promises";
import path from "node:path";
import vm from "node:vm";

function escapeHtml(value) {
  return String(value).replaceAll("&", "&amp;").replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;").replaceAll('"', "&quot;");
}

function decodeHtml(value) {
  const named = { amp: "&", lt: "<", gt: ">", quot: '"', apos: "'", nbsp: "\u00a0" };
  return value.replace(/&(#x[0-9a-f]+|#[0-9]+|[a-z]+);/gi, (entity, body) => {
    if (/^#x/i.test(body)) return String.fromCodePoint(parseInt(body.slice(2), 16));
    if (body.startsWith("#")) return String.fromCodePoint(parseInt(body.slice(1), 10));
    return named[body.toLowerCase()] ?? entity;
  });
}

export async function figureMathRenderer(siteDir) {
  const context = vm.createContext({});
  vm.runInContext(await readFile(path.join(siteDir, "-verso-data/katex/katex.js"), "utf8"), context);
  const katex = context.katex;
  if (typeof katex?.renderToString !== "function") throw new Error("Missing figure KaTeX renderer.");
  const cache = new Map();
  const render = (tex) => {
    if (!cache.has(tex)) {
      cache.set(tex, katex.renderToString(tex, {
        throwOnError: true,
        strict: "error",
        trust: false,
        output: "htmlAndMathml",
        displayMode: false,
      }));
    }
    return cache.get(tex);
  };

  return (html, page) => {
    let labels = 0;
    let captionEquations = 0;
    html = html.replace(/<figure\b[^>]*class="leanpde-fig"[^>]*>[\s\S]*?<\/figure>/g, (figure) => {
      const id = figure.match(/data-leanpde-figure="([^"]+)"/)?.[1] ?? page;
      try {
        figure = figure.replace(/<text\b([^>]*\bdata-leanpde-tex="[^"]*"[^>]*)>([\s\S]*?)<\/text>/g,
          (_, attributeText, body) => {
            const attrs = Object.fromEntries([...attributeText.matchAll(/([\w:-]+)="([^"]*)"/g)]
              .map((m) => [m[1], decodeHtml(m[2])]));
            const tex = attrs["data-leanpde-tex"];
            const x = Number(attrs.x);
            const y = Number(attrs.y);
            const size = Number(attrs["font-size"]);
            if (![x, y, size].every(Number.isFinite) || size <= 0) {
              throw new Error(`Invalid math label position or font size: ${tex}`);
            }
            const anchor = { start: "0%", middle: "-50%", end: "-100%" }[attrs["text-anchor"] ?? "start"];
            if (!anchor) throw new Error(`Unknown math label anchor: ${attrs["text-anchor"]}`);
            // SVG text is positioned on its baseline. Center the HTML box near
            // the original x-height; its own layout makes room for tall math.
            const top = Math.round((y - 0.35 * size) * 1000) / 1000;
            const classes = (attrs.class ?? "").split(/\s+/).filter((c) => c && c !== "lfh");
            classes.push("lf-math-label");
            const halo = (attrs.class ?? "").split(/\s+/).includes("lfh") ? " lf-math-halo" : "";
            const inherited = ["transform", "opacity", "fill-opacity"].filter((key) => key in attrs)
              .map((key) => ` ${key}="${escapeHtml(attrs[key])}"`).join("");
            const animations = [...body.matchAll(/<animate(?:Transform)?\b[\s\S]*?<\/animate(?:Transform)?>/g)]
              .map((m) => m[0]).join("");
            labels += 1;
            // In an HTML document, foreignObject children enter the HTML
            // namespace. Keep SMIL beside the label and target it explicitly,
            // so the browser parses the animation as an SVG element.
            const target = animations ? `lf-${id}-math-${labels}` : "";
            const targetAttr = target ? ` id="${escapeHtml(target)}"` : "";
            const targetedAnimations = animations.replace(/<(animate(?:Transform)?)\b/g,
              `<$1 href="#${escapeHtml(target)}"`);
            return `<foreignObject class="${classes.join(" ")}" x="${x}" y="${top}" width="1" height="1"` +
              ` data-leanpde-math="${escapeHtml(tex)}"${targetAttr}${inherited}>` +
              `<div xmlns="http://www.w3.org/1999/xhtml" class="lf-math${halo}"` +
              ` style="font-size:${size}px;--lf-math-anchor:${anchor}">${render(tex)}</div>` +
              `</foreignObject>${targetedAnimations}`;
          });
        figure = figure.replace(/(<figcaption\b[^>]*>)([\s\S]*?)(<\/figcaption>)/g,
          (_, open, caption, close) => {
            if (/\\[()]/.test(caption.replace(/\\\([\s\S]*?\\\)/g, ""))) {
              throw new Error("Unpaired caption math delimiter.");
            }
            caption = caption.replace(/\\\(([\s\S]*?)\\\)/g, (_, encoded) => {
              captionEquations += 1;
              const tex = decodeHtml(encoded);
              return `<span class="lf-caption-math" data-leanpde-math="${escapeHtml(tex)}">${render(tex)}</span>`;
            });
            return open + caption + close;
          });
        if (figure.includes("data-leanpde-tex=")) throw new Error("Unrendered mathematical label.");
        return figure;
      } catch (error) {
        throw new Error(`Figure ${id} in ${page}: ${error.message}`, { cause: error });
      }
    });
    return { html, labels, captionEquations };
  };
}
