/*!
Shared HTML scanning helpers for the deferral step.

The rendered blueprint is large, well-formed HTML that we rewrite by byte offset rather
than by parsing into a DOM: a 7 MB page holds around 60,000 spans, and every DOM library
we tried needs more than a gigabyte to hold one chapter. Offsets also let us leave the
bytes we do not touch exactly as Verso emitted them, which matters because two audits
match on literal substrings of the generated markup.

Two things make a naive regex scan wrong, and both occur in this site:

  * `>` appears inside quoted attribute values, for example
    `data-bp-preview-footer-html="<span title=&quot;Declared&quot;>"`, so a start tag
    cannot be found with `<span[^>]*>`.
  * `<` appears inside inline `<script>` bodies as a comparison operator, and
    `.bp_relation_panel` appears inside `<style>` bodies as a selector, so raw-text
    element contents must be skipped rather than scanned.

`scanElements` handles both.
*/

const VOID_ELEMENTS = new Set([
  "area", "base", "br", "col", "embed", "hr", "img", "input",
  "link", "meta", "param", "source", "track", "wbr",
]);

const RAW_TEXT_ELEMENTS = new Set(["script", "style", "textarea", "title"]);

/** Parse the attribute region of a start tag into ordered descriptors. */
export function parseAttributes(html, from, to) {
  const attrs = [];
  let i = from;
  while (i < to) {
    const ch = html[i];
    if (ch === " " || ch === "\t" || ch === "\n" || ch === "\r" || ch === "\f" || ch === "/") {
      i += 1;
      continue;
    }
    const start = i;
    while (i < to && !/[\s/=>]/.test(html[i])) i += 1;
    const name = html.slice(start, i).toLowerCase();
    while (i < to && /\s/.test(html[i])) i += 1;
    if (html[i] !== "=") {
      attrs.push({ name, value: "", quote: "", start, end: i });
      continue;
    }
    i += 1;
    while (i < to && /\s/.test(html[i])) i += 1;
    const quote = html[i] === '"' || html[i] === "'" ? html[i] : "";
    let value;
    if (quote) {
      const close = html.indexOf(quote, i + 1);
      const stop = close === -1 || close > to ? to : close;
      value = html.slice(i + 1, stop);
      i = stop + 1;
    } else {
      const vstart = i;
      while (i < to && !/\s/.test(html[i])) i += 1;
      value = html.slice(vstart, i);
    }
    attrs.push({ name, value, quote, start, end: i });
  }
  return attrs;
}

function attrRegionEnd(html, tagStart) {
  // Returns the index of the `>` that closes the start tag at `tagStart`.
  let i = tagStart + 1;
  while (i < html.length && !/[\s/>]/.test(html[i])) i += 1;
  while (i < html.length) {
    const ch = html[i];
    if (ch === ">") return i;
    if (ch === '"' || ch === "'") {
      const close = html.indexOf(ch, i + 1);
      if (close === -1) return -1;
      i = close + 1;
      continue;
    }
    i += 1;
  }
  return -1;
}

/**
 * Walk every element in `html` and call `onElement` once per element, when its end is
 * known, so children are reported before their parents.
 *
 * The visitor receives `{ name, tagStart, tagEnd, contentStart, contentEnd, end, depth }`
 * where `tagEnd === contentStart` is the offset just past the start tag's `>`, and
 * `contentEnd === end` for void and self-closed elements. `attrs()` parses the start tag
 * lazily so that scanning a page costs one pass and no allocation per uninteresting tag.
 */
export function scanElements(html, onElement) {
  const stack = [];
  let i = 0;
  const len = html.length;
  while (i < len) {
    const lt = html.indexOf("<", i);
    if (lt === -1) break;
    const next = html[lt + 1];
    if (next === "!") {
      if (html.startsWith("<!--", lt)) {
        const close = html.indexOf("-->", lt + 4);
        i = close === -1 ? len : close + 3;
      } else {
        const close = html.indexOf(">", lt);
        i = close === -1 ? len : close + 1;
      }
      continue;
    }
    if (next === "?") {
      const close = html.indexOf(">", lt);
      i = close === -1 ? len : close + 1;
      continue;
    }
    if (next === "/") {
      let j = lt + 2;
      while (j < len && !/[\s>]/.test(html[j])) j += 1;
      const name = html.slice(lt + 2, j).toLowerCase();
      const close = html.indexOf(">", j);
      const after = close === -1 ? len : close + 1;
      i = after;
      if (!name) continue;
      // Tolerate stray close tags and unclosed elements: find the nearest open element
      // with this name and discard anything opened inside it.
      let at = -1;
      for (let k = stack.length - 1; k >= 0; k -= 1) {
        if (stack[k].name === name) { at = k; break; }
      }
      if (at === -1) continue;
      const open = stack[at];
      stack.length = at;
      onElement({
        name,
        tagStart: open.tagStart,
        tagEnd: open.tagEnd,
        contentStart: open.tagEnd,
        contentEnd: lt,
        end: after,
        depth: stack.length,
        attrs: () => parseAttributes(html, open.attrStart, open.attrEnd),
        startTag: () => html.slice(open.tagStart, open.tagEnd),
      });
      continue;
    }
    if (!/[a-zA-Z]/.test(next ?? "")) {
      i = lt + 1;
      continue;
    }
    let j = lt + 1;
    while (j < len && !/[\s/>]/.test(html[j])) j += 1;
    const name = html.slice(lt + 1, j).toLowerCase();
    const gt = attrRegionEnd(html, lt);
    if (gt === -1) break;
    const selfClosed = html[gt - 1] === "/";
    const tagEnd = gt + 1;
    if (RAW_TEXT_ELEMENTS.has(name)) {
      const closeRe = new RegExp(`</${name}\\s*>`, "i");
      closeRe.lastIndex = 0;
      const rest = html.slice(tagEnd);
      const m = closeRe.exec(rest);
      const contentEnd = m ? tagEnd + m.index : len;
      const end = m ? tagEnd + m.index + m[0].length : len;
      onElement({
        name,
        tagStart: lt,
        tagEnd,
        contentStart: tagEnd,
        contentEnd,
        end,
        depth: stack.length,
        attrs: () => parseAttributes(html, j, gt),
        startTag: () => html.slice(lt, tagEnd),
      });
      i = end;
      continue;
    }
    if (selfClosed || VOID_ELEMENTS.has(name)) {
      onElement({
        name,
        tagStart: lt,
        tagEnd,
        contentStart: tagEnd,
        contentEnd: tagEnd,
        end: tagEnd,
        depth: stack.length,
        attrs: () => parseAttributes(html, j, gt),
        startTag: () => html.slice(lt, tagEnd),
      });
      i = tagEnd;
      continue;
    }
    stack.push({ name, tagStart: lt, tagEnd, attrStart: j, attrEnd: gt });
    i = tagEnd;
  }
  return stack.length;
}

/** Split a `class` attribute value into a set. */
export function classSet(value) {
  return new Set((value ?? "").split(/\s+/).filter(Boolean));
}

/** Apply non-overlapping `{ start, end, text }` edits to a string. */
export function applyEdits(html, edits) {
  const sorted = edits.slice().sort((a, b) => a.start - b.start || a.end - b.end);
  const out = [];
  let at = 0;
  for (const edit of sorted) {
    if (edit.start < at) {
      throw new Error(`overlapping edit at ${edit.start} (previous edit ended at ${at})`);
    }
    out.push(html.slice(at, edit.start), edit.text);
    at = edit.end;
  }
  out.push(html.slice(at));
  return out.join("");
}

/** Collect the ids and names declared inside `html`, in document order. */
export function collectAnchors(html) {
  const ids = [];
  scanElements(html, (el) => {
    let id = null;
    let name = null;
    for (const attr of el.attrs()) {
      if (attr.name === "id") id = attr.value;
      else if (attr.name === "name" && el.name !== "meta") name = attr.value;
    }
    if (id) ids.push({ kind: "id", value: id, at: el.tagStart });
    if (name) ids.push({ kind: "name", value: name, at: el.tagStart });
  });
  ids.sort((a, b) => a.at - b.at);
  return ids;
}
