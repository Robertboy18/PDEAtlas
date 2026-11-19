/*!
Deferred blueprint content, client side.

`Blueprint/Tools/defer-heavy-blocks.mjs` copies this file to
`-verso-data/leanpde-defer.mjs` and links it from every page. It rehydrates the three
kinds of payload that the build step moved out of the HTML into per-page JSON sidecars:

  * `[data-bp-defer-code]`   a closed code panel's body, fetched on first open or when a
                             link points inside it,
  * `[data-bp-defer-hover]`  a hover surface's markup (relation panels, preview
                             templates), fetched on the first pointer or focus that could
                             open it,
  * `[data-bp-defer-attrs]`  a relation chip's `data-bp-preview-*` bundle, restored on the
                             same signal.

Hydration goes through the documented preview API, `createPreview(...).hydrate(root)`, so
the same hydrators the page registered at startup run over the inserted markup. We create
our own instance with `bindTemplatePreviews: false` because the shared instance created by
`blueprint-page-runtime.mjs` already bound the document once, and re-binding it costs a
document-wide query on pages with 150,000 elements.

The rule that matters most: fragment links must keep working. 2,789 ids on this site are
`href` targets that live inside a closed code panel. The build step leaves an empty stub
carrying each of those ids in the page, so `getElementById` still finds them and the
static link audits still see them; this module notices that the element it found sits
inside a payload that has not arrived, fetches it, opens the disclosure, and then lets the
page's own hash handling highlight and scroll. `-deferred-index.json` maps id to payload
as a fallback for ids that are not in the page at all.
*/

import { createPreview } from "./blueprint-preview-api.mjs";

const doc = document;
// The build step writes the sidecar descriptors onto this module's own script tag.
const descriptor = doc.querySelector("script[data-bp-defer-dir]");
const readDescriptor = function (name, fallback) {
  const value = descriptor ? descriptor.getAttribute("data-bp-defer-" + name) : null;
  return value === null ? fallback : value;
};
const dir = readDescriptor("dir", "");
const codeChunkCount = Number(readDescriptor("code-chunks", "0"));
const hoverChunkCount = Number(readDescriptor("hover-chunks", "0"));

const renderApi = createPreview({ bindTemplatePreviews: false });

const chunks = new Map();
const chunkData = new Map();
const codePending = new WeakMap();
let indexPromise = null;
let ownHashChange = false;

function sidecarUrl(name) {
  try {
    return new URL(dir + name, doc.baseURI).href;
  } catch (_err) {
    return dir + name;
  }
}

function fetchJson(url) {
  return fetch(url, { credentials: "same-origin" }).then(function (response) {
    if (!response.ok) throw new Error("HTTP " + response.status + " for " + url);
    return response.json();
  });
}

function loadChunk(family, chunk) {
  const id = family + "-" + chunk;
  const ready = chunks.get(id);
  if (ready) return ready;
  const url = sidecarUrl("-deferred-" + family + "-" + chunk + ".json");
  const promise = fetchJson(url).then(
    function (value) {
      const data = value && typeof value === "object" ? value : {};
      chunkData.set(id, data);
      return data;
    },
    function (error) {
      if (typeof console !== "undefined") console.warn("deferred payload failed", url, error);
      chunkData.set(id, {});
      return {};
    },
  );
  chunks.set(id, promise);
  return promise;
}

function splitRef(ref) {
  const slash = (ref || "").indexOf("/");
  if (slash === -1) return null;
  return { chunk: ref.slice(0, slash), key: ref.slice(slash + 1) };
}

/** Payload for `ref` if its chunk is already in memory, otherwise `undefined`. */
function payloadNow(family, ref) {
  const parts = splitRef(ref);
  if (!parts) return undefined;
  const data = chunkData.get(family + "-" + parts.chunk);
  return data ? data[parts.key] : undefined;
}

function payloadSoon(family, ref) {
  const parts = splitRef(ref);
  if (!parts) return Promise.resolve(undefined);
  return loadChunk(family, parts.chunk).then(function (data) {
    return data[parts.key];
  });
}

function parseFragment(markup) {
  const template = doc.createElement("template");
  template.innerHTML = markup;
  return template.content;
}

/**
 * Clear the runtime's "already bound" markers inside `scope`.
 *
 * Every feature in the page runtime guards against double binding with an attribute whose
 * name ends in `bound`, and several of them set the marker before discovering that the
 * element they were handed is empty. An emptied hover surface is therefore marked as bound
 * during page startup and would never bind again. Clearing the markers generically is
 * deliberate: a duplicate listener shows the same panel twice, a missing one shows nothing.
 */
function clearBoundMarkers(scope) {
  if (!(scope instanceof Element)) return;
  const strip = function (el) {
    if (!(el instanceof Element)) return;
    const names = el.getAttributeNames();
    for (let i = 0; i < names.length; i += 1) {
      const name = names[i];
      if (name.indexOf("data-bp-") === 0 && /bound$/.test(name)) el.removeAttribute(name);
    }
  };
  strip(scope);
  scope.querySelectorAll("[data-bp-bound], [data-bp-template-preview-bound], [data-bp-relation-chip-bound], [data-bp-relation-panel-lifetime-bound], [data-bp-relation-dismiss-bound], [data-bp-preview-bound]").forEach(strip);
}

const LEAN_TOKEN_KINDS = ["const", "keyword", "literal", "option", "var", "typed"];
const LEAN_LEVEL_KINDS = ["level-var", "level-const", "level-op", "sort"];

let highlightedTokens = [];
const bindingTokenCache = new Map();

function cssEscape(value) {
  if (typeof CSS !== "undefined" && typeof CSS.escape === "function") return CSS.escape(value);
  return String(value).replace(/["\\]/g, "\\$&");
}

/** The theme the page installer would have given this token, by class. */
function leanTippyTheme(el) {
  const classes = el.classList;
  if (classes.contains("tactic")) return "tactic";
  if (classes.contains("has-info")) {
    if (classes.contains("warning")) return "warning message";
    if (classes.contains("information")) return "info message";
    if (classes.contains("error")) return "error message";
    return null;
  }
  if (classes.contains("token")) {
    for (let i = 0; i < LEAN_TOKEN_KINDS.length; i += 1) {
      if (classes.contains(LEAN_TOKEN_KINDS[i])) return "lean";
    }
  }
  for (let i = 0; i < LEAN_LEVEL_KINDS.length; i += 1) {
    if (classes.contains(LEAN_LEVEL_KINDS[i])) return "lean";
  }
  return null;
}

function bindingTokens(context, binding) {
  const key = String(context) + "\u0000" + String(binding);
  let tokens = bindingTokenCache.get(key);
  if (!tokens) {
    tokens = [];
    doc.querySelectorAll(".hl.lean").forEach(function (example) {
      if (example.dataset.leanContext !== context) return;
      example.querySelectorAll('.token[data-binding="' + cssEscape(binding) + '"]').forEach(function (token) {
        tokens.push(token);
      });
    });
    bindingTokenCache.set(key, tokens);
  }
  return tokens;
}

function bindBindingHighlights(container, kit) {
  if (container.getAttribute("data-leanpde-binding-bound") === "1") return;
  container.setAttribute("data-leanpde-binding-bound", "1");
  container.addEventListener("mouseover", function (event) {
    const token = event.target instanceof Element ? event.target.closest(".token") : null;
    if (!token || !token.dataset.binding || !container.contains(token)) return;
    if (typeof kit.blockedByTactic === "function" && kit.blockedByTactic(token)) return;
    const tokens = bindingTokens(container.dataset.leanContext, token.dataset.binding);
    tokens.forEach(function (other) {
      other.classList.add("binding-hl");
    });
    highlightedTokens = tokens;
  });
  container.addEventListener("mouseout", function (event) {
    const token = event.target instanceof Element ? event.target.closest(".token") : null;
    if (!token || !container.contains(token)) return;
    highlightedTokens.forEach(function (other) {
      other.classList.remove("binding-hl");
    });
    highlightedTokens = [];
  });
}

function bindTacticToggle(tactic, kit, tippy) {
  const toggle = tactic.querySelector(":scope > input.tactic-toggle");
  if (!toggle) return;
  if (!toggle.checked && kit.closedTactics && typeof kit.closedTactics.add === "function") {
    kit.closedTactics.add(tactic);
  }
  if (toggle.getAttribute("data-leanpde-tactic-bound") === "1") return;
  toggle.setAttribute("data-leanpde-tactic-bound", "1");
  toggle.addEventListener("change", function () {
    if (toggle.checked) {
      if (kit.closedTactics) kit.closedTactics.delete(tactic);
      tactic.querySelectorAll(".token").forEach(function (token) {
        if (!token._tippy && token.matches(kit.tacticTippySelector)) tippy(token, kit.defaultTippyProps);
      });
    } else {
      if (kit.closedTactics) kit.closedTactics.add(tactic);
      tactic.querySelectorAll(".token").forEach(function (token) {
        if (token._tippy) token._tippy.destroy();
      });
    }
  });
}

/**
 * Give inserted Lean code the hovers the rest of the page has.
 *
 * Verso installs tippy once, on `load`, over the tokens present at that moment, so
 * declarations that arrive later would have no docstring hovers, no binding highlights and
 * no rendered docstrings. The build step publishes the installer's closure as
 * `leanpdeLeanHoverKit` and this repeats its work for one subtree. Without the kit the
 * panel still reads; it just loses hovers.
 */
function bindLeanTokens(root) {
  const kit = globalThis.leanpdeLeanHoverKit;
  const tippy = globalThis.tippy;
  if (!(root instanceof Element) || !kit || typeof tippy !== "function") return;
  if (typeof kit.tokenSelector !== "string" || kit.tokenSelector.length === 0) return;
  // Inserted tokens can share a binding with tokens already on the page, so the installer's
  // cache has to forget what it thinks a binding covers.
  if (kit.bindingCache && typeof kit.bindingCache.clear === "function") kit.bindingCache.clear();
  bindingTokenCache.clear();

  root.querySelectorAll(".hl.lean .tactic").forEach(function (tactic) {
    bindTacticToggle(tactic, kit, tippy);
  });
  root.querySelectorAll(kit.tokenSelector).forEach(function (el) {
    const theme = leanTippyTheme(el);
    if (theme) el.setAttribute("data-tippy-theme", theme);
  });

  const containers = [];
  if (typeof root.matches === "function" && root.matches(".hl.lean")) containers.push(root);
  root.querySelectorAll(".hl.lean").forEach(function (container) {
    containers.push(container);
  });
  containers.forEach(function (container) {
    bindBindingHighlights(container, kit);
  });

  const marked = globalThis.marked;
  if (marked && typeof marked.parse === "function") {
    root.querySelectorAll("code.docstring, pre.docstring").forEach(function (node) {
      const rendered = doc.createElement("div");
      rendered.classList.add("docstring");
      try {
        rendered.innerHTML = marked.parse(node.textContent || "");
      } catch (_err) {
        return;
      }
      if (node.parentNode) node.parentNode.replaceChild(rendered, node);
    });
  }

  const targets = [];
  root.querySelectorAll(kit.tokenSelector).forEach(function (el) {
    if (el._tippy) return;
    if (typeof kit.isInsideClosedTactic === "function" && kit.isInsideClosedTactic(el)) return;
    targets.push(el);
  });
  if (targets.length > 0) {
    try {
      tippy(targets, kit.defaultTippyProps);
    } catch (_err) {}
  }
}

function hydrateScope(scope) {
  if (!(scope instanceof Element)) return Promise.resolve(false);
  try {
    renderApi.hydrate(scope);
    return Promise.resolve(true);
  } catch (_err) {
    return Promise.resolve(false);
  }
}

function setStatus(slot, text) {
  const status = slot.querySelector(".bp_defer_status");
  if (status) status.textContent = text;
}

// Code panels.

function hydrateCode(slot) {
  if (!(slot instanceof Element)) return Promise.resolve(false);
  const started = codePending.get(slot);
  if (started) return started;
  const ref = slot.getAttribute("data-bp-defer-code");
  if (!ref) return Promise.resolve(false);
  const details = slot.closest("details");
  const promise = payloadSoon("code", ref).then(function (markup) {
    if (typeof markup !== "string") {
      slot.setAttribute("data-bp-defer-state", "error");
      setStatus(slot, "The Lean code did not load. Reload the page to try again.");
      return false;
    }
    const fragment = parseFragment(markup);
    slot.replaceWith(fragment);
    const scope = details instanceof Element ? details : null;
    if (scope) {
      bindLeanTokens(scope);
      return hydrateScope(scope).then(function () {
        return true;
      });
    }
    return true;
  });
  codePending.set(slot, promise);
  return promise;
}

function codeSlotIn(details) {
  if (!(details instanceof Element)) return null;
  return details.querySelector(":scope > [data-bp-defer-code]");
}

doc.addEventListener(
  "toggle",
  function (event) {
    const details = event.target;
    if (!(details instanceof Element) || details.tagName !== "DETAILS") return;
    if (!details.hasAttribute("open")) return;
    const slot = codeSlotIn(details);
    if (slot) hydrateCode(slot);
  },
  true,
);

// Hover surfaces and chip attribute bundles.

function triggerIn(scope) {
  if (!(scope instanceof Element)) return null;
  const selector = scope.getAttribute("data-bp-template-preview-trigger-selector");
  if (selector) {
    try {
      const found = scope.querySelector(selector);
      if (found) return found;
    } catch (_err) {}
  }
  return scope.querySelector(".bp_relation_chip") || scope;
}

function stillEngaged(el) {
  if (!(el instanceof Element) || !el.isConnected) return false;
  try {
    if (el.matches(":hover")) return true;
  } catch (_err) {}
  const active = doc.activeElement;
  return active instanceof Element && (el === active || el.contains(active));
}

/**
 * Re-send the signal that arrived before the markup did.
 *
 * The runtime binds its listeners directly on each trigger, so the gesture that started the
 * fetch is lost: it happened while the surface was still unbound. Replaying it on the trigger,
 * and only while the reader is still there, makes the first gesture behave like every later one.
 *
 * The kind matters. A relation chip opens its panel on hover, but the Lean status chip on a
 * statement card is a button that opens on click and ignores hover, so replaying a hover after a
 * click would leave the reader looking at nothing and clicking again. We replay what arrived.
 */
function replayIntent(el, kind) {
  if (!stillEngaged(el)) return;
  if (kind === "activate" && !(el instanceof HTMLAnchorElement && el.hasAttribute("href"))) {
    try {
      el.click();
    } catch (_err) {}
    return;
  }
  try {
    el.dispatchEvent(new MouseEvent("mouseover", { bubbles: true, cancelable: true, view: window }));
    el.dispatchEvent(new MouseEvent("mouseenter", { bubbles: false, cancelable: false, view: window }));
  } catch (_err) {}
  const active = doc.activeElement;
  if (active instanceof Element && (el === active || el.contains(active))) {
    try {
      el.dispatchEvent(new FocusEvent("focusin", { bubbles: true }));
    } catch (_err) {}
  }
}

/*
The element that owns a deferred preview body. A relation wrap holds its own panel; a template
preview root holds a template, and the build step renames its descriptor attribute so the page
does not bind the surface while the template is empty, so we look for both spellings.
*/
const SCOPE_SELECTOR = ".bp_relation_wrap, [data-bp-template-preview-root], [data-bp-defer-preview-root]";

/**
 * Hand a preview root back to the page runtime.
 *
 * The build step parked the descriptor under a different attribute name. Putting the name back
 * before we hydrate means the descriptor binder sees a root with a full template and a panel
 * still inside it, which is the only state in which it will bind.
 */
function awaken(scope) {
  const parked = scope.getAttribute("data-bp-defer-preview-root");
  if (parked === null) return;
  scope.setAttribute("data-bp-template-preview-root", parked || "true");
  scope.removeAttribute("data-bp-defer-preview-root");
}

/*
The gesture to replay once a payload lands, per host. A press and the click that follows it are
two intents on the same host, and the payload usually arrives after both, so the last one wins.
*/
const pendingIntent = new WeakMap();

function applyHover(host, scope, markup) {
  if (!host.hasAttribute("data-bp-defer-hover")) return false;
  if (typeof markup !== "string") {
    host.removeAttribute("data-bp-defer-hover");
    host.removeAttribute("data-bp-defer-kind");
    return false;
  }
  host.innerHTML = markup;
  host.removeAttribute("data-bp-defer-hover");
  host.removeAttribute("data-bp-defer-kind");
  clearBoundMarkers(scope);
  awaken(scope);
  bindLeanTokens(host);
  hydrateScope(scope);
  return true;
}

function hydrateHover(host, scope) {
  const ref = host.getAttribute("data-bp-defer-hover");
  if (!ref) return;
  warmHoverChunks();
  const replay = function (ok) {
    if (!ok) return;
    const kind = pendingIntent.get(host) || "hover";
    pendingIntent.delete(host);
    replayIntent(triggerIn(scope), kind);
  };
  const ready = payloadNow("hover", ref);
  if (typeof ready === "string") {
    replay(applyHover(host, scope, ready));
    return;
  }
  payloadSoon("hover", ref).then(function (markup) {
    replay(applyHover(host, scope, markup));
  });
}

function applyAttrs(chip, bundle) {
  if (!chip.hasAttribute("data-bp-defer-attrs")) return false;
  if (!bundle || typeof bundle !== "object") {
    chip.removeAttribute("data-bp-defer-attrs");
    return false;
  }
  Object.keys(bundle).forEach(function (name) {
    const value = bundle[name];
    if (typeof value === "string") chip.setAttribute("data-bp-preview-" + name, value);
  });
  chip.removeAttribute("data-bp-defer-attrs");
  return true;
}

function restoreAttrs(chip) {
  const ref = chip.getAttribute("data-bp-defer-attrs");
  if (!ref) return;
  const ready = payloadNow("hover", ref);
  if (ready) {
    applyAttrs(chip, ready);
    return;
  }
  payloadSoon("hover", ref).then(function (bundle) {
    if (applyAttrs(chip, bundle)) replayIntent(chip);
  });
}

function intentKind(event) {
  if (event.type === "click") return "activate";
  if (event.type === "keydown") {
    const key = event.key;
    return key === "Enter" || key === " " || key === "Spacebar" ? "activate" : "hover";
  }
  return "hover";
}

function onIntent(event) {
  const target = event.target;
  if (!(target instanceof Element)) return;
  const chip = target.closest("[data-bp-defer-attrs]");
  if (chip) restoreAttrs(chip);
  const scope = target.closest(SCOPE_SELECTOR);
  if (!scope) return;
  const host = scope.querySelector("[data-bp-defer-hover]");
  if (!host) return;
  pendingIntent.set(host, intentKind(event));
  hydrateHover(host, scope);
}

const INTENT_EVENTS = ["pointerover", "mouseover", "mouseenter", "focusin", "pointerdown", "touchstart", "click", "keydown"];
for (let i = 0; i < INTENT_EVENTS.length; i += 1) {
  doc.addEventListener(INTENT_EVENTS[i], onIntent, true);
}

// Hash navigation. This module owns it for deferred content.

function openAncestors(el) {
  let node = el instanceof Element ? el.closest("details") : null;
  let opened = false;
  while (node) {
    if (!node.open) {
      node.open = true;
      opened = true;
    }
    node = node.parentElement ? node.parentElement.closest("details") : null;
  }
  return opened;
}

const SCROLL_CANCEL_EVENTS = ["wheel", "touchstart", "keydown", "pointerdown"];
const SETTLE_DELAYS = [0, 0, 32, 120, 350, 700];

function headerBottom() {
  const header = doc.querySelector("header");
  return header ? Math.max(0, header.getBoundingClientRect().bottom) : 0;
}

function tallerThanViewport(el) {
  const height = window.innerHeight || doc.documentElement.clientHeight || 0;
  return el.getBoundingClientRect().height > height - headerBottom();
}

function onScreen(el) {
  const rect = el.getBoundingClientRect();
  const height = window.innerHeight || doc.documentElement.clientHeight || 0;
  const top = headerBottom();
  return rect.top >= top - 1 && rect.bottom > top && rect.top < height;
}

function aim(el) {
  // Centering a long theorem or signature hides its beginning above the viewport.
  // Align its start below the header; short targets can still be centered.
  if (tallerThanViewport(el)) {
    const margin = parseFloat(window.getComputedStyle(el).scrollMarginTop) || 0;
    el.scrollIntoView({ block: "start", behavior: "instant" });
    window.scrollBy({ top: el.getBoundingClientRect().top - headerBottom() - margin,
      behavior: "instant" });
  } else {
    el.scrollIntoView({ block: "center", behavior: "instant" });
  }
}

// One scroll is not enough. Opening the disclosures above a target can start a second fetch
// whose body lands after we have scrolled, and the page's own hashchange listeners move things
// too, so the target drifts off screen a few hundred milliseconds later. Keep re-aiming until
// it stops moving, and give up the moment the reader takes over.
let cancelSettle = null;

function settleScroll(el) {
  // A reader who clicks a second link before the first has settled must not be dragged back to
  // the first target, so a new aim cancels the one in flight.
  if (cancelSettle) cancelSettle();
  let index = 0;
  let last = null;
  let stopped = false;
  /*
  Chrome keeps the reader's place when content above the viewport grows, by adding the new height
  to the scroll offset. That is the right instinct while reading and the wrong one here: the panel
  body we just inserted is exactly such a growth, and the adjustment lands after our scroll, so
  the reader ends up thousands of pixels past the declaration they asked for. Anchoring is off for
  as long as we are aiming, and on again the moment we stop.
  */
  const root = doc.documentElement;
  const savedAnchor = root.style.overflowAnchor;
  root.style.overflowAnchor = "none";
  const stop = function () {
    if (stopped) return;
    stopped = true;
    root.style.overflowAnchor = savedAnchor;
    if (cancelSettle === stop) cancelSettle = null;
    for (let i = 0; i < SCROLL_CANCEL_EVENTS.length; i += 1) {
      window.removeEventListener(SCROLL_CANCEL_EVENTS[i], stop, true);
    }
  };
  cancelSettle = stop;
  for (let i = 0; i < SCROLL_CANCEL_EVENTS.length; i += 1) {
    window.addEventListener(SCROLL_CANCEL_EVENTS[i], stop, true);
  }
  const step = function () {
    if (stopped || !el.isConnected) {
      stop();
      return;
    }
    const top = el.getBoundingClientRect().top;
    if (last === null || Math.abs(top - last) > 1 || !onScreen(el)) aim(el);
    last = el.getBoundingClientRect().top;
    if (index < SETTLE_DELAYS.length) {
      const delay = SETTLE_DELAYS[index];
      index += 1;
      if (delay === 0) window.requestAnimationFrame(step);
      else window.setTimeout(step, delay);
    } else {
      stop();
    }
  };
  aim(el);
  window.requestAnimationFrame(step);
}

// A deferred panel can sit inside another one. Opening the outer disclosure starts its fetch,
// and the markup it inserts lands above the target, so wait for the whole chain before scrolling.
function hydrateAncestors(el) {
  const slots = [];
  let node = el instanceof Element ? el.parentElement : null;
  while (node) {
    const slot = node.closest("[data-bp-defer-code]");
    if (!slot) break;
    slots.push(slot);
    node = slot.parentElement;
  }
  if (!slots.length) return Promise.resolve();
  return Promise.all(slots.map(hydrateCode)).then(function () {});
}

function decodeFragment(raw) {
  try {
    return decodeURIComponent(raw);
  } catch (_err) {
    return raw;
  }
}

function elementForFragment(raw) {
  const decoded = decodeFragment(raw);
  return (
    doc.getElementById(decoded) ||
    doc.getElementById(raw) ||
    doc.getElementsByName(decoded)[0] ||
    null
  );
}

function slotFromIndex(fragment) {
  if (!codeChunkCount) return Promise.resolve(null);
  if (!indexPromise) {
    indexPromise = fetchJson(sidecarUrl("-deferred-index.json")).catch(function () {
      return null;
    });
  }
  return indexPromise.then(function (index) {
    const ids = index && index.ids && typeof index.ids === "object" ? index.ids : null;
    if (!ids) return null;
    const ref = ids[fragment] || ids[decodeFragment(fragment)];
    if (typeof ref !== "string") return null;
    const escaped = typeof CSS !== "undefined" && CSS.escape ? CSS.escape(ref) : ref.replace(/["\\]/g, "\\$&");
    return doc.querySelector('[data-bp-defer-code="' + escaped + '"]');
  });
}

function announceHashChange() {
  ownHashChange = true;
  try {
    let event;
    try {
      event = new HashChangeEvent("hashchange", { newURL: location.href, oldURL: location.href });
    } catch (_err) {
      event = new Event("hashchange");
    }
    window.dispatchEvent(event);
  } finally {
    ownHashChange = false;
  }
}

/*
`arrived` means the browser has already done its own fragment scroll, which is the case on load
and by the time a `hashchange` reaches us. Then, and only then, are we entitled to judge the
result and take the scroll over: on a click we run before the browser, and an ordinary in-page
anchor should keep the alignment the reader is used to.
*/
function reveal(rawFragment, arrived) {
  const fragment = (rawFragment || "").replace(/^#/, "");
  if (!fragment) return Promise.resolve(false);
  if (cancelSettle) cancelSettle();
  const found = elementForFragment(fragment);
  const slot = found ? found.closest("[data-bp-defer-code]") : null;
  const resolve = slot ? Promise.resolve(slot) : found ? Promise.resolve(null) : slotFromIndex(fragment);
  return resolve.then(function (target) {
    if (!(target instanceof Element)) {
      if (!found) return false;
      const opened = openAncestors(found);
      // Nothing was deferred here, so the browser had its chance. It misses when we have just
      // opened a disclosure under it, and it misses on the ids Lean spells with escapes, where
      // the browser's fragment matching and `getElementById` disagree.
      // Other hash listeners may center a tall card after the browser's initial jump.
      if (arrived && (opened || !onScreen(found) || tallerThanViewport(found))) {
        settleScroll(found);
      }
      return opened;
    }
    return hydrateCode(target).then(function () {
      const el = elementForFragment(fragment) || found;
      if (!el) return false;
      openAncestors(el);
      return hydrateAncestors(el).then(function () {
        openAncestors(el);
        announceHashChange();
        settleScroll(el);
        return true;
      });
    });
  });
}

window.addEventListener("hashchange", function () {
  if (ownHashChange) return;
  reveal(location.hash, true);
});

doc.addEventListener(
  "click",
  function (event) {
    if (event.defaultPrevented || event.button !== 0) return;
    if (event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    const target = event.target;
    const anchor = target instanceof Element ? target.closest("a[href]") : null;
    if (!anchor) return;
    const raw = anchor.getAttribute("href") || "";
    if (raw.charAt(0) === "#") {
      reveal(raw);
      return;
    }
    const hash = anchor.hash;
    if (!hash || hash.length < 2) return;
    let resolved;
    try {
      resolved = new URL(anchor.href);
    } catch (_err) {
      return;
    }
    const here = new URL(location.href);
    if (resolved.origin !== here.origin) return;
    const normalize = function (pathname) {
      return pathname.replace(/index\.html$/, "");
    };
    if (normalize(resolved.pathname) !== normalize(here.pathname)) return;
    reveal(hash);
  },
  true,
);

function whenReady(fn) {
  if (doc.readyState === "loading") {
    doc.addEventListener("DOMContentLoaded", fn, { once: true });
  } else {
    fn();
  }
}

whenReady(function () {
  if (location.hash) reveal(location.hash, true);
});

let warmRequested = false;

/**
 * Warm the rest of the hover sidecars, once the reader has used one.
 *
 * A chapter carries a few megabytes of preview markup, so fetching all of it on load would put
 * the bytes we took out of the page straight back on the wire, and a reader who never hovers
 * would pay for every one. The first hover pays for the chunk it needs; from then on the reader
 * is clearly reading with the pointer, so we pull the remaining chunks in while the browser is
 * idle and every later preview opens without a round trip. Save-data and 2G opt out entirely.
 */
function warmHoverChunks() {
  if (warmRequested || !hoverChunkCount) return;
  warmRequested = true;
  const connection = navigator.connection;
  if (connection) {
    if (connection.saveData) return;
    if (/(^|-)2g$/.test(connection.effectiveType || "")) return;
  }
  const start = function () {
    for (let chunk = 0; chunk < hoverChunkCount; chunk += 1) loadChunk("hover", chunk);
  };
  if (typeof requestIdleCallback === "function") requestIdleCallback(start, { timeout: 3000 });
  else setTimeout(start, 1200);
}

export const leanpdeDefer = { reveal, hydrateCode, hydrateHover, restoreAttrs, renderApi };
export default leanpdeDefer;
