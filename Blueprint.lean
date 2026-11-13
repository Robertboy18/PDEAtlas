/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.PreviewManifest
import Blueprint.Commands.Bibliography
import Blueprint.Commands.Figures
import Blueprint.Chapters.Overview
import Blueprint.Chapters.RelatedWork
import Blueprint.Chapters.Foundations
import Blueprint.Chapters.Sobolev
import Blueprint.Chapters.Elliptic
import Blueprint.Chapters.Parabolic
import Blueprint.Chapters.Hyperbolic
import Blueprint.Chapters.Fluid
import Blueprint.Chapters.Variational
import Blueprint.Chapters.Symbolic
import Blueprint.Chapters.DependencyAtlas

/-!
# LeanPDE: the book and its opening page

This module assembles the book. The overview introduces the library through
its contributions, authors, and history. Twelve chapters develop the mathematics,
from a worked calculation in the Introduction and a comparison with related
projects to the Bibliography. The computation chapter also contains
the textbook map and certified plots. This file carries the site stylesheet,
page scripts, and command-line renderer. Its Lake package lives under
`Blueprint/`, so the public Lean libraries do not depend on Verso.

`Blueprint/Tools/optimize-site.mjs` finishes the site shell after rendering:
the sidebar subtitle, the entry for this page, the footer with the theme
button and optional repository link, and the Proof map action on
statement cards.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- The embedded site stylesheet and script below keep their natural line
-- lengths; Verso raw strings are not Lean code.
set_option linter.style.longLine false

-- This persistent `#doc` command is the module's public artifact.
set_option linter.hashCommand false in
set_option linter.style.emptyLine false in
#docs (Manual) leanPDEBlueprint "PDEAtlas" :=
:::::::

%%%
tag := "leanpde"
authors := ["Robert Joseph George", "Anima Anandkumar"]
%%%

PDEAtlas is a formalization and exposition of Lawrence C. Evans's
[*Partial Differential Equations*, second edition](https://www.ams.org/bookpages/gsm-19-r),
in Lean 4 and Mathlib. It pairs selected results from the textbook with
machine-checked proofs, worked calculations, and explanations of the analysis.
The exposition is intended for graduate students studying PDEs and for
undergraduates with a background in analysis.

PDEAtlas is also a foundation for further PDE formalization. Its Sobolev spaces,
weak derivatives, energy estimates, and solution constructions are designed
for reuse in projects on Navier–Stokes, Euler, and singularity formation.
Our proof-producing CAS connects symbolic calculus and certified numerical
bounds to those analytic arguments, including the De Gregorio blowup proof.

Related efforts include [FluidLean](https://github.com/tristanbuckmaster/fluid_lean),
[our team's Euler project](https://github.com/lean-dojo/Euler), and
[OpenAI's Navier–Stokes and Euler formalizations](https://github.com/openai/NavierStokesAndEuler).
We aim to contribute suitable general results to
[Mathlib](https://leanprover-community.github.io/contribute/index.html) and to
coordinate with [Tau Ceti's PDE roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/PDE/README.md).

We contacted Evans about following his book, and he was excited about the project.

A few parts of the library we are especially excited about:

* *Constructing solutions.* The
  {bpref "elliptic.poisson.convolution_solution"}[fundamental-solution construction]
  gives classical Poisson solutions for compactly supported $`C^2` data in
  dimensions $`n\ge2`. The
  {bpref "elliptic.energy.dirichlet_principle"}[Dirichlet principle] relates
  classical solutions to finite-energy minimizers on bounded $`C^1` graph domains.
  These are complementary ways to use the analysis: one builds a formula,
  the other identifies a solution by its energy.

* *Analysis beyond explicit formulas.* The development also covers Sobolev
  spaces and traces, compactness, weak formulations, heat and wave equations,
  transport, and variational methods.

* *Calculations a proof can use.* `cas` proves supported identities,
  derivatives and integrals in ordinary Lean notation. `cega` turns intervals,
  Taylor models, quadrature and root certificates into bounds on real functions.
  We use [FloatLib](https://github.com/lean-dojo/FloatLib) for checked interval
  arithmetic and elementary-function enclosures. The
  {bpref "symbolic.normalization_sound"}[soundness theorems] connect the
  computed expressions to Mathlib's analytic definitions. We can differentiate
  a proposed profile, check its residual, and use that result in an energy estimate.

* *Fluid constructions.* Given a smooth harmonic velocity potential, we
  {bpref "fluid.euler.potential_solution"}[construct an Euler solution] with
  recovered pressure and the prescribed initial trace. The fluid library also
  treats weak formulations, vorticity, energy and exact flows. Two applications
  built on it, blowup for the De Gregorio model on the real line and the
  nonuniqueness of suitable Leray–Hopf solutions of the Navier–Stokes equations,
  are formalized in the companion repository
  [BlowupZoo](https://github.com/Robertboy18/BlowupZoo).

The CAS also responds to a long-standing community question. The
[2020 CAS-tactics wishlist](https://github.com/leanprover-community/mathlib3/issues/2730)
asked for expression manipulation that sits naturally inside a Lean proof. In a
[2023 Lean Zulip discussion](https://leanprover-community.github.io/archive/stream/113488-general/topic/Computer.20Algebra.20Systems.20and.20Lean.html),
Kaiyu Yang proposed a transparent PDE solver, and the discussion asked how
to turn that idea into a concrete plan. Our contribution is a set of symbolic procedures whose answers come
with proofs over the analytic objects a PDE argument already uses.
[Hex](https://github.com/leanprover/hex) develops verified computational algebra,
including polynomial, matrix and algebraic-number algorithms with Mathlib
correspondence layers where available.
The {ref "verified-computation"}[computation chapter] explains our algorithms,
prior work and supported operations.

For large finite computations, `cega [fast]` can check certificates by compiled
evaluation. This additionally trusts Lean's compiler and native evaluation;
CAS and bare `cega` retain kernel checking. The
{ref "verified-computation"}[computation chapter] explains both modes and
how to build the De Gregorio certificates with kernel evaluation instead.

We began thinking about this project in early 2024. That July, Robert
[asked on Lean Zulip](https://leanprover-community.github.io/archive/stream/113488-general/topic/Formalization.20of.20PDEs.20in.20Lean.3F.html)
about PDE formalization. The conversation pointed us toward the multivariable
calculus and Sobolev theory already in Mathlib. Much of the work that followed
was learning that analysis, choosing definitions, and working through proofs.
We used AI coding agents to write and repair proofs and documentation. We chose the statements,
definitions and sources, and checked the claims.

PDEAtlas is written by Robert Joseph George and Anima Anandkumar at Caltech, with the PDE
group of Thomas Y. Hou. Contributors include Peicong Song. We thank the Lean and Mathlib communities for their mathematics,
tools and conversations, and Evans for his interest in the project.
Source references identify the results we follow.

To contribute a PDE result, extend the computer algebra system, or improve an explanation, see
the [contributing guide](https://github.com/Robertboy18/PDEAtlas/blob/main/CONTRIBUTING.md).

{include 0 Blueprint.Chapters.Overview}
{include 0 Blueprint.Chapters.RelatedWork}
{include 0 Blueprint.Chapters.Foundations}
{include 0 Blueprint.Chapters.Sobolev}
{include 0 Blueprint.Chapters.Elliptic}
{include 0 Blueprint.Chapters.Parabolic}
{include 0 Blueprint.Chapters.Hyperbolic}
{include 0 Blueprint.Chapters.Fluid}
{include 0 Blueprint.Chapters.Variational}
{include 0 Blueprint.Chapters.Symbolic}
{include 0 Blueprint.Chapters.DependencyAtlas}
{leanpde_bibliography}
:::::::

/-- The site stylesheet: paper and serif prose, quiet sans-serif navigation,
notebook cell rails, warm calculator accents and teal mathematical figures.
Verso's own stylesheet arrives in unspecified order relative to this one,
so overrides use `html` prefixes or `!important`. -/
private def blueprintSiteCss : CSS := r##"
/* Typography. */
html:root {
  --verso-text-font-family: "Iowan Old Style", "Palatino Linotype", "Book Antiqua", Palatino, "STIX Two Text", Georgia, "Times New Roman", "DejaVu Serif", serif;
  --verso-structure-font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Cantarell, "DejaVu Sans", Arial, sans-serif;
  --verso-code-font-family: "Source Code Pro", ui-monospace, SFMono-Regular, Menlo, Consolas, "DejaVu Sans Mono", monospace;
  --verso-header-height: 0px;
  --verso-toc-width: 17rem;
  --verso-content-max-width: 47rem;
  --verso-toc-background-color: #f7f5ef;
  --verso-toc-border-color: #e2ded4;
  --leanpde-page: #fffdf8;
  --leanpde-panel: #f7f5ef;
  --leanpde-ink: #292923;
  --leanpde-ink-strong: #1e2422;
  --leanpde-ink-soft: #46483f;
  --leanpde-accent: #a4442d;
  --leanpde-accent-wash: #f9ede5;
  --leanpde-pde: #176b68;
  --leanpde-pde-wash: #eaf3ef;
  --leanpde-code-surface: #f5f3ee;
  --leanpde-rule: #ddd9cf;
  --leanpde-rule-strong: #bdb8ab;
  --leanpde-muted: #706b61;
  --leanpde-faint: #aaa394;
  --leanpde-badge-border: #ccc7bb;
  --leanpde-badge-text: #625f55;
  --leanpde-badge-icon: #b3ad9f;
  --leanpde-badge-icon-ink: #fffdf8;
  --leanpde-selection: #f4dcc6;
  --leanpde-cell-accent: var(--leanpde-accent);
  --verso-text-color: var(--leanpde-ink);
  --verso-code-color: var(--leanpde-ink);
  --verso-structure-color: var(--leanpde-ink-strong);
  --verso-background-color: var(--leanpde-page);
  --verso-surface-color: var(--leanpde-panel);
  --verso-border-color: var(--leanpde-rule);
  --verso-muted-color: var(--leanpde-muted);
  --verso-selected-color: var(--leanpde-accent-wash);
  /* Keep Lean's messages and interactive proof views on the same palette. */
  --verso-info-indicator-color: var(--leanpde-pde);
  --verso-warning-indicator-color: var(--leanpde-accent);
  --verso-error-indicator-color: var(--leanpde-accent);
  --verso-message-info-color: var(--leanpde-ink);
  --verso-message-warning-color: var(--leanpde-ink);
  --verso-message-error-color: var(--leanpde-accent);
  --verso-tooltip-color: var(--leanpde-ink);
  --verso-tooltip-bg-color: var(--leanpde-panel);
  --verso-tooltip-border-color: var(--leanpde-rule-strong);
  --verso-tooltip-separator-color: var(--leanpde-rule);
  --verso-tooltip-info-color: var(--leanpde-ink);
  --verso-tooltip-info-bg-color: var(--leanpde-code-surface);
  --verso-tooltip-info-border-color: var(--leanpde-pde);
  --verso-tooltip-warning-color: var(--leanpde-ink);
  --verso-tooltip-warning-bg-color: var(--leanpde-panel);
  --verso-tooltip-warning-border-color: var(--leanpde-accent);
  --verso-tooltip-error-color: var(--leanpde-ink);
  --verso-tooltip-error-bg-color: var(--leanpde-panel);
  --verso-tooltip-error-border-color: var(--leanpde-accent);
  --verso-code-hover-bg-color: var(--leanpde-pde-wash);
  --verso-code-info-hover-bg-color: var(--leanpde-pde-wash);
  --verso-code-warning-hover-bg-color: var(--leanpde-accent-wash);
  --verso-code-error-hover-bg-color: var(--leanpde-accent-wash);
  --verso-tactic-state-color: var(--leanpde-ink);
  --verso-tactic-state-bg-color: var(--leanpde-code-surface);
  --verso-tactic-state-border-color: var(--leanpde-rule-strong);
  --verso-tactic-toggle-color: var(--leanpde-muted);
  --verso-tactic-toggle-checked-color: var(--leanpde-pde);

  /* Width of the section rail's column. Read by `main`, so it lives here. */
  --leanpde-rail-width: clamp(11rem, 13.5vw, 15rem);
  color-scheme: light;
  --bp-shadow-sm: none;
  --bp-shadow-md: none;
  --bp-shadow-lg: none;
  --bp-shadow-modern: none;
  --bp-shadow-bold: none;
  --bp-shadow-bold-lg: none;
  --bp-radius-sm: 2px;
  --bp-radius-md: 2px;
  --bp-radius-lg: 2px;
  --bp-radius-xl: 2px;
  --bp-radius-2xl: 2px;
  --bp-radius-3xl: 2px;
  --bp-color-surface: var(--leanpde-page);
  --bp-color-surface-muted: var(--leanpde-panel);
  --bp-color-surface-subtle: var(--leanpde-panel);
  --bp-color-surface-modern: var(--leanpde-page);
  --bp-color-border: var(--leanpde-rule);
  --bp-color-border-soft: var(--leanpde-rule);
  --bp-color-text: var(--leanpde-ink);
  --bp-color-text-strong: var(--leanpde-ink-strong);
  --bp-color-text-muted: var(--leanpde-ink-soft);
  --bp-color-text-subtle: var(--leanpde-muted);
  --bp-color-text-faint: var(--leanpde-muted);
  --bp-color-focus-border: var(--leanpde-accent);
  --bp-color-focus-surface: var(--leanpde-accent-wash);
  --bp-color-focus-ring: rgba(164, 68, 45, 0.18);
  --bp-color-target-ring: rgba(164, 68, 45, 0.22);
  --bp-color-target-surface: var(--leanpde-accent-wash);
  --bp-color-biblio-link: var(--leanpde-pde);
}

/* Figure palette. Keep these seven values in each mode synchronized with the
   standalone fallback in Blueprint/Commands/Figures.lean. `muted` is legible as a label; gridlines drawn with it
   should carry their own `stroke-opacity`. `band` fills an enclosure. */
html:root {
  --leanpde-fig-surface: #fffdf8;
  --leanpde-fig-ink: #292923;
  --leanpde-fig-muted: #706b61;
  --leanpde-fig-accent: #176b68;
  --leanpde-fig-accent-2: #a4442d;
  --leanpde-fig-band: rgba(23, 107, 104, 0.14);
  --leanpde-fig-warn: #a3302a;
}

html[data-theme="dark"] {
  --leanpde-fig-surface: #191d1c;
  --leanpde-fig-ink: #e8e6dc;
  --leanpde-fig-muted: #aaa99c;
  --leanpde-fig-accent: #7cc5bd;
  --leanpde-fig-accent-2: #eea07c;
  --leanpde-fig-band: rgba(124, 197, 189, 0.2);
  --leanpde-fig-warn: #e2796b;
}

/* The head script sets data-theme before the first paint. The same paper,
   cell and figure tokens serve both palettes. The site's root selectors
   outrank the zero-specificity fallback shipped by the figure renderer. */
html[data-theme="dark"] {
  color-scheme: dark;
  --leanpde-page: #191d1c;
  --leanpde-panel: #202625;
  --leanpde-ink: #e8e6dc;
  --leanpde-ink-strong: #f5f1e7;
  --leanpde-ink-soft: #cbcbbf;
  --leanpde-accent: #eea07c;
  --leanpde-accent-wash: #362921;
  --leanpde-pde: #7cc5bd;
  --leanpde-pde-wash: #203431;
  --leanpde-code-surface: #202524;
  --leanpde-rule: #363d38;
  --leanpde-rule-strong: #565e53;
  --leanpde-muted: #aaa99c;
  --leanpde-faint: #787d70;
  --leanpde-badge-border: #565e53;
  --leanpde-badge-text: #b4b5a7;
  --leanpde-badge-icon: #596053;
  --leanpde-badge-icon-ink: #191d1c;
  --leanpde-selection: #59402d;
  --verso-toc-background-color: #161a19;
  --verso-toc-border-color: var(--leanpde-rule);
  --verso-toc-resize-handle-color: var(--leanpde-rule-strong);
  --verso-burger-toc-hidden-color: var(--leanpde-ink-soft);
  --verso-burger-toc-hidden-shadow-color: var(--leanpde-page);
  --verso-burger-toc-visible-shadow-color: #161a19;

  /* Verso's own tokens, which its stylesheet and the search assets read. */
  --verso-warning-indicator-color: #e8b45c;
  --verso-error-indicator-color: #ef8579;
  --verso-info-indicator-color: var(--leanpde-pde);

  /* VersoBlueprint's tokens: the statement cards, relation chips, status
     badges, code panels and bibliography all read these. */
  --bp-color-surface-warn: #2a2318;
  --bp-color-surface-warn-soft: #33291a;
  --bp-color-surface-note: #2a2620;
  --bp-color-border-muted: var(--leanpde-rule);
  --bp-color-border-panel: var(--leanpde-rule);
  --bp-color-border-strong: var(--leanpde-rule-strong);
  --bp-color-accent-success: #5fbd7d;
  --bp-color-accent-warning: #d6a75c;
  --bp-color-accent-danger: #ef8579;
  --bp-color-accent-info: #b49ae8;
  --bp-color-status-success-text: #7fd097;
  --bp-color-status-warning-text: #dcb46a;
  --bp-color-status-warning-strong: #e2a978;
  --bp-color-status-warning-border: #6b5330;
  --bp-color-status-warning-border-soft: #4d3d24;
  --bp-color-status-error-text: #ef8579;
  --bp-color-status-error-strong: #f29a8f;
  --bp-color-status-error-border-soft: #5c3129;
  --bp-color-status-note-border: #6b5a30;
  --bp-color-status-note-text: #dcb46a;
  --bp-color-focus-ring: rgba(238, 160, 124, 0.18);
  --bp-color-selection: rgba(124, 197, 189, 0.24);
  --bp-color-selection-ring: rgba(124, 197, 189, 0.3);
  --bp-color-selection-surface-strong: rgba(124, 197, 189, 0.3);
  --bp-color-selection-surface-soft: rgba(124, 197, 189, 0.16);
  --bp-color-selection-surface-faint: rgba(124, 197, 189, 0.1);
  --bp-color-selection-shadow-strong: rgba(124, 197, 189, 0.32);
  --bp-color-selection-shadow-soft: rgba(124, 197, 189, 0.24);
  --bp-color-selection-shadow-faint: rgba(124, 197, 189, 0.16);
  --bp-color-target-ring: rgba(238, 160, 124, 0.26);
  --bp-color-target-ring-strong: rgba(238, 160, 124, 0.32);
  --bp-color-modern-border: var(--leanpde-rule);
  --bp-color-modern-surface-alt: var(--leanpde-panel);
  --bp-color-modern-caption: var(--leanpde-pde-wash);
  --bp-color-bold-link: var(--leanpde-accent);
  --bp-color-bold-label: #dcb46a;
  --bp-color-biblio-border: var(--leanpde-rule-strong);
  --bp-color-biblio-surface: var(--leanpde-panel);
  --bp-color-biblio-border-soft: var(--leanpde-rule);
  --bp-color-biblio-surface-soft: var(--leanpde-page);
}

body {
  color: var(--leanpde-ink);
  background: var(--leanpde-page);
  font-family: var(--verso-text-font-family);
}

main {
  min-width: 0;
  font-size: 1.0625rem;
  line-height: 1.65;
}

main p,
main li,
main dd {
  line-height: 1.65;
}

main a,
main a:visited {
  color: var(--leanpde-accent);
  text-decoration-thickness: 1px;
  text-decoration-color: var(--leanpde-rule-strong);
  text-underline-offset: 0.16em;
}

main a:hover {
  text-decoration-color: currentColor;
}

a:focus-visible,
button:focus-visible,
summary:focus-visible,
input:focus-visible,
[tabindex]:focus-visible {
  outline: 2px solid var(--leanpde-accent);
  outline-offset: 3px;
}

::selection {
  background: var(--leanpde-selection);
  color: var(--leanpde-ink-strong);
}

main h1,
main h2,
main h3,
main h4,
main h5,
main h6 {
  color: var(--leanpde-ink-strong);
  font-family: var(--verso-text-font-family);
  font-weight: 600;
  letter-spacing: -0.015em;
  overflow-wrap: normal;
  word-break: normal;
}

/* Keep the coverage table readable on narrow screens, including source paths. */
main table#pde-coverage {
  width: 100%;
  table-layout: fixed;
  border-spacing: 0.4rem;
}

main table#pde-coverage th:first-child {
  width: 26%;
}

main table#pde-coverage th:nth-child(2) {
  width: 24%;
}

main table#pde-coverage td,
main table#pde-coverage th,
main table#pde-coverage code {
  overflow-wrap: anywhere;
  white-space: normal;
}

main h1 {
  font-size: 2.1rem;
  line-height: 1.2;
}

main h2 {
  font-size: 1.45rem;
  line-height: 1.3;
}

main h3 {
  font-size: 1.15rem;
  line-height: 1.3;
}

.katex-display {
  max-width: 100%;
  overflow-x: auto;
  overflow-y: hidden;
  padding: 0.15rem 0;
}

/* Long declaration names may appear inline in mathematical prose. Let those
   names wrap on narrow screens while leaving displayed code blocks alone. */
main p > code:not(.bp_math),
main li > code:not(.bp_math),
main dd > code:not(.bp_math) {
  overflow-wrap: anywhere;
  word-break: break-word;
}

/* Successful commands carry an informational hover message. Keep that
   explanation available without drawing an editor-like blue squiggle under
   correct Lean code. Warning and error decorations remain visible. */
.hl.lean .has-info.information .token:not(.tactic-state):not(.tactic-state *),
.hl.lean .has-info.information .inter-text:not(.tactic-state):not(.tactic-state *) {
  text-decoration-line: none !important;
}

/* KaTeX's hidden accessibility tree can retain the unconstrained width of a
   displayed formula. The visible rendering remains scrollable above. */
.katex-mathml,
.katex-mathml math,
.katex-mathml semantics {
  overflow: hidden !important;
  max-width: 1px !important;
}

.katex .hide-tail,
.katex .hide-tail svg {
  overflow: hidden !important;
}

/* The sidebar carries the desktop title. On mobile, the existing header gives
   the menu button a solid bar and a home link. The quick-jump search box that
   Verso mounts into the header is moved into the sidebar by the page script. */
header {
  display: none;
}

#bp-style-switcher {
  display: none !important;
}

/* Build provenance stays in the generated metadata, outside the reading view. */
.bp_build_metadata {
  display: none !important;
}

/* Sidebar. */
#toc {
  border-right: 1px solid var(--verso-toc-border-color);
  background: var(--verso-toc-background-color);
  font-family: var(--verso-structure-font-family);
  scrollbar-width: thin;
}

#toc a,
#toc a:visited {
  color: var(--leanpde-ink-soft);
}

#toc a:hover,
html[data-theme="dark"] #toc a:hover {
  color: var(--leanpde-accent);
}

#toc .toc-title {
  display: block;
  padding: 1.2rem 1rem 0;
}

#toc .toc-title h1 {
  margin: 0;
  color: var(--leanpde-ink-strong);
  font-family: var(--verso-text-font-family);
  font-size: 1.375rem;
  font-weight: 600;
  line-height: 1.2;
  letter-spacing: -0.02em;
}

/* Keep a real heading and home-link name alongside the supplied wordmark. */
.leanpde-brand-name {
  position: absolute;
  width: 1px;
  height: 1px;
  padding: 0;
  margin: -1px;
  overflow: hidden;
  clip-path: inset(50%);
  white-space: nowrap;
}

.leanpde-wordmark {
  display: inline-flex;
  align-items: center;
  max-width: 100%;
  font-family: Georgia, "Times New Roman", serif;
  font-weight: 700;
  line-height: 1;
  letter-spacing: -0.055em;
  white-space: nowrap;
}

/* Display the original emblem between LeanP and E without changing the asset. */
.leanpde-brand-symbol {
  display: block;
  flex: none;
  width: 1.28em;
  aspect-ratio: 440 / 318;
  margin: 0 -0.035em;
  overflow: hidden;
  letter-spacing: normal;
}

.leanpde-brand-symbol img {
  display: block;
  width: 307.272727%;
  max-width: none;
  height: auto;
}

html .leanpde-wordmark .leanpde-logo-dark,
html[data-theme="dark"] .leanpde-wordmark .leanpde-logo-light {
  display: none;
}

html[data-theme="dark"] .leanpde-wordmark .leanpde-logo-dark {
  display: block;
}

#toc .leanpde-wordmark {
  font-size: 2rem;
}

#toc .leanpde-toc-subtitle {
  margin: 0.35rem 0 0;
  padding: 0 1rem;
  color: var(--leanpde-muted);
  font: 400 0.75rem/1.5 var(--verso-structure-font-family);
}

/* Verso positions the box absolutely inside the top bar; in the sidebar it is
   an ordinary block under the subtitle. */
#toc #search-wrapper {
  --search-bar-width: 100%;
  position: static !important;
  inset: auto !important;
  display: block !important;
  width: auto !important;
  height: auto !important;
  margin: 0 !important;
  padding: 0.85rem 1rem 0;
  background: transparent !important;
}

#toc #search-wrapper .combobox .group {
  width: 100%;
}

#toc #search-wrapper .combobox .cb_edit {
  border: 1px solid var(--leanpde-rule);
  border-radius: 2px;
  background: var(--leanpde-page);
  color: var(--leanpde-ink);
  font-family: var(--verso-structure-font-family);
  font-size: 0.8rem;
  padding: 0.4rem 0.55rem;
}

#toc #search-wrapper .combobox .cb_edit:focus-within {
  border-color: var(--leanpde-accent);
  outline: 2px solid var(--leanpde-accent);
  outline-offset: 2px;
}

#toc #search-wrapper .cb_edit:empty:before {
  font-family: var(--verso-structure-font-family);
}

#toc .split-tocs {
  margin-top: 1.1rem;
  padding-left: 1rem;
  padding-right: 0.75rem;
}

#toc .split-toc {
  margin-bottom: 1.1rem;
}

#toc .split-toc.book {
  margin-bottom: 1.4rem;
}

#toc .split-toc.book > .title {
  color: var(--leanpde-muted);
  font-size: 0.72rem;
  font-weight: 600;
  letter-spacing: 0.08em;
  text-transform: uppercase;
}

#toc .split-toc.book > .title label.toggle-split-toc {
  display: none;
}

/* Verso lists the sections of the current chapter under the chapter list, and
   the section rail lists the same headings while showing which one is being
   read. One of the two is enough: the sidebar carries the chapters, the rail
   carries the sections. */
#toc .split-toc:not(.book) {
  display: none;
}

#toc .split-toc.book > :not(:first-child) {
  margin-left: 0;
}

#toc .split-toc table {
  border-left: 0;
  padding-left: 0;
  padding-top: 0.3rem;
  border-collapse: collapse;
}

#toc .split-toc.book table td {
  padding: 0.25rem 0;
  font-size: 0.8rem;
  line-height: 1.4;
}

#toc .split-toc.book table td.num {
  padding-right: 0.55rem;
  color: var(--leanpde-muted);
  font-family: var(--verso-code-font-family);
  font-size: 0.78rem;
  font-variant-numeric: tabular-nums;
  white-space: nowrap;
}

/* Mark the current table-of-contents entry without Verso's dotted underline,
   which reads like an editor diagnostic in a public mathematical document. */
#toc .split-toc .current td:not(.num),
#toc .split-toc .title .current {
  text-decoration: none !important;
  font-weight: 600;
}

#toc .split-toc .current td {
  background: var(--leanpde-accent-wash);
}

#toc .split-toc .current td.num {
  box-shadow: -2px 0 var(--leanpde-accent);
}

#toc .split-toc .current td a {
  color: var(--leanpde-accent);
}

#toc .last {
  padding: 0.85rem 1rem 1rem;
  border-top: 1px solid var(--verso-toc-border-color);
  color: var(--leanpde-muted);
  font-size: 0.7rem;
  line-height: 1.5;
}

#toc .leanpde-toc-footer p {
  margin: 0;
}

#toc .leanpde-toc-footer a {
  color: inherit;
  text-decoration: underline;
  text-decoration-color: var(--leanpde-rule-strong);
}

#toc .leanpde-toc-footer a:hover {
  color: var(--leanpde-ink-strong);
  text-decoration-color: currentColor;
}

#toc .leanpde-toc-links {
  display: flex;
  gap: 0.9rem;
  margin-top: 0.2rem !important;
}

/* A source reference when the repository is not public: the path and line as
   muted text where a link would otherwise be. */
.leanpde-source-ref {
  color: var(--leanpde-muted);
  font-family: var(--verso-code-font-family);
  font-size: 0.8em;
  overflow-wrap: anywhere;
}

/* Landing page: the title, the byline, the preface prose and the pointers
   written in the root part. Verso's auto-generated contents list is hidden,
   because the sidebar is the single navigation, and so is the upper prev/next
   bar. */
main .titlepage h1 {
  text-align: left;
  margin: 1.4rem 0 0.35rem;
  font-size: 2.4rem;
  font-weight: 600;
  line-height: 1.15;
  letter-spacing: -0.025em;
}

main .titlepage .leanpde-wordmark {
  font-size: clamp(3.5rem, 7vw, 5.5rem);
}

main .titlepage .leanpde-title-subtitle {
  margin: 0;
  color: var(--leanpde-ink-soft);
  font: 400 1.1rem/1.5 var(--verso-text-font-family);
}

main .titlepage .permalink-widget,
main .titlepage + section {
  display: none;
}

/* The byline, under the title. Verso already puts ", " and " and " between the
   author spans, so we only set the type and the alignment. */
main .titlepage .authors {
  margin: 0.85rem 0 0.15rem;
  color: var(--leanpde-muted);
  font-family: var(--verso-text-font-family);
  font-size: 0.9rem;
  font-style: normal;
  text-align: left;
}

main .titlepage .leanpde-affiliation {
  margin: 0 0 1.8rem;
  color: var(--leanpde-muted);
  font: 400 0.85rem/1.5 var(--verso-text-font-family);
}

main .content-wrapper:has(.titlepage) > .prev-next-buttons:first-child {
  display: none;
}

main .titlepage dl {
  margin: 2rem 0 0;
}

main .titlepage dt {
  margin: 1.7rem 0 0.55rem;
  padding-bottom: 0.3rem;
  border-bottom: 1px solid var(--leanpde-rule);
  color: var(--leanpde-ink-soft);
  font-family: var(--verso-structure-font-family);
  font-size: 0.78rem;
  font-weight: 600;
  letter-spacing: 0.06em;
  text-transform: uppercase;
}

main .titlepage dd {
  margin: 0 0 0.6rem;
}

main .titlepage dd p {
  margin: 0 0 0.6rem;
}

/* Chapter pages list their sections; keep that list quiet. */
main .section-toc li {
  font-weight: 400;
}

/* Statement and proof cells keep the text on the page. A teal rail marks the
   mathematical statement; the quieter continuation belongs to its proof.
   Existing relation chips and declaration status badges retain their roles. */
html[data-bp-style] .bp_wrapper,
html .bp_wrapper {
  box-sizing: border-box;
  border: 0 !important;
  border-radius: 0 !important;
  background: transparent !important;
  box-shadow: none !important;
  padding: 0 !important;
}

html .bp_wrapper.bp_kind_theorem_wrapper,
html .bp_wrapper.bp_kind_definition_wrapper {
  border-top: 1px solid var(--leanpde-rule) !important;
  border-left: 2px solid var(--leanpde-pde) !important;
  padding: 0.85rem 0 0.25rem 1rem !important;
  margin: 2rem 0 0.6rem;
}

html .bp_wrapper.bp_code_panel_wrapper,
html .bp_wrapper.bp_kind_proof_wrapper {
  border-left: 2px solid var(--leanpde-rule) !important;
  padding-left: 1rem !important;
  margin: 0.65rem 0 1rem;
}

html .bp_wrapper.bp_code_panel_wrapper {
  border-left-color: var(--leanpde-accent) !important;
}

html[data-bp-style] .bp_heading,
html .bp_heading {
  border-bottom: 0 !important;
  padding-bottom: 0 !important;
  letter-spacing: 0 !important;
}

html .bp_heading .bp_caption,
html .bp_heading .bp_label {
  font-family: var(--verso-text-font-family);
  font-size: 1.05rem;
}

html .bp_heading .bp_extras,
html .bp_metadata_panel,
html .bp_code_panel > summary {
  font-family: var(--verso-structure-font-family);
}

html[data-bp-style] .bp_caption,
html .bp_caption,
html[data-bp-style] .bp_label,
html .bp_label {
  background: transparent !important;
  color: inherit !important;
  border-radius: 0 !important;
  padding: 0 !important;
  text-transform: none !important;
}

html[data-bp-style] .bp_content,
html .bp_content {
  margin-top: 0.45rem !important;
  padding-left: 0 !important;
  border-left: 0 !important;
}

.bp_wrapper:target {
  animation: none !important;
  box-shadow: none !important;
  outline: 1px solid var(--leanpde-accent);
  outline-offset: 0.5rem;
}

/* VersoBlueprint also marks ordinary chapter links as declaration targets.
   A section can contain pages of prose, so it must not inherit the declaration
   highlight. Keep scrolling to the anchor and the focus ring on the link. */
html main section.bp_decl_target,
html main :is(h1, h2, h3, h4, h5, h6).bp_decl_target {
  background: transparent !important;
  box-shadow: none !important;
  animation: none !important;
}

html .bp_metadata_panel {
  margin: 0.4rem 0 0.6rem;
  padding: 0.35rem 0 0;
  border: 0;
  border-top: 1px dotted var(--leanpde-rule);
  border-radius: 0;
  background: transparent;
}

html .bp_external_status_badge,
html .bp_code_decl_status {
  background: transparent !important;
  border-color: var(--leanpde-badge-border) !important;
  color: var(--leanpde-badge-text) !important;
}

html .bp_external_status_icon {
  background: var(--leanpde-badge-icon) !important;
  color: var(--leanpde-badge-icon-ink) !important;
  border-color: transparent !important;
  box-shadow: none !important;
}

/* The folded Lean panel is renamed for readers who are not Lean users. */
.bp_code_panel > summary .bp_code_summary_text {
  font-size: 0;
}

.bp_code_panel > summary .bp_code_summary_text::after {
  content: "Lean declarations";
  font-size: 0.8rem;
}

html .bp_code_panel > summary {
  color: var(--leanpde-accent);
  padding-block: 0.35rem;
}

html main pre.hl.lean,
html main .bp_external_decl_body > pre:not(.docstring) {
  box-sizing: border-box;
  max-width: 100%;
  overflow-x: auto;
  padding: 0.8rem 1rem;
  border: 1px solid var(--leanpde-rule);
  border-radius: 2px;
  background: var(--leanpde-code-surface);
  font-family: var(--verso-code-font-family);
  font-size: 0.82rem;
  line-height: 1.6;
  tab-size: 2;
}

.bp_external_decl_body pre.docstring {
  max-width: 100%;
  white-space: pre-wrap;
  overflow-wrap: anywhere;
  line-height: 1.5;
}

/* The opening notebook uses the same page and cell rails as the chapters.
   These rules refine its standalone stylesheet; the example switcher and
   hidden states remain owned by opening-notebook.js and opening-notebook.css. */
html .leanpde-notebook {
  margin-block: 2rem 2.5rem;
  border: 0;
  border-radius: 0;
  background: transparent;
}

/* The site header is hidden above. This header belongs to the notebook's
   content and must remain in normal reading order. */
html .leanpde-notebook > header {
  display: block;
  position: static;
  width: auto;
  height: auto;
  margin: 0;
  padding: 0 0 0.85rem;
  border: 0;
  background: transparent;
  color: inherit;
  box-shadow: none;
}

html .leanpde-notebook h2 {
  font-size: 1.45rem;
}

html .leanpde-notebook .leanpde-notebook-kicker {
  color: var(--leanpde-muted);
  font: 500 0.72rem/1.5 var(--verso-structure-font-family);
  letter-spacing: 0.04em;
}

html .leanpde-notebook .leanpde-notebook-example {
  padding: 1rem 0;
}

html .leanpde-notebook .leanpde-notebook-cell {
  --leanpde-cell-accent: var(--leanpde-accent);
  box-sizing: border-box;
  min-width: 0;
  margin: 1rem 0;
  padding: 0.25rem 0 0.25rem 1rem;
  border-left: 2px solid var(--leanpde-cell-accent);
}

html .leanpde-notebook .leanpde-notebook-result {
  --leanpde-cell-accent: var(--leanpde-pde);
}

html .leanpde-notebook .leanpde-notebook-label {
  color: var(--leanpde-cell-accent);
  font: 500 0.72rem/1.5 var(--verso-code-font-family);
  font-variant-numeric: tabular-nums;
}

html .leanpde-notebook .leanpde-notebook-controls {
  gap: 0.4rem;
  padding: 0.55rem 0;
  border-block: 1px solid var(--leanpde-rule);
  background: transparent;
  color: var(--leanpde-muted);
  font: 0.75rem/1.5 var(--verso-structure-font-family);
}

html .leanpde-notebook .leanpde-notebook-controls button {
  padding: 0.35rem 0.7rem;
  border-radius: 3px;
  color: var(--leanpde-ink-soft);
  font: inherit;
}

html .leanpde-notebook .leanpde-notebook-controls button:hover,
html .leanpde-notebook .leanpde-notebook-controls button[aria-pressed="true"] {
  border-color: var(--leanpde-accent);
  background: var(--leanpde-accent-wash);
  color: var(--leanpde-accent);
}

html .leanpde-notebook pre {
  box-sizing: border-box;
  background: var(--leanpde-code-surface);
  font-size: 0.82rem;
}

html .leanpde-notebook .leanpde-notebook-source,
html .leanpde-notebook .leanpde-notebook-definitions {
  color: var(--leanpde-muted);
  font-family: var(--verso-structure-font-family);
  font-size: 0.78rem;
}

/* Figure captions and controls use the navigation face; mathematical labels
   inside the drawing retain the surrounding text face. */
html .leanpde-fig-caption,
html .leanpde-cp-legend,
html .leanpde-cp-note {
  font-family: var(--verso-structure-font-family);
  font-size: 0.8rem;
  line-height: 1.55;
}

html .leanpde-fig {
  padding-block: 0.7rem;
  border-block: 1px solid var(--leanpde-rule);
}

html .leanpde-fig-pause {
  padding: 0.2rem 0.5rem;
  border-color: var(--leanpde-rule-strong);
  color: var(--leanpde-pde);
}

/* Header chips align right and wrap to fit the available width (Verso lays
   them out as a grid with one column per chip kind).
   The Proof map action written by `optimize-site.mjs` sits last and opens the
   atlas at the card's group. */
html .bp_heading .bp_extras {
  display: flex !important;
  flex: 1 1 auto;
  flex-wrap: wrap;
  align-items: baseline;
  justify-content: flex-end;
  column-gap: 0.65rem;
  row-gap: 0.25rem;
  width: auto;
  min-width: 0;
  max-width: 100%;
}

/* A source citation can be longer than a phone screen. Keep its full text
   readable without widening the card or clipping the other actions. */
html .bp_heading .bp_extra_slot_source,
html .bp_heading .bp_source_ref_wrap {
  max-width: 100%;
}

html .bp_heading .bp_source_ref_chip {
  max-width: 100%;
  white-space: normal;
  overflow-wrap: anywhere;
  text-align: left;
}

.leanpde-extra-slot-map {
  order: 10;
}

.leanpde-proof-map,
.leanpde-proof-map:visited {
  color: var(--leanpde-muted) !important;
  font-size: 0.78rem;
  font-weight: 600;
  text-decoration: none !important;
  white-space: nowrap;
}

.leanpde-proof-map::before {
  content: "\21B3";
  margin-right: 0.3rem;
  color: var(--leanpde-faint);
}

.leanpde-proof-map:hover {
  color: var(--leanpde-accent) !important;
  text-decoration: underline !important;
}

/* The atlas block keeps Verso's graph controls, legend, options and preview
   panel; only the canvas is replaced by the pre-rendered Graphviz views. */
.leanpde-dependency-atlas {
  position: relative;
  box-sizing: border-box;
  width: 100%;
  max-width: none;
  margin-top: 0.35rem;
}

.leanpde-dependency-atlas-stats {
  color: var(--leanpde-muted);
  font-size: 0.85rem;
  font-variant-numeric: tabular-nums;
  white-space: nowrap;
}

.leanpde-dependency-atlas-button {
  min-width: 2.4rem;
}

.leanpde-dependency-atlas-button:disabled {
  cursor: wait;
  opacity: 0.5;
}

.leanpde-dependency-atlas-canvas {
  position: relative;
  height: max(52rem, calc(100vh - 12rem)) !important;
  min-height: 52rem !important;
  max-height: none !important;
  width: 100%;
  margin-top: 0.7rem;
  overflow: hidden;
  border: 1px solid var(--leanpde-rule);
  border-radius: 2px;
  background: var(--leanpde-panel);
  cursor: grab;
  touch-action: none;
  user-select: none;
}

.leanpde-dependency-atlas-canvas[data-leanpde-loading="true"]::before,
.leanpde-dependency-atlas-canvas[data-leanpde-error="true"]::before {
  position: absolute;
  inset: 50% auto auto 50%;
  transform: translateX(-50%);
  color: var(--leanpde-muted);
  font-size: 0.95rem;
}

.leanpde-dependency-atlas-canvas[data-leanpde-loading="true"]::before {
  content: "Loading dependency graph...";
}

.leanpde-dependency-atlas-canvas[data-leanpde-error="true"]::before {
  content: "The dependency graph could not be loaded.";
}

.leanpde-dependency-atlas-canvas.is-dragging {
  cursor: grabbing;
}

.leanpde-dependency-atlas-canvas > svg {
  display: block;
  width: 100%;
  height: 100%;
  max-width: none;
}

.leanpde-dependency-atlas-canvas .node a,
.leanpde-dependency-atlas-canvas .node[tabindex],
.leanpde-dependency-atlas-canvas .cluster[data-leanpde-view] {
  cursor: pointer;
}

.leanpde-dependency-atlas-canvas .node:focus-visible {
  outline: none;
}

.leanpde-dependency-atlas-canvas .node:focus-visible > polygon,
.leanpde-dependency-atlas-canvas .node:focus-visible > ellipse,
.leanpde-dependency-atlas-canvas .node:focus-visible > path {
  stroke: var(--leanpde-accent);
  stroke-width: 3px;
}

.leanpde-dependency-atlas-canvas .cluster[data-leanpde-view]:hover > path,
.leanpde-dependency-atlas-canvas .cluster[data-leanpde-view]:hover > polygon {
  stroke: var(--leanpde-accent);
  fill: var(--leanpde-accent-wash);
}

.leanpde-dependency-atlas .bp_graph_preview {
  max-height: min(70vh, 40rem);
}

.leanpde-dependency-atlas .bp_graph_preview_body {
  max-height: min(60vh, 34rem);
}

@supports (width: 100cqw) {
  main > .content-wrapper:has(.leanpde-dependency-atlas) {
    container-type: inline-size;
    max-width: none;
  }

  main > .content-wrapper:has(.leanpde-dependency-atlas) > section {
    max-width: none;
  }

  .leanpde-dependency-atlas {
    width: 100cqw;
  }
}

@media (max-width: 700px) {
  #toc .toc-title {
    padding-top: 1.2rem;
  }

  main {
    font-size: 1rem;
  }

  main h1,
  main .titlepage h1 {
    font-size: 1.7rem;
    line-height: 1.25;
  }

  main h2 {
    font-size: 1.35rem;
    line-height: 1.3;
  }

  main h3 {
    font-size: 1.15rem;
    line-height: 1.3;
  }

  html .bp_wrapper.bp_kind_theorem_wrapper,
  html .bp_wrapper.bp_kind_definition_wrapper,
  html .bp_wrapper.bp_code_panel_wrapper,
  html .bp_wrapper.bp_kind_proof_wrapper {
    padding-left: 0.7rem !important;
  }

  html .leanpde-notebook .leanpde-notebook-cell {
    padding-left: 0.7rem;
  }

  main h1,
  main h2,
  main h3 {
    overflow-wrap: anywhere;
  }

  .leanpde-dependency-atlas-canvas {
    height: max(40rem, calc(100vh - 8rem)) !important;
    min-height: 40rem !important;
    width: 100% !important;
  }
}

/* ------------------------------------------------------------------------- */
/* Dark mode: the parts that are not reachable through a custom property.    */
/* Every rule below is scoped to `html[data-theme="dark"]`, so light mode is */
/* untouched.                                                               */

/* The field takes the user-agent text colour otherwise, which `color-scheme`
   lightens but does not warm. */
html[data-theme="dark"] #toc #search-wrapper .combobox .cb_edit {
  color: var(--leanpde-ink);
}

html[data-theme="dark"] #toc a {
  color: var(--leanpde-ink);
}

html[data-theme="dark"] .prev-next-buttons > *,
html[data-theme="dark"] .prev-next-buttons > *:visited {
  color: var(--leanpde-muted);
}

html[data-theme="dark"] ::selection {
  background: var(--leanpde-selection);
  color: var(--leanpde-ink-strong);
}

html[data-theme="dark"] main hr {
  border: 0;
  border-top: 1px solid var(--leanpde-rule);
}

html[data-theme="dark"] main blockquote {
  border-left-color: var(--leanpde-rule);
  color: var(--leanpde-ink-soft);
}

html[data-theme="dark"] main table,
html[data-theme="dark"] main th,
html[data-theme="dark"] main td {
  border-color: var(--leanpde-rule);
}

/* Lean's hover cards, message popups and tactic states are white boxes with
   black text in Verso's stylesheet. */
html[data-theme="dark"] .hl.lean .token .hover-info,
html[data-theme="dark"] .hl.lean .has-info .hover-info,
html[data-theme="dark"] .hl.lean .hover-info.messages > code,
html[data-theme="dark"] .tippy-box[data-theme~="lean"],
html[data-theme="dark"] .tippy-box[data-theme~="warning"],
html[data-theme="dark"] .tippy-box[data-theme~="error"],
html[data-theme="dark"] .tippy-box[data-theme~="info"],
html[data-theme="dark"] .tippy-box[data-theme~="tactic"] {
  background-color: var(--leanpde-panel) !important;
  color: var(--leanpde-ink) !important;
  border-color: var(--leanpde-rule-strong) !important;
}

html[data-theme="dark"] .hl.lean .hover-info code {
  color: var(--leanpde-ink);
}

html[data-theme="dark"] .hl.lean .tactic-state,
html[data-theme="dark"] .hl.lean.popup .tactic-state {
  background-color: var(--leanpde-panel);
  border-color: var(--leanpde-rule-strong);
}

html[data-theme="dark"] .hl.lean .token.binding-hl,
html[data-theme="dark"] .hl.lean .literal:hover,
html[data-theme="dark"] .hl.lean .token.typed:hover {
  background-color: var(--leanpde-pde-wash);
}

html[data-theme="dark"] .hl.lean .has-info.error:hover {
  background-color: #4a2723;
}

html[data-theme="dark"] .hl.lean .has-info.information:hover {
  background-color: var(--leanpde-pde-wash);
}

html[data-theme="dark"] .hl.lean .case-label:has(input[type="checkbox"])::before {
  background-color: var(--leanpde-muted);
}

html[data-theme="dark"] .tippy-box > .tippy-arrow::before {
  border-top-color: var(--leanpde-panel) !important;
  border-bottom-color: var(--leanpde-panel) !important;
  border-left-color: var(--leanpde-panel) !important;
  border-right-color: var(--leanpde-panel) !important;
}

/* The textbook coverage map. Its own stylesheet is written next to the map
   generator, so the dark values live here. The five coverage levels keep their
   green ramp; only the ends move so that both the light and the dark cell text
   stay readable. */
html[data-theme="dark"] .leanpde-tm-summary,
html[data-theme="dark"] .leanpde-tm-legend,
html[data-theme="dark"] .leanpde-tm-pages {
  color: var(--leanpde-ink-soft);
}

html[data-theme="dark"] .leanpde-tm-summary strong {
  color: var(--leanpde-ink-strong);
}

html[data-theme="dark"] .leanpde-tm-chapter small,
html[data-theme="dark"] .leanpde-tm-doc small,
html[data-theme="dark"] .leanpde-tm-kind,
html[data-theme="dark"] .leanpde-tm-page,
html[data-theme="dark"] .leanpde-tm-approx,
html[data-theme="dark"] .leanpde-tm-muted {
  color: var(--leanpde-muted);
}

html[data-theme="dark"] .leanpde-tm-table th,
html[data-theme="dark"] .leanpde-tm-table td {
  border-bottom-color: var(--leanpde-rule);
}

html[data-theme="dark"] .leanpde-tm-table th {
  background: var(--leanpde-panel);
}

html[data-theme="dark"] .leanpde-tm-cell,
html[data-theme="dark"] .leanpde-tm-legend-swatch {
  border-color: #3d4249;
}

html[data-theme="dark"] .leanpde-tm-level-0 {
  background: #24272d;
  color: #a8a49b;
}

html[data-theme="dark"] .leanpde-tm-level-1 {
  background: #1e3327;
  color: #8fd6a4;
}

html[data-theme="dark"] .leanpde-tm-level-2 {
  background: #27452f;
  color: #a8e2b8;
}

html[data-theme="dark"] .leanpde-tm-level-3 {
  background: #2f6b41;
  color: #dff5e5;
}

html[data-theme="dark"] .leanpde-tm-level-4 {
  background: #3f8c55;
  color: #0d1a11;
  border-color: #4d9d63;
}

html[data-theme="dark"] .leanpde-tm-none {
  color: #ef8579;
}

html[data-theme="dark"] .leanpde-tm-cas {
  background: var(--leanpde-accent-wash);
  color: var(--leanpde-accent);
}

html[data-theme="dark"] .leanpde-tm-card-cas,
html[data-theme="dark"] .leanpde-tm-cards > summary {
  color: var(--leanpde-accent);
}

/* The certified plots. The three series colours are baked into the SVG as
   presentation attributes and into the legend swatches as inline styles; a CSS
   declaration beats a presentation attribute, and `!important` beats an inline
   style, so the same three curves can be lifted for dark without regenerating
   the drawings. */
html[data-theme="dark"] .leanpde-cp {
  color: var(--leanpde-ink);
}

html[data-theme="dark"] .leanpde-cp-svg {
  background: var(--leanpde-fig-surface);
  border-color: var(--leanpde-rule);
}

html[data-theme="dark"] .leanpde-cp-axis {
  stroke: var(--leanpde-fig-muted);
}

html[data-theme="dark"] .leanpde-cp-grid {
  stroke: var(--leanpde-rule);
}

html[data-theme="dark"] .leanpde-cp-tick-label,
html[data-theme="dark"] .leanpde-cp-axis-label {
  fill: var(--leanpde-fig-muted);
}

html[data-theme="dark"] .leanpde-cp-title {
  color: var(--leanpde-ink);
}

html[data-theme="dark"] .leanpde-cp-theorems > summary {
  color: var(--leanpde-accent);
}

html[data-theme="dark"] .leanpde-cp-bar rect {
  stroke: var(--leanpde-fig-surface);
}

html[data-theme="dark"] .leanpde-cp-bar:hover rect,
html[data-theme="dark"] .leanpde-cp-bar:focus rect {
  stroke: var(--leanpde-fig-ink);
}

html[data-theme="dark"] .leanpde-cp-table tr:target {
  background: #382f16;
}

html[data-theme="dark"] .leanpde-cp-table tr:target td {
  border-bottom-color: #6d5b1f;
}

html[data-theme="dark"] .leanpde-cp-curve {
  stroke: var(--leanpde-fig-ink);
}

html[data-theme="dark"] .leanpde-cp-curve-marker {
  stroke: var(--leanpde-fig-surface);
}

html[data-theme="dark"] .leanpde-cp-note,
html[data-theme="dark"] .leanpde-cp-legend,
html[data-theme="dark"] .leanpde-cp-num {
  color: var(--leanpde-ink-soft);
}

html[data-theme="dark"] .leanpde-cp-theorems {
  color: var(--leanpde-accent);
}

html[data-theme="dark"] .leanpde-cp-table th,
html[data-theme="dark"] .leanpde-cp-table td {
  border-bottom-color: var(--leanpde-rule);
}

html[data-theme="dark"] .leanpde-cp-table th {
  background: var(--leanpde-panel);
}

html[data-theme="dark"] .leanpde-cp-svg rect[fill="#1d4ed8"] {
  fill: #7aa7e8;
}

html[data-theme="dark"] .leanpde-cp-svg rect[fill="#b45309"] {
  fill: #e8a765;
}

html[data-theme="dark"] .leanpde-cp-svg rect[fill="#0f766e"] {
  fill: #5cc0b4;
}

html[data-theme="dark"] .leanpde-cp-swatch[style*="#1d4ed8"] {
  background: #7aa7e8 !important;
}

html[data-theme="dark"] .leanpde-cp-swatch[style*="#b45309"] {
  background: #e8a765 !important;
}

html[data-theme="dark"] .leanpde-cp-swatch[style*="#0f766e"] {
  background: #5cc0b4 !important;
}

/* The dependency atlas. Graphviz bakes its palette into the SVG as `fill` and
   `stroke` attributes; the atlas page injects that SVG into the document, so a
   handful of attribute selectors re-colour it live when the theme changes,
   with no second render and no rewriting at build time. */
html[data-theme="dark"] .leanpde-dependency-atlas-canvas svg [fill="#ffffff"],
html[data-theme="dark"] .leanpde-dependency-atlas-canvas svg [fill="white"] {
  fill: var(--leanpde-panel);
}

html[data-theme="dark"] .leanpde-dependency-atlas-canvas svg [stroke="#6b7280"] {
  stroke: #8a919e;
}

html[data-theme="dark"] .leanpde-dependency-atlas-canvas svg [fill="#6b7280"] {
  fill: #8a919e;
}

html[data-theme="dark"] .leanpde-dependency-atlas-canvas svg [stroke="#cbd5e1"] {
  stroke: #414850;
}

html[data-theme="dark"] .leanpde-dependency-atlas-canvas svg [stroke="#16a34a"] {
  stroke: #5fbd7d;
}

html[data-theme="dark"] .leanpde-dependency-atlas-canvas svg [fill="#166534"] {
  fill: #8fd6a4;
}

html[data-theme="dark"] .leanpde-dependency-atlas-canvas svg text:not([fill]) {
  fill: var(--leanpde-ink-soft);
}

html[data-theme="dark"] .leanpde-dependency-atlas-canvas .cluster[data-leanpde-view]:hover > path,
html[data-theme="dark"] .leanpde-dependency-atlas-canvas .cluster[data-leanpde-view]:hover > polygon {
  fill: var(--leanpde-accent-wash);
}

/* The graph's floating panels hard-code a near-white background, and its legend
   text a near-black, in a stylesheet that ships after ours; the swatches carry
   the graph palette as inline styles. `!important` is the only thing that reaches
   all three, and the swatch colours are the same substitutions the SVG gets
   above, so the key and the drawing keep saying the same thing. */
html[data-theme="dark"] .bp_graph_legend_popover,
html[data-theme="dark"] .bp_graph_options_popover,
html[data-theme="dark"] .bp_group_hover_preview {
  background: var(--leanpde-panel) !important;
}

html[data-theme="dark"] .bp_graph_legend_item {
  color: var(--leanpde-ink) !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="background: #ffffff"] {
  background: var(--leanpde-panel) !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="background: #f8fafc"] {
  background: #23262c !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="background: #dbeafe"] {
  background: #1e2a3d !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="background: #fef3c7"] {
  background: #332c1c !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="background: #dcfce7"] {
  background: #1c2c22 !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="background: #fee2e2"] {
  background: #2e1f1e !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="background: #166534"] {
  background: #8fd6a4 !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="border-color: #6b7280"] {
  border-color: #8a919e !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="border-color: #14532d"],
html[data-theme="dark"] .bp_graph_legend_swatch[style*="border-color: #16a34a"] {
  border-color: #5fbd7d !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="border-color: #2563eb"] {
  border-color: #7aa7e8 !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="border-color: #f59e0b"] {
  border-color: #e8a765 !important;
}

html[data-theme="dark"] .bp_graph_legend_swatch[style*="border-color: #b91c1c"] {
  border-color: #e2796b !important;
}

/* ------------------------------------------------------------------------- */
/* One theme button in the sidebar footer. Each click advances through
   system, light and dark; system continues to follow the reader's device. */

/* Hidden until the script claims it, so a reader without JavaScript is not
   shown a control that cannot do anything. */
#toc .leanpde-theme {
  display: none;
}

#toc .leanpde-theme[data-leanpde-ready] {
  display: inline-flex;
}

#toc .leanpde-theme {
  align-items: center;
  margin: 0;
  min-height: 2.25rem;
  padding: 0.4rem 0.65rem;
  border: 1px solid var(--leanpde-rule);
  border-radius: 3px;
  background: transparent;
  color: var(--leanpde-ink-soft);
  font-family: var(--verso-structure-font-family);
  font-size: 0.75rem;
  line-height: 1.2;
  cursor: pointer;
}

#toc .leanpde-theme:hover {
  color: var(--leanpde-ink);
  background: var(--leanpde-accent-wash);
}

#toc .leanpde-theme:focus-visible {
  outline: 2px solid var(--leanpde-accent);
  outline-offset: 3px;
}

/* ------------------------------------------------------------------------- */
/* Reading progress: a hairline across the top of the viewport, and a pill   */
/* in the corner that carries the percentage and doubles as "back to top".   */

.leanpde-progress {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  height: 3px;
  z-index: 60;
  pointer-events: none;
  background: transparent;
}

.leanpde-progress-fill {
  height: 100%;
  width: 100%;
  background: var(--leanpde-pde);
  transform: scaleX(var(--leanpde-read, 0));
  transform-origin: 0 50%;
  transition: transform 90ms linear;
}

.leanpde-progress[hidden] {
  display: none;
}

.leanpde-top {
  position: fixed;
  right: 1.1rem;
  bottom: 1.1rem;
  z-index: 60;
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 0.05rem;
  min-width: 2.6rem;
  padding: 0.28rem 0.3rem 0.3rem;
  border: 1px solid var(--leanpde-rule);
  border-radius: 2px;
  background: var(--leanpde-page);
  color: var(--leanpde-muted);
  font-family: var(--verso-code-font-family);
  font-size: 0.68rem;
  font-variant-numeric: tabular-nums;
  line-height: 1.1;
  cursor: pointer;
  opacity: 0;
  visibility: hidden;
  transition: opacity 160ms ease;
}

.leanpde-top[data-leanpde-shown="true"] {
  opacity: 1;
  visibility: visible;
}

.leanpde-top:hover {
  color: var(--leanpde-accent);
  border-color: var(--leanpde-accent);
}

/* Keep it on screen while it has the focus ring, so a keyboard reader who has
   just used it does not lose their place in the tab order. */
.leanpde-top:focus-visible {
  opacity: 1;
  visibility: visible;
  outline: 2px solid var(--leanpde-accent);
  outline-offset: 2px;
}

/* The prev/next pair is the last thing on the page, so the pill steps aside
   rather than covering it. Focus keeps it visible either way. */
.leanpde-top[data-leanpde-clear="false"]:not(:focus-visible) {
  opacity: 0;
  visibility: hidden;
}

.leanpde-top-arrow {
  font-size: 0.8rem;
  line-height: 1;
}

.leanpde-top[hidden] {
  display: none;
}

/* ------------------------------------------------------------------------- */
/* The section rail. On a wide screen it is a column to the right of the     */
/* text: the chapter name at the top, the page's headings under it, and the  */
/* one the reader is looking at marked. Below 1280px there is no room beside */
/* the text, so the same markup folds into a jump list at the top of the     */
/* page. Neither form ever overlaps the text.                               */

.leanpde-rail {
  margin: 0;
  padding: 0 var(--verso--content-padding-x);
  font-family: var(--verso-structure-font-family);
}

.leanpde-rail-box {
  max-width: var(--verso-content-max-width);
  padding: 0.55rem 0 0.15rem;
}

.leanpde-rail-chapter {
  display: none;
}

.leanpde-rail-head {
  display: flex;
  align-items: baseline;
  gap: 0.5rem;
  margin: 0;
}

.leanpde-rail-label {
  color: var(--leanpde-muted);
  font-size: 0.7rem;
  font-weight: 600;
  letter-spacing: 0.09em;
  text-transform: uppercase;
}

.leanpde-rail-here {
  flex: 1 1 auto;
  min-width: 0;
  overflow: hidden;
  color: var(--leanpde-ink-soft);
  font-size: 0.8rem;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.leanpde-rail-toggle {
  flex: 0 0 auto;
  display: inline-flex;
  align-items: center;
  gap: 0.3rem;
  margin-left: auto;
  padding: 0.1rem 0.25rem;
  border: 0;
  background: transparent;
  color: var(--leanpde-accent);
  font-family: inherit;
  font-size: 0.76rem;
  cursor: pointer;
}

.leanpde-rail-toggle:focus-visible {
  outline: 2px solid var(--leanpde-accent);
  outline-offset: 1px;
}

.leanpde-rail-chevron {
  font-size: 0.6rem;
  transition: transform 140ms ease;
}

.leanpde-rail[data-leanpde-open="true"] .leanpde-rail-chevron {
  transform: rotate(180deg);
}

.leanpde-rail-list {
  display: none;
  position: relative;
  margin: 0.4rem 0 0;
  padding: 0;
  max-height: min(58vh, 24rem);
  overflow-y: auto;
  overscroll-behavior: contain;
  list-style: none;
}

.leanpde-rail[data-leanpde-open="true"] .leanpde-rail-list {
  display: block;
}

.leanpde-rail-item > a,
.leanpde-rail-item > a:visited {
  display: block;
  padding: 0.17rem 0 0.17rem 0.7rem;
  border-left: 1px solid var(--leanpde-rule);
  color: var(--leanpde-muted);
  font-size: 0.82rem;
  line-height: 1.35;
  text-decoration: none;
}

.leanpde-rail-item > a:hover {
  color: var(--leanpde-accent);
  border-left-color: var(--leanpde-accent);
}

.leanpde-rail-item > a:focus-visible {
  outline: 2px solid var(--leanpde-accent);
  outline-offset: -2px;
}

.leanpde-rail-item[data-leanpde-current="true"] > a {
  border-left: 2px solid var(--leanpde-accent);
  padding-left: calc(0.7rem - 1px);
  color: var(--leanpde-ink-strong);
  font-weight: 600;
}

.leanpde-rail-num {
  margin-right: 0.35rem;
  color: var(--leanpde-muted);
  font-family: var(--verso-code-font-family);
  font-size: 0.72rem;
  font-variant-numeric: tabular-nums;
}

.leanpde-rail-level-3 > a {
  padding-left: 1.5rem;
  font-size: 0.79rem;
}

.leanpde-rail-level-3[data-leanpde-current="true"] > a {
  padding-left: calc(1.5rem - 1px);
}

.leanpde-rail-level-4 > a {
  padding-left: 2.3rem;
  font-size: 0.77rem;
}

.leanpde-rail-level-4[data-leanpde-current="true"] > a {
  padding-left: calc(2.3rem - 1px);
}

/* Wide screens. Centre the 47rem reader, or the reader and its section rail
   together. The atlas keeps its full-width canvas. 1280px is where the pair
   first fits next to a 17rem sidebar. */
@media screen and (min-width: 1280px) {
  main:not(:has(> .leanpde-rail)) > .content-wrapper:not(:has(.leanpde-dependency-atlas)) {
    max-width: var(--verso-content-max-width);
    margin-inline: auto;
  }

  main:has(> .leanpde-rail) {
    display: grid;
    grid-template-columns:
      minmax(0, calc(var(--verso-content-max-width) + 2 * var(--verso--content-padding-x)))
      var(--leanpde-rail-width);
    column-gap: clamp(1rem, 2vw, 3rem);
    justify-content: center;
    align-items: start;
  }

  main:has(> .leanpde-rail) > :not(.leanpde-rail) {
    grid-column: 1;
  }

  main:has(> .leanpde-rail) > .content-wrapper {
    margin-inline: 0;
    max-width: none;
  }

  main > .leanpde-rail {
    grid-column: 2;
    grid-row: 1;
    position: sticky;
    top: 1.6rem;
    padding: 0;
  }

  main > .leanpde-rail .leanpde-rail-box {
    max-width: none;
    padding: 0;
  }

  main > .leanpde-rail .leanpde-rail-chapter {
    display: block;
    margin: 0 0 0.55rem;
    padding-bottom: 0.4rem;
    border-bottom: 1px solid var(--leanpde-rule);
    color: var(--leanpde-ink-soft);
    font-size: 0.82rem;
    font-weight: 600;
    line-height: 1.3;
  }

  main > .leanpde-rail .leanpde-rail-here,
  main > .leanpde-rail .leanpde-rail-toggle {
    display: none;
  }

  /* Always open here, and scrollable on its own so a chapter with forty
     headings still fits beside the text. */
  main > .leanpde-rail .leanpde-rail-list {
    display: block;
    margin-top: 0;
    max-height: calc(100dvh - 9rem);
    scrollbar-width: thin;
  }
}

/* ------------------------------------------------------------------------- */
/* Anchors, motion, print.                                                  */

/* Rail and sidebar section links scroll instead of jumping. On mobile the
   scroll container reserves the header's height; targets add a little space. */
html {
  scroll-behavior: smooth;
}

@media (prefers-reduced-motion: reduce) {
  html {
    scroll-behavior: auto;
  }

  .leanpde-progress-fill,
  .leanpde-top,
  .leanpde-rail-chevron {
    transition: none;
  }
}

/* Reuse Verso's real title and home link. The existing native menu button stays
   above this bar; its drawer and keyboard handling do not depend on the header. */
@media screen and (max-width: 700px) {
  html:root {
    --verso-header-height: 3.25rem;
    scroll-padding-top: var(--verso-header-height);
  }

  body > header {
    display: flex;
    background: var(--leanpde-page);
    border-bottom: 1px solid var(--leanpde-rule);
    box-shadow: none;
  }

  body > header .header-title-wrapper {
    min-width: 0;
  }

  body > header .header-title {
    display: block;
    margin: 0 1rem 0 3.25rem;
    color: var(--leanpde-ink-strong);
    font: 600 0.875rem/1.25 var(--verso-text-font-family);
  }

  body > header .header-title h1 {
    margin: 0;
  }

  body > header .leanpde-wordmark {
    font-size: 1.35rem;
  }

  .with-toc #toc {
    top: var(--verso-header-height);
  }

  main [id] {
    scroll-margin-top: 1rem;
  }

  #toggle-toc-click {
    top: calc((var(--verso-header-height) - var(--verso-burger-height) - 1rem) / 2);
    border: 0;
    background: transparent;
  }
}

@media print {
  html .leanpde-wordmark .leanpde-logo-light {
    display: block !important;
  }

  html .leanpde-wordmark .leanpde-logo-dark {
    display: none !important;
  }

  .leanpde-progress,
  .leanpde-top,
  .leanpde-rail,
  .leanpde-theme {
    display: none !important;
  }

  html:root,
  html:root[data-theme="dark"] {
    --leanpde-page: #ffffff;
    --leanpde-panel: #ffffff;
    --leanpde-code-surface: #ffffff;
    --leanpde-ink: #222222;
    --leanpde-ink-strong: #111111;
    --leanpde-ink-soft: #333333;
    --leanpde-muted: #555555;
    --leanpde-accent: #713322;
    --leanpde-pde: #235451;
    --leanpde-rule: #cccccc;
    --leanpde-rule-strong: #999999;
    --leanpde-fig-surface: var(--leanpde-page);
    --leanpde-fig-ink: var(--leanpde-ink);
    --leanpde-fig-muted: var(--leanpde-muted);
    --leanpde-fig-accent: var(--leanpde-pde);
    --leanpde-fig-accent-2: var(--leanpde-accent);
    color-scheme: light;
  }
}

/* Printed command output can grow with the calculation; hover views stay scrollable. */
.hl.lean .hover-info.messages {
  max-height: min(70vh, 40rem);
}
.lean-output .hl.lean .hover-info.messages {
  max-height: none;
  overflow: visible;
  padding: 0;
}
.lean-output .hl.lean .hover-info.messages > code {
  width: auto;
  max-width: 100%;
  box-sizing: border-box;
  overflow-wrap: anywhere;
  white-space: pre-wrap;
}
.lean-output .verso-message .token,
.lean-output .verso-message .text {
  white-space: pre-wrap;
  overflow-wrap: anywhere;
}
.verso-message .trace-class { display: none; }
.verso-message .trace > summary { color: var(--leanpde-ink-strong); }
.verso-message .trace-children > li { margin-left: 0.8em; }
.leanpde-tm-muted, .leanpde-tm-citation,
.bp_external_decl_meta, .bp_external_decl_head_meta,
.bp_external_decl_rendered .inheritance {
  color: var(--leanpde-muted) !important;
}
@media (max-width: 700px) {
  #highlight-controls { min-width: 0; }
}
"##

/-- Move Verso's quick-jump search box into the sidebar.

Verso mounts the box into the fixed top bar once the page has loaded. The top
bar is hidden because the sidebar carries the one title of the site, so the
box is moved under the sidebar subtitle as soon as it appears. -/
private def siteShellSetup : JS := r##"
(function () {
  var root = document.documentElement;
  var THEME_KEY = "leanpde-theme";
  var THEME_COLORS = { light: "#fffdf8", dark: "#191d1c" };
  var themeChoice = null;
  var darkQuery = window.matchMedia ? window.matchMedia("(prefers-color-scheme: dark)") : null;
  var motionQuery = window.matchMedia ? window.matchMedia("(prefers-reduced-motion: reduce)") : null;

  function prefersReducedMotion() {
    return !!(motionQuery && motionQuery.matches);
  }

  /* ---------------------------------------------------------------- theme */

  // `?theme=light` and `?theme=dark` decide the theme for this page load only
  // and are never stored, so a link can carry a theme and a screenshot can ask
  // for one. Anything else in the query string is ignored.
  function forcedTheme() {
    var match = /[?&]theme=([^&]*)/.exec(window.location.search);
    if (!match) return null;
    var value = match[1];
    return value === "light" || value === "dark" ? value : null;
  }

  function storedChoice() {
    try {
      var value = window.localStorage.getItem(THEME_KEY);
      if (value === "light" || value === "dark" || value === "system") return value;
    } catch (error) {
      /* Private browsing, or storage denied: fall back to the media query. */
    }
    return null;
  }

  function storeChoice(choice) {
    try {
      window.localStorage.setItem(THEME_KEY, choice);
    } catch (error) {
      /* Nothing to do: the choice then lasts for this page only. */
    }
  }

  function resolve(choice) {
    if (choice === "light" || choice === "dark") return choice;
    return darkQuery && darkQuery.matches ? "dark" : "light";
  }

  function paint(theme) {
    root.dataset.theme = theme;
    var meta = document.getElementById("leanpde-theme-color");
    if (meta) meta.setAttribute("content", THEME_COLORS[theme] || THEME_COLORS.light);
  }

  function nextTheme(choice) {
    return choice === "system" ? "light" : choice === "light" ? "dark" : "system";
  }

  function markControl(control, choice) {
    var label = "Theme: " + choice;
    control.textContent = label;
    control.setAttribute("data-leanpde-theme", choice);
    control.setAttribute("aria-label", label + ". Switch to " + nextTheme(choice) + " theme.");
    control.title = "Cycle between system, light and dark";
  }

  // Runs while the document head is still parsing, so the theme is settled
  // before anything is painted. The control is wired up once the sidebar exists.
  function setUpTheme() {
    themeChoice = forcedTheme() || storedChoice() || "system";
    paint(resolve(themeChoice));
    if (!darkQuery) return;
    var follow = function () {
      if (themeChoice === "system") paint(resolve("system"));
    };
    if (darkQuery.addEventListener) darkQuery.addEventListener("change", follow);
    else if (darkQuery.addListener) darkQuery.addListener(follow);
  }

  function setUpThemeControl() {
    var control = document.querySelector(".leanpde-theme");
    if (!control) return;
    markControl(control, themeChoice);
    control.setAttribute("data-leanpde-ready", "true");
    control.addEventListener("click", function () {
      themeChoice = nextTheme(themeChoice);
      storeChoice(themeChoice);
      paint(resolve(themeChoice));
      markControl(control, themeChoice);
    });
  }

  /* ------------------------------------------------------------- sidebar */

  function setUpMobileToc() {
    var toc = document.getElementById("toc");
    var checked = document.getElementById("toggle-toc");
    var label = document.getElementById("toggle-toc-click");
    if (!toc || !checked || !label) return;
    var mobile = window.matchMedia("(max-width: 700px)");
    var main = document.querySelector("main");
    var backdrop = document.querySelector(".toc-backdrop");

    // Keep Verso's checkbox for its drawer styles, but use a native control.
    var button = document.createElement("button");
    button.type = "button";
    button.id = label.id;
    button.className = label.className;
    button.setAttribute("aria-controls", toc.id);
    while (label.firstChild) button.appendChild(label.firstChild);
    label.replaceWith(button);
    if (!toc.hasAttribute("aria-label")) toc.setAttribute("aria-label", "Table of contents");

    function isOpen() {
      return mobile.matches && checked.checked;
    }

    function sync() {
      var open = isOpen();
      toc.inert = mobile.matches && !open;
      if (toc.inert) toc.setAttribute("aria-hidden", "true");
      else toc.removeAttribute("aria-hidden");
      if (main) main.inert = open;
      button.setAttribute("aria-expanded", String(open));
      button.setAttribute("aria-label", open ? "Close table of contents" : "Open table of contents");
    }

    function setOpen(open, restoreFocus) {
      checked.checked = mobile.matches && open;
      sync();
      if (restoreFocus && mobile.matches) button.focus({ preventScroll: true });
    }

    function focusableItems() {
      var candidates = toc.querySelectorAll(
        "a[href], button, input, select, textarea, summary, [tabindex], [contenteditable='true']",
      );
      return [button].concat([].slice.call(candidates).filter(function (item) {
        return item.tabIndex >= 0 && !item.disabled && !item.closest("[inert]")
          && item.getClientRects().length > 0 && getComputedStyle(item).visibility !== "hidden";
      }));
    }

    button.addEventListener("click", function () {
      setOpen(!isOpen(), false);
    });
    checked.addEventListener("change", function () {
      sync();
      if (!isOpen() && mobile.matches && toc.contains(document.activeElement)) {
        button.focus({ preventScroll: true });
      }
    });
    if (backdrop) {
      // Replace Verso's inline click forwarder so one click closes the drawer once.
      backdrop.removeAttribute("onclick");
      backdrop.addEventListener("click", function () { setOpen(false, true); });
    }
    toc.addEventListener("click", function (event) {
      if (!isOpen() || event.defaultPrevented || event.button !== 0
        || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
      if (event.target.closest("a[href]")) setOpen(false, true);
    });
    document.addEventListener("keydown", function (event) {
      if (!isOpen() || event.defaultPrevented || event.key !== "Escape") return;
      var search = event.target.closest("#search-wrapper");
      var input = search && search.querySelector("#cb1-input");
      // An open search handles Escape itself. Its closed input also consumes
      // Escape, so close the drawer during capture before that handler runs.
      if (input && input.getAttribute("aria-expanded") === "true") return;
      event.preventDefault();
      event.stopPropagation();
      setOpen(false, true);
    }, true);
    document.addEventListener("keydown", function (event) {
      if (!isOpen() || event.defaultPrevented) return;
      if (event.key === "Tab") {
        var items = focusableItems();
        var first = items[0];
        var last = items[items.length - 1];
        var active = document.activeElement;
        if (event.shiftKey && (active === first || items.indexOf(active) < 0)) {
          event.preventDefault();
          last.focus();
        } else if (!event.shiftKey && (active === last || items.indexOf(active) < 0)) {
          event.preventDefault();
          first.focus();
        }
      }
    });

    function syncViewport() {
      var active = document.activeElement;
      if (!mobile.matches) checked.checked = false;
      sync();
      if (mobile.matches && !isOpen() && toc.contains(active)) {
        button.focus({ preventScroll: true });
      } else if (!mobile.matches && active === button) {
        var first = toc.querySelector("a[href]");
        if (first) first.focus({ preventScroll: true });
      }
    }
    if (mobile.addEventListener) mobile.addEventListener("change", syncViewport);
    else mobile.addListener(syncViewport);
    syncViewport();
  }

  function setUpSearchAccessibility(box) {
    var input = box.querySelector("#cb1-input");
    var listbox = box.querySelector('[role="listbox"]');
    if (!input || !listbox || box.hasAttribute("data-leanpde-search-ready")) return;
    box.setAttribute("data-leanpde-search-ready", "true");
    var nextId = 0;

    function syncOptions() {
      // Verso refers to the selected option by ID, but can render unnamed options.
      listbox.querySelectorAll('[role="option"]').forEach(function (option) {
        if (option.id) return;
        var id;
        do { id = "leanpde-search-option-" + (++nextId); }
        while (document.getElementById(id));
        option.id = id;
      });
      var selected = listbox.querySelector('[role="option"][aria-selected="true"]');
      var active = input.getAttribute("aria-expanded") === "true"
        && listbox.classList.contains("focus") && selected ? selected.id : "";
      if (input.getAttribute("aria-activedescendant") !== active) {
        input.setAttribute("aria-activedescendant", active);
      }
    }

    syncOptions();
    new MutationObserver(syncOptions).observe(listbox, {
      childList: true, subtree: true, attributes: true, attributeFilter: ["aria-selected"],
    });
  }

  // Verso mounts its quick-jump search box in the top bar, which this site does
  // not show. Move it into the sidebar, under the subtitle.
  function placeSearchBox() {
    var box = document.getElementById("search-wrapper");
    var first = document.querySelector("#toc .first");
    if (!box || !first) return false;
    setUpSearchAccessibility(box);
    if (box.parentNode === first) return true;
    var anchor = first.querySelector(".leanpde-toc-subtitle")
      || first.querySelector(".toc-title");
    if (anchor && anchor.parentNode === first) {
      first.insertBefore(box, anchor.nextSibling);
    } else {
      first.insertBefore(box, first.firstChild);
    }
    return true;
  }

  function watchHeader() {
    var header = document.querySelector("header");
    if (!header || placeSearchBox()) return;
    var observer = new MutationObserver(function () {
      if (placeSearchBox()) observer.disconnect();
    });
    observer.observe(header, { childList: true });
  }

  /* ------------------------------------------------------------ progress */

  // Progress is measured through the main element, so the last paragraph reads
  // 100 per cent whatever follows it. The metrics are read on resize and on
  // load, never inside the scroll handler, which only reads `scrollY`.
  function setUpProgress() {
    var main = document.querySelector("main");
    var bar = document.querySelector(".leanpde-progress");
    var fill = bar && bar.querySelector(".leanpde-progress-fill");
    var pill = document.querySelector(".leanpde-top");
    var readout = pill && pill.querySelector(".leanpde-top-pct");
    if (!main || !bar || !fill) return null;

    var start = 0;
    var span = 0;
    var scrollable = false;
    var lastPercent = -1;
    var atEnd = false;
    var listeners = [];

    function measure() {
      var viewport = window.innerHeight;
      var rect = main.getBoundingClientRect();
      var top = rect.top + window.scrollY;
      var bottom = top + main.offsetHeight;
      var document_ = document.documentElement;
      scrollable = document_.scrollHeight > viewport + 8;
      start = Math.max(0, top);
      span = Math.max(0, bottom - viewport - start);
      if (span < 40) span = Math.max(0, document_.scrollHeight - viewport - start);
      if (!scrollable) {
        bar.setAttribute("hidden", "hidden");
        if (pill) pill.setAttribute("hidden", "hidden");
      } else {
        bar.removeAttribute("hidden");
        if (pill) pill.removeAttribute("hidden");
      }
    }

    function draw() {
      if (!scrollable) return;
      var offset = window.scrollY - start;
      var fraction = span > 0 ? offset / span : offset > 0 ? 1 : 0;
      if (fraction < 0) fraction = 0;
      if (fraction > 1) fraction = 1;
      fill.style.setProperty("--leanpde-read", String(fraction));
      var percent = Math.round(fraction * 100);
      if (percent !== lastPercent) {
        lastPercent = percent;
        if (readout) readout.textContent = percent + "%";
      }
      if (pill) {
        pill.setAttribute(
          "data-leanpde-shown",
          window.scrollY > window.innerHeight * 0.75 ? "true" : "false",
        );
      }
      var ended = fraction > 0.995;
      if (ended !== atEnd) {
        atEnd = ended;
        for (var i = 0; i < listeners.length; i += 1) listeners[i](ended);
      }
    }

    var ticking = false;
    function schedule() {
      if (ticking) return;
      ticking = true;
      window.requestAnimationFrame(function () {
        ticking = false;
        draw();
      });
    }

    function remeasure() {
      measure();
      schedule();
    }

    measure();
    draw();
    window.addEventListener("scroll", schedule, { passive: true });
    window.addEventListener("resize", remeasure);
    window.addEventListener("load", remeasure);
    if (window.ResizeObserver) new ResizeObserver(remeasure).observe(main);

    if (pill) {
      pill.addEventListener("click", function () {
        window.scrollTo({ top: 0, behavior: prefersReducedMotion() ? "auto" : "smooth" });
      });
    }

    return {
      onEnd: function (listener) {
        listeners.push(listener);
      },
    };
  }

  /* ------------------------------------------------------- end clearance */

  // Nothing follows the main element except the closing tags, so the corner
  // pill sits over the prev/next pair at the foot of a chapter. The pill steps
  // aside while that pair is on screen. An observer does this without reading
  // any geometry during a scroll.
  function setUpEndClearance() {
    var pill = document.querySelector(".leanpde-top");
    var pairs = document.querySelectorAll(".prev-next-buttons");
    if (!pill || pairs.length === 0 || !window.IntersectionObserver) return;
    var last = pairs[pairs.length - 1];
    new IntersectionObserver(
      function (entries) {
        for (var i = 0; i < entries.length; i += 1) {
          pill.setAttribute("data-leanpde-clear", entries[i].isIntersecting ? "false" : "true");
        }
      },
      { rootMargin: "0px 0px 24px 0px", threshold: 0 },
    ).observe(last);
  }

  /* ----------------------------------------------------------- page rail */

  // The rail is written into the page by `optimize-site.mjs`, so it is there
  // before the first paint and works without this script. What is added here is
  // the mark that follows the reader, and the narrow-screen disclosure.
  function setUpRail(progress) {
    var rail = document.querySelector(".leanpde-rail");
    if (!rail) return;
    var list = rail.querySelector(".leanpde-rail-list");
    var here = rail.querySelector(".leanpde-rail-here");
    var items = [].slice.call(rail.querySelectorAll(".leanpde-rail-item"));
    if (!list || items.length === 0) return;

    var states = [];
    var byTarget = new Map();
    for (var i = 0; i < items.length; i += 1) {
      var id = items[i].getAttribute("data-leanpde-target");
      var heading = id ? document.getElementById(id) : null;
      if (!heading) continue;
      byTarget.set(heading, states.length);
      states.push({ item: items[i], heading: heading, visible: false, top: 1 });
    }
    if (states.length === 0) return;

    var current = -1;

    function keepInView(item) {
      if (list.scrollHeight <= list.clientHeight + 4) return;
      var link = item.firstElementChild;
      if (!link) return;
      var top = link.offsetTop;
      var bottom = top + link.offsetHeight;
      if (top < list.scrollTop + 8) list.scrollTop = Math.max(0, top - 8);
      else if (bottom > list.scrollTop + list.clientHeight - 8) {
        list.scrollTop = bottom - list.clientHeight + 8;
      }
    }

    function mark(index) {
      if (index === current || index < 0 || index >= states.length) return;
      if (current >= 0) states[current].item.removeAttribute("data-leanpde-current");
      current = index;
      var item = states[index].item;
      item.setAttribute("data-leanpde-current", "true");
      if (here) here.textContent = item.getAttribute("data-leanpde-short") || "";
      keepInView(item);
    }

    function pick() {
      for (var i = 0; i < states.length; i += 1) {
        if (states[i].visible) return mark(i);
      }
      for (var j = states.length - 1; j >= 0; j -= 1) {
        if (states[j].top < 0) return mark(j);
      }
      return mark(0);
    }

    // The band is the top third of the viewport: the heading a reader is under
    // is the last one to have crossed it. `boundingClientRect` comes with the
    // entry, so no measurement happens outside this callback.
    var observer = new IntersectionObserver(
      function (entries) {
        for (var i = 0; i < entries.length; i += 1) {
          var index = byTarget.get(entries[i].target);
          if (index === undefined) continue;
          states[index].visible = entries[i].isIntersecting;
          states[index].top = entries[i].boundingClientRect.top;
        }
        pick();
      },
      { rootMargin: "-8px 0px -67% 0px", threshold: 0 },
    );
    for (var k = 0; k < states.length; k += 1) observer.observe(states[k].heading);

    // At the very bottom of a page the last heading may never reach the band.
    if (progress) {
      progress.onEnd(function (ended) {
        if (ended) mark(states.length - 1);
      });
    }

    var toggle = rail.querySelector(".leanpde-rail-toggle");
    if (toggle) {
      toggle.removeAttribute("hidden");
      toggle.addEventListener("click", function () {
        var open = rail.getAttribute("data-leanpde-open") === "true";
        rail.setAttribute("data-leanpde-open", open ? "false" : "true");
        toggle.setAttribute("aria-expanded", open ? "false" : "true");
        if (!open && current >= 0) keepInView(states[current].item);
      });
      list.addEventListener("click", function (event) {
        if (event.target.closest("a")) {
          rail.setAttribute("data-leanpde-open", "false");
          toggle.setAttribute("aria-expanded", "false");
        }
      });
      rail.addEventListener("keydown", function (event) {
        if (event.key !== "Escape") return;
        if (rail.getAttribute("data-leanpde-open") !== "true") return;
        rail.setAttribute("data-leanpde-open", "false");
        toggle.setAttribute("aria-expanded", "false");
        toggle.focus();
      });
    }
  }

  /* ------------------------------------------------------ incoming hashes */

  // A link into a proof or a Lean panel lands inside a closed <details>. Open
  // the ancestors and scroll again, since the browser has already given up.
  function revealHash() {
    var id = window.location.hash.slice(1);
    if (!id) return;
    var target = null;
    try {
      target = document.getElementById(decodeURIComponent(id));
    } catch (error) {
      target = document.getElementById(id);
    }
    if (!target) return;
    var opened = false;
    for (var node = target.parentElement; node; node = node.parentElement) {
      if (node.tagName === "DETAILS" && !node.open) {
        node.open = true;
        opened = true;
      }
    }
    if (opened) target.scrollIntoView({ block: "start", behavior: "auto" });
  }

  /* ---------------------------------------------------------------- start */

  setUpTheme();

  function start() {
    setUpThemeControl();
    watchHeader();
    setUpMobileToc();
    var progress = setUpProgress();
    setUpRail(progress);
    setUpEndClearance();
    revealHash();
    window.addEventListener("hashchange", revealHash);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", start, { once: true });
  } else {
    start();
  }
})();
"##

/-- Drive the atlas page with the pre-rendered Graphviz views.

The generated graph block is claimed while the document is still parsing, so
Verso's graph runtime never sees a `.bp_graph_fullwidth` block and the browser
never downloads D3 or Graphviz-WASM for this large graph. Verso's Legend button
and popover, the View selector, the preview-behaviour options and the preview
panel are kept; only the canvas is replaced by a lightweight SVG viewer, and
node previews are rendered through the generated `api/preview.mjs` module.

The page opens on the group overview, which is the entry point to a graph of
more than a thousand statements; the full graph and every focused group view
are one selection away and are addressable as `#view=full` and
`#view=parent:...` in the URL. Every view first appears fitted to the canvas,
whose height follows the shape of the graph, so nothing is cut off on first
paint; Reset zooms to the readable scale and Fit returns to the whole graph. -/
private def dependencyGraphPageSetup : JS := r##"
(function () {
  var XLINK_NS = "http://www.w3.org/1999/xlink";

  function isLeanPDEDependencyGraphPage() {
    return /\/Dependency-Atlas(?:\/index\.html|\/)?$/.test(window.location.pathname);
  }

  if (!isLeanPDEDependencyGraphPage()) return;
  document.documentElement.classList.add("leanpde-dependency-page");

  function claimLeanPDEAtlasBlock(block) {
    if (!(block instanceof Element)) return;
    if (block.getAttribute("data-leanpde-atlas") === "claimed") return;
    block.classList.remove("bp_graph_fullwidth");
    block.classList.add("leanpde-dependency-atlas");
    block.setAttribute("data-leanpde-atlas", "claimed");
  }

  function claimLeanPDEAtlasBlocks(root) {
    if (root instanceof Element && root.matches(".bp_graph_fullwidth")) {
      claimLeanPDEAtlasBlock(root);
    }
    if (root && typeof root.querySelectorAll === "function") {
      root.querySelectorAll(".bp_graph_fullwidth").forEach(claimLeanPDEAtlasBlock);
    }
  }

  var claimObserver = new MutationObserver(function (records) {
    records.forEach(function (record) {
      record.addedNodes.forEach(claimLeanPDEAtlasBlocks);
    });
  });
  claimObserver.observe(document.documentElement, { childList: true, subtree: true });
  claimLeanPDEAtlasBlocks(document);

  function makeLeanPDEAtlasButton(label, title) {
    var button = document.createElement("button");
    button.type = "button";
    button.className = "bp_graph_controls_button leanpde-dependency-atlas-button";
    button.textContent = label;
    button.title = title;
    button.setAttribute("aria-label", title);
    button.disabled = true;
    return button;
  }

  function parseLeanPDEAtlasViewBox(svg) {
    var values = (svg.getAttribute("viewBox") || "")
      .trim()
      .split(/\s+/)
      .map(Number);
    if (values.length !== 4 || values.some(function (value) {
      return !Number.isFinite(value);
    })) {
      throw new Error("The pre-rendered dependency graph has no valid viewBox.");
    }
    return { x: values[0], y: values[1], width: values[2], height: values[3] };
  }

  function fitLeanPDEAtlasView(bounds, aspect) {
    var padding = 0.025;
    var width = bounds.width * (1 + 2 * padding);
    var height = bounds.height * (1 + 2 * padding);
    if (width / height > aspect) {
      height = width / aspect;
    } else {
      width = height * aspect;
    }
    return {
      x: bounds.x + bounds.width / 2 - width / 2,
      y: bounds.y + bounds.height / 2 - height / 2,
      width: width,
      height: height
    };
  }

  function readableLeanPDEAtlasView(bounds, canvas, aspect) {
    var graphFontSize = 10;
    var targetFontPixels = 11;
    var width = Math.min(
      bounds.width,
      Math.max(280, canvas.clientWidth * graphFontSize / targetFontPixels)
    );
    var height = Math.min(bounds.height, width / aspect);
    return {
      x: bounds.x + bounds.width / 2 - width / 2,
      y: bounds.y + bounds.height / 2 - height / 2,
      width: width,
      height: height
    };
  }

  function readLeanPDEGraphData(block) {
    var script = block.querySelector("script.bp-graph-data");
    if (!script) return null;
    try {
      return JSON.parse(script.textContent || "null");
    } catch (error) {
      console.error(error);
      return null;
    }
  }

  function siteUrl(path) {
    return new URL(path, document.baseURI).href;
  }

  function labelOfPreviewKey(previewKey) {
    return String(previewKey || "")
      .replace(/--statement$/, "")
      .replace(/^«/, "")
      .replace(/»$/, "");
  }

  function readNodeHref(node) {
    var links = node.querySelectorAll("a");
    for (var i = 0; i < links.length; i += 1) {
      var href = links[i].getAttribute("href")
        || links[i].getAttributeNS(XLINK_NS, "href");
      if (href) return siteUrl(href);
    }
    return "";
  }

  function textOf(element) {
    return Array.prototype.map.call(element.querySelectorAll("text"), function (text) {
      return (text.textContent || "").trim();
    }).join(" ").replace(/\s+/g, " ").trim();
  }

  function formatCount(value) {
    return Number(value).toLocaleString("en-US");
  }

  function positionLeanPDEPopover(_controller, rootNode, triggerNode, panelNode) {
    if (!(rootNode instanceof Element)) return;
    if (!(triggerNode instanceof Element)) return;
    if (!(panelNode instanceof HTMLElement)) return;
    var rootRect = rootNode.getBoundingClientRect();
    var triggerRect = triggerNode.getBoundingClientRect();
    var top = Math.max(0, Math.round(triggerRect.bottom - rootRect.top + 8));
    panelNode.style.top = top + "px";
    if (rootRect.width <= 720) {
      panelNode.style.left = "0px";
      panelNode.style.right = "0px";
      return;
    }
    var right = Math.max(0, Math.round(rootRect.right - triggerRect.right));
    panelNode.style.left = "";
    panelNode.style.right = right + "px";
  }

  function bindLeanPDEPopover(previewApi, block, buttonSelector, panelSelector, closeSelector, boundAttr) {
    var trigger = block.querySelector(buttonSelector);
    var panel = block.querySelector(panelSelector);
    if (!trigger || !panel) return null;
    var close = panel.querySelector(closeSelector);
    if (previewApi && typeof previewApi.bindAnchoredPopover === "function") {
      return previewApi.bindAnchoredPopover({
        root: block,
        trigger: trigger,
        panel: panel,
        close: close,
        boundAttr: boundAttr,
        offset: 8,
        position: positionLeanPDEPopover
      });
    }
    function setOpen(open) {
      if (open) positionLeanPDEPopover(null, block, trigger, panel);
      panel.hidden = !open;
      trigger.setAttribute("aria-expanded", open ? "true" : "false");
    }
    trigger.addEventListener("click", function () {
      setOpen(panel.hidden);
    });
    if (close) {
      close.addEventListener("click", function () {
        setOpen(false);
      });
    }
    setOpen(false);
    return { close: function () { setOpen(false); } };
  }

  function trimLeanPDEGraphOptions(block) {
    // The layout is pre-rendered, so the direction and packing options of the
    // in-browser renderer do not apply. The preview behaviour options remain.
    var direction = block.querySelector(".bp_graph_direction_select");
    if (direction) {
      var directionLabel = block.querySelector('label[for="' + direction.id + '"]');
      if (directionLabel) directionLabel.remove();
      direction.remove();
    }
    var pack = block.querySelector(".bp_graph_pack_input");
    if (pack) {
      var toggle = pack.closest(".bp_graph_option_toggle");
      if (toggle) toggle.remove(); else pack.remove();
    }
  }

  function syncLeanPDELegend(block, activeKey) {
    var fullLegend = block.querySelector('.bp_graph_legend[data-bp-legend-kind="full"]');
    var groupLegend = block.querySelector('.bp_graph_legend[data-bp-legend-kind="group"]');
    var showGroupLegend = activeKey === "group";
    if (fullLegend) fullLegend.hidden = showGroupLegend;
    if (groupLegend) groupLegend.hidden = !showGroupLegend;
  }

  function viewKeyFromLocation() {
    var match = /(?:^|[#&])view=([^&]+)/.exec(window.location.hash || "");
    if (!match) return "";
    try {
      return decodeURIComponent(match[1]);
    } catch (error) {
      return "";
    }
  }

  async function loadLeanPDEPreviewApi() {
    try {
      var previewModule = await import(siteUrl("-verso-data/api/preview.mjs"));
      if (previewModule && typeof previewModule.createPreview === "function") {
        return previewModule.createPreview();
      }
    } catch (error) {
      console.error(error);
    }
    return null;
  }

  async function installLeanPDEDependencyAtlas() {
    claimObserver.disconnect();
    claimLeanPDEAtlasBlocks(document);
    var block = document.querySelector(".leanpde-dependency-atlas");
    if (!block) return;
    var generatedCanvas = block.querySelector(".bp_graph_canvas");
    if (!generatedCanvas) return;

    var graphData = readLeanPDEGraphData(block);
    var variantsByKey = new Map();
    var nodeByPreviewKey = new Map();
    if (graphData && Array.isArray(graphData.variants)) {
      graphData.variants.forEach(function (variant) {
        if (variant && typeof variant.key === "string") variantsByKey.set(variant.key, variant);
      });
    }
    if (graphData && Array.isArray(graphData.nodes)) {
      graphData.nodes.forEach(function (node) {
        if (node && typeof node.previewKey === "string") nodeByPreviewKey.set(node.previewKey, node);
      });
    }

    var groupHover = block.querySelector(".bp_group_hover_preview");
    if (groupHover) groupHover.remove();
    trimLeanPDEGraphOptions(block);

    var controls = block.querySelector(".bp_graph_controls");
    var primary = controls ? controls.querySelector(".bp_graph_controls_primary") : null;
    var actions = controls ? controls.querySelector(".bp_graph_controls_actions") : null;

    var stats = document.createElement("span");
    stats.className = "leanpde-dependency-atlas-stats";
    stats.textContent = "Loading atlas...";
    stats.setAttribute("role", "status");
    stats.setAttribute("aria-live", "polite");
    if (primary) primary.appendChild(stats);

    var fitButton = makeLeanPDEAtlasButton("Fit", "Fit the entire graph");
    var resetButton = makeLeanPDEAtlasButton("Reset", "Return to readable scale");
    var zoomOutButton = makeLeanPDEAtlasButton("-", "Zoom out");
    var zoomInButton = makeLeanPDEAtlasButton("+", "Zoom in");
    var buttons = [fitButton, resetButton, zoomOutButton, zoomInButton];
    if (actions) {
      var optionsButton = actions.querySelector(".bp_graph_options_button");
      buttons.forEach(function (button) {
        actions.insertBefore(button, optionsButton);
      });
    }

    var canvas = document.createElement("div");
    canvas.className = "leanpde-dependency-atlas-canvas";
    canvas.setAttribute("data-leanpde-loading", "true");
    canvas.setAttribute("aria-busy", "true");
    generatedCanvas.replaceWith(canvas);

    var select = block.querySelector(".bp_graph_view_select");
    var previewPanel = block.querySelector(".bp_graph_preview");
    var previewModeSelect = block.querySelector(".bp_graph_preview_mode_select");
    var previewPlacementSelect = block.querySelector(".bp_graph_preview_placement_select");

    var viewer = {
      svg: null,
      bounds: null,
      view: null,
      drag: null,
      suppressClick: false,
      activeKey: "",
      previewActiveNode: null,
      previewRequestToken: 0
    };

    function aspect() {
      return Math.max(0.2, canvas.clientWidth / Math.max(1, canvas.clientHeight));
    }

    function remInPixels() {
      var size = parseFloat(getComputedStyle(document.documentElement).fontSize);
      return Number.isFinite(size) && size > 0 ? size : 16;
    }

    // Give the canvas the shape of the graph, within limits, so that the fitted
    // view fills it instead of floating as a thin band in a tall empty box.
    function sizeCanvasFor(bounds) {
      var rem = remInPixels();
      var width = Math.max(1, canvas.clientWidth);
      var tallest = Math.max(40 * rem, window.innerHeight - 12 * rem);
      var fitted = width * bounds.height / Math.max(1, bounds.width) * 1.05;
      var height = Math.round(Math.min(tallest, Math.max(24 * rem, fitted)));
      canvas.style.setProperty("height", height + "px", "important");
      canvas.style.setProperty("min-height", height + "px", "important");
    }

    function applyView(next) {
      if (!viewer.svg) return;
      viewer.view = next;
      viewer.svg.setAttribute(
        "viewBox",
        [next.x, next.y, next.width, next.height].join(" ")
      );
    }

    function fitView() {
      if (!viewer.bounds) return;
      applyView(fitLeanPDEAtlasView(viewer.bounds, aspect()));
    }

    function resetView() {
      if (!viewer.bounds) return;
      applyView(readableLeanPDEAtlasView(viewer.bounds, canvas, aspect()));
    }

    function zoom(factor, clientX, clientY) {
      if (!viewer.view || !viewer.bounds) return;
      var view = viewer.view;
      var rect = canvas.getBoundingClientRect();
      var px = Number.isFinite(clientX) ? clientX - rect.left : rect.width / 2;
      var py = Number.isFinite(clientY) ? clientY - rect.top : rect.height / 2;
      var ratioX = Math.max(0, Math.min(1, px / Math.max(1, rect.width)));
      var ratioY = Math.max(0, Math.min(1, py / Math.max(1, rect.height)));
      var focusX = view.x + ratioX * view.width;
      var focusY = view.y + ratioY * view.height;
      var fitted = fitLeanPDEAtlasView(viewer.bounds, aspect());
      var minWidth = Math.min(180, viewer.bounds.width);
      var nextWidth = Math.max(
        minWidth,
        Math.min(fitted.width, view.width * factor)
      );
      var nextHeight = nextWidth / aspect();
      applyView({
        x: focusX - ratioX * nextWidth,
        y: focusY - ratioY * nextHeight,
        width: nextWidth,
        height: nextHeight
      });
    }

    fitButton.addEventListener("click", fitView);
    resetButton.addEventListener("click", resetView);
    zoomOutButton.addEventListener("click", function () {
      zoom(1.7);
    });
    zoomInButton.addEventListener("click", function () {
      zoom(1 / 1.7);
    });

    canvas.addEventListener("wheel", function (event) {
      if (!viewer.view) return;
      event.preventDefault();
      var delta = Math.max(-120, Math.min(120, event.deltaY));
      zoom(Math.exp(delta * 0.0045), event.clientX, event.clientY);
    }, { passive: false });

    canvas.addEventListener("pointerdown", function (event) {
      if (event.button !== 0 || viewer.drag || !viewer.view) return;
      viewer.suppressClick = false;
      viewer.drag = {
        pointerId: event.pointerId,
        clientX: event.clientX,
        clientY: event.clientY,
        x: viewer.view.x,
        y: viewer.view.y,
        moved: false
      };
    });

    window.addEventListener("pointermove", function (event) {
      var drag = viewer.drag;
      if (!drag || drag.pointerId !== event.pointerId) return;
      var dx = event.clientX - drag.clientX;
      var dy = event.clientY - drag.clientY;
      if (!drag.moved && Math.abs(dx) + Math.abs(dy) > 4) {
        drag.moved = true;
        // Capture only actual drags; ordinary clicks must keep the node as their target.
        canvas.setPointerCapture(event.pointerId);
        canvas.classList.add("is-dragging");
      }
      if (!drag.moved) return;
      event.preventDefault();
      applyView({
        x: drag.x - dx * viewer.view.width / Math.max(1, canvas.clientWidth),
        y: drag.y - dy * viewer.view.height / Math.max(1, canvas.clientHeight),
        width: viewer.view.width,
        height: viewer.view.height
      });
    });

    function finishDrag(event) {
      var drag = viewer.drag;
      if (!drag || drag.pointerId !== event.pointerId) return;
      viewer.suppressClick = drag.moved && event.type === "pointerup";
      viewer.drag = null;
      canvas.classList.remove("is-dragging");
      if (canvas.hasPointerCapture(event.pointerId)) {
        canvas.releasePointerCapture(event.pointerId);
      }
    }

    window.addEventListener("pointerup", finishDrag);
    window.addEventListener("pointercancel", finishDrag);
    canvas.addEventListener("click", function (event) {
      if (!viewer.suppressClick) return;
      event.preventDefault();
      event.stopPropagation();
      viewer.suppressClick = false;
    }, true);

    function updateCanvasOffset() {
      block.style.setProperty("--bp-graph-canvas-top", Math.max(0, Math.round(canvas.offsetTop)) + "px");
    }

    var resizeObserver = new ResizeObserver(function () {
      updateCanvasOffset();
      if (!viewer.view) return;
      var view = viewer.view;
      var centerX = view.x + view.width / 2;
      var centerY = view.y + view.height / 2;
      var height = view.width / aspect();
      applyView({
        x: centerX - view.width / 2,
        y: centerY - height / 2,
        width: view.width,
        height: height
      });
    });
    resizeObserver.observe(canvas);

    // Statement previews through the generated Blueprint preview API. The module
    // import and the atlas index request overlap with the first SVG download.
    var indexPromise = fetch(siteUrl("-verso-data/leanpde-dependency-atlas.json"));
    var previewApi = await loadLeanPDEPreviewApi();
    var surface = null;
    if (previewApi && previewPanel && typeof previewApi.createPreviewSurface === "function") {
      surface = previewApi.createPreviewSurface({
        panel: previewPanel,
        titleSelector: ".bp_graph_preview_title",
        bodySelector: ".bp_graph_preview_body",
        closeSelector: ".bp_graph_preview_close",
        defaults: {
          mode: previewPanel.getAttribute("data-bp-preview-mode") || "pinned",
          placement: previewPanel.getAttribute("data-bp-preview-placement") || "docked"
        },
        onHide: function () {
          viewer.previewRequestToken += 1;
          viewer.previewActiveNode = null;
        }
      });
    }

    function readPreviewBehavior() {
      var mode = previewModeSelect ? previewModeSelect.value : "pinned";
      var placement = previewPlacementSelect ? previewPlacementSelect.value : "docked";
      return { mode: mode, placement: placement };
    }

    function applyPreviewBehavior() {
      if (!surface) return;
      surface.setBehavior(readPreviewBehavior());
      surface.hide();
    }

    if (previewModeSelect) {
      var defaultMode = previewModeSelect.getAttribute("data-bp-graph-default-preview-mode");
      if (defaultMode) previewModeSelect.value = defaultMode;
      previewModeSelect.addEventListener("change", applyPreviewBehavior);
    }
    if (previewPlacementSelect) {
      var defaultPlacement = previewPlacementSelect.getAttribute("data-bp-graph-default-preview-placement");
      if (defaultPlacement) previewPlacementSelect.value = defaultPlacement;
      previewPlacementSelect.addEventListener("change", applyPreviewBehavior);
    }
    if (surface) surface.setBehavior(readPreviewBehavior());

    var legendPopover = bindLeanPDEPopover(
      previewApi, block,
      ".bp_graph_legend_button", ".bp_graph_legend_popover", ".bp_graph_legend_popover_close",
      "data-bp-legend-bound"
    );
    var optionsPopover = bindLeanPDEPopover(
      previewApi, block,
      ".bp_graph_options_button", ".bp_graph_options_popover", ".bp_graph_options_popover_close",
      "data-bp-options-bound"
    );

    block.addEventListener("keydown", function (event) {
      if (event.key !== "Escape") return;
      if (surface && surface.isOpen()) surface.hide();
      if (legendPopover && typeof legendPopover.close === "function") legendPopover.close();
      if (optionsPopover && typeof optionsPopover.close === "function") optionsPopover.close();
    });

    function bindPreviews(svg, variant) {
      if (!surface || !variant || !Array.isArray(variant.previewKeyByNodeId)) return;
      var previewKeys = new Map(variant.previewKeyByNodeId);
      if (previewKeys.size === 0) return;
      svg.querySelectorAll("g.node").forEach(function (node) {
        if (!previewKeys.has(node.id)) return;
        node.setAttribute("tabindex", "0");
        var title = node.querySelector("title");
        if (title) title.remove();
        node.querySelectorAll("a").forEach(function (link) {
          link.removeAttribute("title");
          link.removeAttribute("xlink:title");
          link.removeAttributeNS(XLINK_NS, "title");
        });
      });

      function canPreview(node) {
        return node instanceof Element && previewKeys.has(node.id);
      }

      async function showNode(node) {
        var previewKey = previewKeys.get(node.id);
        if (!previewKey) return;
        var token = ++viewer.previewRequestToken;
        var resolved = await previewApi.resolvePreviewHtml(previewKey);
        if (token !== viewer.previewRequestToken) return;
        if (!resolved || !resolved.html) return;
        if (resolved.reason === "semantic-preview-body-missing") return;
        var data = nodeByPreviewKey.get(previewKey);
        var label = labelOfPreviewKey(previewKey);
        var title = data && typeof data.title === "string" ? data.title.trim() : "";
        viewer.previewActiveNode = node;
        surface.showContent({
          heading: title ? title + " · " + label : label,
          headingHref: readNodeHref(node) || (data && data.href ? siteUrl(data.href) : ""),
          headingTitle: "Open the statement card",
          html: resolved.html,
          anchor: node
        });
      }

      surface.bindTriggers({
        eventRoot: svg,
        eventRootBoundAttr: "data-bp-preview-bound",
        triggerSelector: "g.node",
        filterTrigger: canPreview,
        show: function (node) {
          if (!canPreview(node)) return false;
          if (viewer.previewActiveNode === node && surface.isOpen()) {
            surface.position(node);
            return true;
          }
          showNode(node);
          return true;
        },
        hide: function () { surface.hide(); },
        getActiveTrigger: function () { return viewer.previewActiveNode; },
        activateOnClick: true,
        activateOnKeydown: true,
        enterRequiresHover: true,
        bindEscape: false,
        bindWindow: false
      });
    }

    var index = null;
    var indexByKey = new Map();
    var svgCache = new Map();
    // The group overview is the landing view; the full graph is `#view=full`.
    var defaultKey = "full";

    function bindViewSwitches(svg, variant) {
      var switches = new Map();
      if (variant && Array.isArray(variant.selectOnNodeId)) {
        variant.selectOnNodeId.forEach(function (entry) {
          if (Array.isArray(entry) && indexByKey.has(entry[1])) switches.set(entry[0], entry[1]);
        });
      }
      function activate(target) {
        return function (event) {
          if (viewer.suppressClick) return;
          event.preventDefault();
          event.stopPropagation();
          showVariant(target);
        };
      }
      svg.querySelectorAll("g.node").forEach(function (node) {
        var target = switches.get(node.id);
        if (!target) return;
        node.setAttribute("tabindex", "0");
        node.setAttribute("data-leanpde-view", target);
        node.addEventListener("click", activate(target));
        node.addEventListener("keydown", function (event) {
          if (event.key === "Enter" || event.key === " ") activate(target)(event);
        });
      });
      // In the full graph every cluster carries its group title; clicking it opens
      // the focused view of that group.
      var keyByLabel = new Map();
      var ambiguous = new Set();
      indexByKey.forEach(function (entry, key) {
        if (!key.startsWith("parent:")) return;
        var label = String(entry.label || "").replace(/\s+/g, " ").trim();
        if (keyByLabel.has(label)) ambiguous.add(label);
        keyByLabel.set(label, key);
      });
      svg.querySelectorAll("g.cluster").forEach(function (cluster) {
        var label = textOf(cluster);
        var target = keyByLabel.get(label);
        if (!target || ambiguous.has(label)) return;
        cluster.setAttribute("data-leanpde-view", target);
        var title = cluster.querySelector("title");
        if (title) title.textContent = "Open the group view: " + label;
        cluster.addEventListener("click", function (event) {
          if (event.target instanceof Element && event.target.closest("g.node")) return;
          activate(target)(event);
        });
      });
    }

    async function loadVariantSvg(entry) {
      if (svgCache.has(entry.key)) return svgCache.get(entry.key);
      var response = await fetch(siteUrl("-verso-data/" + entry.file));
      if (!response.ok) {
        throw new Error("Dependency graph request failed with status " + response.status + ".");
      }
      var source = await response.text();
      var parsed = new DOMParser().parseFromString(source, "image/svg+xml");
      if (parsed.querySelector("parsererror")) {
        throw new Error("The pre-rendered dependency graph is not valid SVG.");
      }
      var svg = document.importNode(parsed.documentElement, true);
      svg.removeAttribute("width");
      svg.removeAttribute("height");
      svg.setAttribute("preserveAspectRatio", "xMidYMid meet");
      svg.setAttribute("role", "img");
      svg.setAttribute("aria-label", "LeanPDE statement dependency graph: " + entry.label);
      svg.querySelectorAll("a").forEach(function (link) {
        var href = link.getAttribute("href") || link.getAttributeNS(XLINK_NS, "href");
        if (!href) return;
        link.setAttribute("href", siteUrl(href));
      });
      var variant = variantsByKey.get(entry.key);
      bindPreviews(svg, variant);
      bindViewSwitches(svg, variant);
      svgCache.set(entry.key, svg);
      return svg;
    }

    function describeVariant(entry, svg) {
      var nodeCount = svg.getAttribute("data-node-count");
      var edgeCount = svg.getAttribute("data-edge-count");
      var clusterCount = svg.getAttribute("data-cluster-count");
      if (!nodeCount || !edgeCount) return "Dependency graph loaded";
      if (entry.key === "group") return nodeCount + " groups / " + edgeCount + " edges";
      var text = nodeCount + " nodes / " + edgeCount + " edges";
      if (entry.key === "full" && clusterCount && clusterCount !== "0") {
        text += " / " + clusterCount + " groups";
      }
      return text;
    }

    async function showVariant(key) {
      var entry = indexByKey.get(key) || indexByKey.get("full") || index.variants[0];
      if (!entry) return;
      viewer.activeKey = entry.key;
      if (select) select.value = entry.key;
      if (surface) surface.hide();
      syncLeanPDELegend(block, entry.key);
      canvas.setAttribute("data-leanpde-loading", "true");
      canvas.setAttribute("aria-busy", "true");
      canvas.removeAttribute("data-leanpde-error");
      try {
        var svg = await loadVariantSvg(entry);
        if (viewer.activeKey !== entry.key) return;
        viewer.svg = svg;
        viewer.bounds = parseLeanPDEAtlasViewBox(svg);
        canvas.replaceChildren(svg);
        canvas.removeAttribute("data-leanpde-loading");
        canvas.removeAttribute("aria-busy");
        stats.textContent = describeVariant(entry, svg);
        buttons.forEach(function (button) {
          button.disabled = false;
        });
        sizeCanvasFor(viewer.bounds);
        updateCanvasOffset();
        fitView();
        var currentHash = window.location.hash || "";
        var nextHash = entry.key === defaultKey ? "" : "#view=" + encodeURIComponent(entry.key);
        if (currentHash !== nextHash && (nextHash || /view=/.test(currentHash))) {
          history.replaceState(null, "", window.location.pathname + window.location.search + nextHash);
        }
      } catch (error) {
        console.error(error);
        canvas.removeAttribute("data-leanpde-loading");
        canvas.removeAttribute("aria-busy");
        canvas.setAttribute("data-leanpde-error", "true");
        stats.textContent = "Dependency graph unavailable";
      }
    }

    try {
      var response = await indexPromise;
      if (!response.ok) {
        throw new Error("Dependency atlas index request failed with status " + response.status + ".");
      }
      index = await response.json();
      if (!index || !Array.isArray(index.variants) || index.variants.length === 0) {
        throw new Error("The dependency atlas index lists no views.");
      }
      index.variants.forEach(function (entry) {
        indexByKey.set(entry.key, entry);
      });
      if (indexByKey.has("group")) defaultKey = "group";
      if (select) {
        var known = new Set(index.variants.map(function (entry) { return entry.key; }));
        Array.prototype.slice.call(select.options).forEach(function (option) {
          if (!known.has(option.value)) option.remove();
        });
        index.variants.forEach(function (entry) {
          if (select.querySelector('option[value="' + entry.key.replace(/"/g, '\\"') + '"]')) return;
          var option = document.createElement("option");
          option.value = entry.key;
          option.textContent = entry.label;
          select.appendChild(option);
        });
        select.addEventListener("change", function () {
          showVariant(select.value);
        });
      }
      window.addEventListener("hashchange", function () {
        var key = viewKeyFromLocation() || defaultKey;
        if (key !== viewer.activeKey && indexByKey.has(key)) showVariant(key);
      });
      var initial = viewKeyFromLocation();
      await showVariant(indexByKey.has(initial) ? initial : defaultKey);
    } catch (error) {
      console.error(error);
      canvas.removeAttribute("data-leanpde-loading");
      canvas.setAttribute("data-leanpde-error", "true");
      canvas.removeAttribute("aria-busy");
      stats.textContent = "Dependency graph unavailable";
    }
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", installLeanPDEDependencyAtlas, { once: true });
  } else {
    installLeanPDEDependencyAtlas();
  }
})();
"##

/-- Choose the colour theme before the first paint, so a reader who asked for the
dark one never sees a white page first.

The choice is `light`, `dark` or `system`, kept in `localStorage` under
`leanpde-theme`; `system` and an unset value follow `prefers-color-scheme`. A
`?theme=light` or `?theme=dark` query decides the theme for one page load without
being stored, which is how a link can carry a theme and how a screenshot asks for
one. Any other value of the parameter is ignored. -/
private def themePrepaintScript : String := r##"
(function () {
  // Verso's default viewport caps zoom; allow readers to enlarge text and mathematics.
  var viewport = document.querySelector('meta[name="viewport"]');
  if (viewport) viewport.setAttribute("content", "width=device-width, initial-scale=1");
  var choice = null;
  var forced = /[?&]theme=(light|dark)(?:&|$)/.exec(window.location.search);
  if (forced) {
    choice = forced[1];
  } else {
    try {
      var stored = window.localStorage.getItem("leanpde-theme");
      if (stored === "light" || stored === "dark") choice = stored;
    } catch (error) {
      /* Storage denied: the media query decides. */
    }
    if (!choice) {
      choice = window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches
        ? "dark"
        : "light";
    }
  }
  document.documentElement.dataset.theme = choice;
  var meta = document.getElementById("leanpde-theme-color");
  if (meta) meta.setAttribute("content", choice === "dark" ? "#191d1c" : "#fffdf8");
})();
"##

-- The favicon comes from the supplied logo; the site optimizer copies it into
-- the data directory. The theme script sets the browser's matching page colour.
open Verso.Output.Html in
private def blueprintExtraHead : Array Verso.Output.Html :=
  #[{{ <link rel="icon" type="image/png" sizes="64x64" href="-verso-data/leanpde-brand/favicon.png"/> }},
    {{ <meta id="leanpde-theme-color" name="theme-color" content="#fffdf8"/> }},
    {{ <script>{{.text false themePrepaintScript}}</script> }}]

/-- Render the assembled Blueprint and its preview metadata. -/
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    leanPDEBlueprint.toPart
    args
    (extensionImpls := by exact extension_impls%)
    (config := {
      toHtmlConfig := {
        extraHead := blueprintExtraHead
        extraCss := [blueprintSiteCss]
        extraJs := [siteShellSetup, dependencyGraphPageSetup]
      }
    })
