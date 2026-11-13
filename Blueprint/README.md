# LeanPDE Blueprint

The Blueprint contains the mathematical exposition, theorem statements, proof
ideas, and references for LeanPDE. The chapters follow selected material from
Evans's *Partial Differential Equations*, second edition, with additional fluid
mechanics and verified computation.

## Build and preview

Install the pinned Lean toolchain, Node.js 22 or newer, Graphviz, Python 3
with the `regex` package, and GNU `realpath`. From the repository root:

```bash
lake exe cache get
bash Blueprint/Tools/build.sh
python3 -m http.server 8000 --bind 127.0.0.1 --directory _out/site/html-multi
```

Open `http://127.0.0.1:8000/`. The build script compiles `PDE`, regenerates the
computation ledger and textbook map, builds the nested Blueprint package, and
renders the static site. The library and documentation package have separate
Lake caches. The script prepares VersoBlueprint's shared library; Lake resolves
the pinned documentation dependencies.

The finite certificates are checked in the kernel. For the faster native evaluation:

```bash
LEANPDE_CERTIFICATES=fast bash Blueprint/Tools/build.sh
```

This writes `_out/site-fast/html-multi` and uses the separate fast cache.
SymLean's README explains the two profiles under
[Kernel checking and the fast profile](https://github.com/Robertboy18/SymLean#kernel-checking-and-the-fast-profile).

An optional first argument selects another output directory under `_out/`.
To make source references link to a public checkout, set
`LEANPDE_PUBLIC_REPOSITORY_URL` before building. The build records the current
commit unless `LEANPDE_SOURCE_REVISION` is supplied explicitly.

On a machine without Node.js:

```bash
bash Blueprint/Tools/build-no-node.sh
```

This writes `_out/site-no-node/html-multi` with the same libraries, renderer and
dependency atlas, and leaves out the three Node.js steps. It compiles the
committed textbook map without regenerating it, and it does not run the two
post-processors described [below](#generated-data-and-assets). The pages
therefore keep Verso's own shell: the logo, the theme button, the section rail,
the "Proof map" actions, the Introduction notebook, the learning features and
the typeset figure labels are absent, and the proof panels stay inside the
pages. The script does not download the Mathlib cache. Set `LEANPDE_LAKE` to run
every Lake call, and the renderer, through a launcher of your own.

## Publishing on GitHub Pages

A rendered site cannot be pushed to a `gh-pages` branch as it is. Its manifest
is larger than the 100 MB that GitHub accepts for one file, and the renderer
records absolute source paths of the machine that built it. To make the tree
to push:

```bash
python3 Blueprint/Tools/build-pages-tree.py _out/site/html-multi _out/pages
```

The copy in `_out/pages` has `codeData: null` in every entry of the manifest
(the page runtime does not read that field; the rendered code is in the pages
and in the HTML cache), names every source by its path in the repository, and
has an empty `.nojekyll`. The script stops if a file over 100 MB, or an
absolute path of the checkout, of a dependency or of your home directory, is
left. Pass `_out/site-no-node/html-multi` for a site built without Node.js.

## Chapters

| Chapter | Source | Mathematical focus |
| --- | --- | --- |
| 1. Introduction | [Overview](Chapters/Overview.lean) | Heat-equation calculation, conventions, and scope |
| 2. Related Work | [RelatedWork](Chapters/RelatedWork.lean) | PDE formalizations and verified computation |
| 3. Foundations | [Foundations](Chapters/Foundations.lean) | Coordinates, operators, PDE problems, and distributions |
| 4. Sobolev Spaces | [Sobolev](Chapters/Sobolev.lean) | Weak calculus, approximation, traces, embeddings, and compactness |
| 5. Elliptic Equations | [Elliptic](Chapters/Elliptic.lean) | Classical solutions, variational theory, spectra, and regularity |
| 6. Parabolic Equations | [Parabolic](Chapters/Parabolic.lean) | Heat equations, weak evolution, regularity, and finite-time mechanisms |
| 7. Hyperbolic Equations | [Hyperbolic](Chapters/Hyperbolic.lean) | Transport, waves, Hamilton–Jacobi equations, and conservation laws |
| 8. Fluid Mechanics | [Fluid](Chapters/Fluid.lean) | Euler, Navier–Stokes, Stokes, axisymmetric flow, and Boussinesq |
| 9. Variational Methods | [Variational](Chapters/Variational.lean) | Minimization, variations, semilinear energies, and fixed points |
| 10. CAS and Certified Bounds | [Symbolic](Chapters/Symbolic.lean) | Exact calculations, analytic bridges, validated numerics, and certified plots |
| 11. Dependency Atlas | [DependencyAtlas](Chapters/DependencyAtlas.lean) | Dependencies across the curated statements |
| 12. Bibliography | [Bibliography command](Commands/Bibliography.lean) | Cited entries registered in [Bibliography.lean](Bibliography.lean) |


[`Blueprint.lean`](../Blueprint.lean) assembles the chapters and contains the
site stylesheet and interaction code. The nested [Lake configuration](lakefile.lean)
uses the repository root as its source directory. The mathematical library
itself does not depend on Verso.

## Writing a statement

Start with the mathematical question or a concrete example. State the domain,
hypotheses, and conclusion, then explain the construction or estimate used in
the proof. Avoid chapter tours, lists of implementation names, and narration
of tactic calls. Use descriptive links in prose:

```text
{bpref "symbolic.first_order_jet_semantics"}[first-order jet semantics]
```

Put exact Lean names in the card's `lean` metadata. Keep each principal result
in one canonical card; group several declarations only when they express one
mathematical theorem family. Auxiliary implementation lemmas stay in the source.
The owning chapter imports the modules defining its linked declarations.

Verso mathematical markup is:

```text
$`inline formula`
$$`display formula`
```

Every theorem card has one matching proof block:

```text
:::theorem "subject.result" (lean := "Namespace.theorem_name")
The mathematical statement, with its hypotheses and quantified conclusion.
:::

:::proof "subject.result"
The construction, estimate, or reduction used in the proof.
:::
```

Use dot-separated identifiers with snake_case segments. Put dependencies visible
in the statement in its `uses` field; put proof-only prerequisites in the proof
block's `uses` field. General analysis retains its mathematical owner prefix
when used in another subject's chapter.

Cite the source in structured metadata and record any specialization beside
the statement. Check edition and page numbers against the
[source records](Sources/README.md). Explain the actual formal argument in your
own words. An illustrative diagram should say what it draws; a certified bound
should identify the theorem that justifies it. Compare the displayed formulas
and proof idea with the linked Lean declarations before submitting.

## Generated data and assets

Edit generator inputs, then regenerate the committed output:

| Output | Generator or input |
| --- | --- |
| `Generated/CasLedgerData.lean` | `python3 Blueprint/Tools/build-cas-ledger.py` scans the `PDE/` call sites |
| `Generated/TextbookMapData.lean` | `node Blueprint/Tools/build-textbook-map.mjs` reads chapter citations |
| `Generated/FiguresData.lean` | `python3 Blueprint/Tools/build-figures.py` computes explanatory diagrams |
| `Generated/CertifiedPlots.lean` and its drawing data | `python3 Blueprint/Tools/build-certified-plots.py` generates enclosures and Lean proofs |
| `Assets/Brand/` | `python3 Blueprint/Tools/build-logo.py` derives the wordmark variants from `logo.png` |

The ledger and textbook-map generators run on every site build. Their `--check`
options detect stale output. Certified plots require a built PDE library; their
Lean containment theorems compile with the Blueprint. Brand regeneration needs
Pillow and NumPy; ordinary site builds use the committed images. The figures
need Python 3.12 or newer, whose `sum` adds floats with compensation; earlier
versions compute slightly different paths.

The textbook map indexes citations, not complete coverage of the textbook.
Section-only citations remain unplaced until their page locations are verified.
The dependency atlas records the dependencies attached to statement and proof
cards. `Tools/build-dependency-atlas.py` renders its views with Graphviz.

`Tools/optimize-site.mjs` prepares navigation, search, source links, and assets.
`Tools/defer-heavy-blocks.mjs` moves large proof and hover payloads into files
loaded when opened. The Introduction notebook uses source excerpts through
`Tools/opening-notebook.mjs`; it does not run Lean in the browser.

The commands `{leanpde_mode_explorer}` and `{leanpde_reading_routes}` place the
interactive examples and reading routes. Edit their explanations in
`Tools/learning.mjs`, their controls in `Tools/learning.js`, and their appearance
in `Tools/learning.css`. The heat and wave plots sample the displayed explicit
solutions. Formulas remain readable with JavaScript disabled or when printed.

For an optional GIF export of an existing animated figure:

```bash
node Blueprint/Tools/export-figure-gif.mjs PAGE_URL FIGURE_ID _out/figure-exports
```

The exporter needs Chrome, Node with WebSocket support, and Python with Pillow.
It captures the existing SVG timeline rather than computing another solution.
