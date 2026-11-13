/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Generated.FiguresData
import Lean
import Verso
import VersoManual
import VersoBlueprint.Lib.ExtensionDecode

/-!
# Figures

`{leanpde_figure "heat-kernel"}` renders one figure of the drawing model in
`Blueprint.Generated.FiguresData` as inline SVG with its caption. An unknown id
is a build error listing the ids that exist.

`Blueprint/Tools/build-figures.py` computes every figure from the mathematics it
illustrates: the Gaussian at several times, a numerical convolution against the
standard bump, marching squares on a harmonic function, Burgers characteristics,
interval arithmetic on subdivisions. Its `--check` mode recomputes the model and
fails if the committed module differs, so a figure cannot drift away from the
code that drew it.

The renderer does no arithmetic. It copies SVG attributes out of the model and
turns two of them into classes: a mark carries a colour *role*, not a colour,
and the roles map onto the site's seven `--leanpde-fig-*` custom properties. One
variable change re-colours every figure in both the light and the dark theme,
and no figure contains a literal colour, so nothing has to be redrawn for dark
mode. Animated figures carry SMIL `animate` children whose frames were computed
alongside the geometry; frame zero is the most informative one, which is what a
reader who asked for reduced motion sees.

Mathematical labels carry their TeX source to the HTML build. The site's
postprocessor typesets them and the caption equations with the same KaTeX
assets as the chapter text, so the finished figures need no client-side
typesetting.
-/

namespace LeanPDE.Figures

open Lean Elab Command
open Verso Doc Elab Syntax
open Verso.Genre Manual

/-- One SMIL animation attached to a mark. -/
structure Anim where
  /-- The SVG tag: `animate` or `animateTransform`. -/
  tag : String
  /-- Attributes of the animation element, copied from the model. -/
  attrs : Array (String × String)
deriving Inhabited

/-- One drawing primitive: an SVG tag, its attributes, its colour roles. -/
structure Mark where
  /-- The SVG tag: `path`, `line`, `rect`, `circle` or `text`. -/
  tag : String
  /-- The body of a `text` mark. -/
  text : String
  /-- TeX for a mathematical label, typeset when the HTML site is assembled. -/
  tex : String
  /-- The colour role of the stroke, or the empty string for no stroke. -/
  stroke : String
  /-- The colour role of the fill, or the empty string for no fill. -/
  fill : String
  /-- The id of a clip path this mark is drawn inside, if any. -/
  clip : String
  /-- `"1"` on a label that paints the surface colour behind its glyphs. -/
  halo : String
  /-- Geometry and typography, already named as SVG attributes. -/
  attrs : Array (String × String)
  /-- Animations of this mark's attributes. -/
  anims : Array Anim
deriving Inhabited

/-- A rectangular clip region, for a mark that moves inside a panel. -/
structure Clip where
  id : String
  x : String
  y : String
  w : String
  h : String
deriving Inhabited

/-- One figure: a viewBox, a caption, a description, and marks. -/
structure Figure where
  id : String
  /-- Short title, repeated in the caption and in the PDF fallback. -/
  title : String
  /-- The caption, which lives with the figure so it reads the same everywhere. -/
  caption : String
  /-- What a screen reader is told the figure shows. -/
  alt : String
  width : String
  height : String
  /-- `"1"` when the figure has animated marks, the empty string otherwise. -/
  animated : String
  clips : Array Clip
  marks : Array Mark
deriving Inhabited

/-- Attributes a mark may carry. Anything else in the model is ignored. -/
private def markAttrs : Array String :=
  #["d", "x", "y", "width", "height", "rx", "ry", "cx", "cy", "r",
    "x1", "y1", "x2", "y2", "dx", "dy", "transform",
    "stroke-width", "stroke-dasharray", "stroke-linecap", "stroke-opacity",
    "fill-opacity", "opacity", "font-size", "font-weight", "font-style",
    "text-anchor", "letter-spacing"]

/-- Attributes an animation may carry. -/
private def animAttrs : Array String :=
  #["attributeName", "type", "values", "keyTimes", "keySplines", "calcMode", "dur"]

/-- The colour roles, in the order the stylesheet lists them. -/
private def roles : Array String :=
  #["ink", "muted", "accent", "accent2", "band", "warn", "surface"]

private def str (value : Json) (key : String) : String :=
  (value.getObjVal? key >>= Json.getStr?).toOption.getD ""

private def jsonArray (value : Json) (key : String) : Array Json :=
  (value.getObjVal? key >>= Json.getArr?).toOption.getD #[]

/-- The attributes of `value` named in `names`, in that order. -/
private def pick (value : Json) (names : Array String) : Array (String × String) :=
  names.filterMap fun name ↦
    match value.getObjVal? name >>= Json.getStr? with
    | .ok found => some (name, found)
    | .error _ => none

private def decodeAnim (value : Json) : Anim :=
  { tag := str value "k", attrs := pick value animAttrs }

private def decodeMark (value : Json) : Mark :=
  { tag := str value "k"
    text := str value "t"
    tex := str value "tex"
    stroke := str value "stroke"
    fill := str value "fill"
    clip := str value "clip"
    halo := str value "halo"
    attrs := pick value markAttrs
    anims := (jsonArray value "anim").map decodeAnim }

private def decodeClip (value : Json) : Clip :=
  { id := str value "id", x := str value "x", y := str value "y",
    w := str value "w", h := str value "h" }

private def decodeFigure (value : Json) : Figure :=
  { id := str value "id"
    title := str value "title"
    caption := str value "caption"
    alt := str value "alt"
    width := str value "width"
    height := str value "height"
    animated := str value "animated"
    clips := (jsonArray value "clips").map decodeClip
    marks := (jsonArray value "marks").map decodeMark }

/-- The figure of the model with this id, and the ids of all of them.

The figure travels to the call site as the model's own JSON, so the block
payload and the model are read by the same decoder. -/
def findFigure (encoded : String) (id : String) :
    Except String (Option Json × Array String) := do
  let value ← Json.parse encoded
  let figures ← value.getObjVal? "figures" >>= Json.getArr?
  return (figures.find? (str · "id" == id), figures.map (str · "id"))

/-- Decode one figure previously serialized at the call site. -/
private def decodeOne (encoded : String) : Figure :=
  match Json.parse encoded with
  | .error error => panic! s!"LeanPDE figure JSON is malformed: {error}"
  | .ok value => decodeFigure value

/-- Shared figure layout, with fallback colours for rendering outside the book's stylesheet. -/
def figureCss : String := r##"
/* Keep these light and dark values synchronized with Blueprint.lean;
   these standalone fallbacks have zero specificity, so the site's own definitions always win. */
:where(html) {
  --leanpde-fig-surface: #fffdf8;
  --leanpde-fig-ink: #292923;
  --leanpde-fig-muted: #706b61;
  --leanpde-fig-accent: #176b68;
  --leanpde-fig-accent-2: #a4442d;
  --leanpde-fig-band: rgba(23, 107, 104, 0.14);
  --leanpde-fig-warn: #a3302a;
}

:where(html[data-theme="dark"]) {
  --leanpde-fig-surface: #191d1c;
  --leanpde-fig-ink: #e8e6dc;
  --leanpde-fig-muted: #aaa99c;
  --leanpde-fig-accent: #7cc5bd;
  --leanpde-fig-accent-2: #eea07c;
  --leanpde-fig-band: rgba(124, 197, 189, 0.2);
  --leanpde-fig-warn: #e2796b;
}

.leanpde-fig {
  margin: 1.5rem 0 1.9rem;
  max-width: 46rem;
}

.leanpde-fig-svg {
  display: block;
  width: 100%;
  height: auto;
  font-family: inherit;
  background: var(--leanpde-fig-surface);
}

.leanpde-fig-caption {
  margin: 0.55rem 0 0;
  font-size: 0.87rem;
  line-height: 1.5;
  color: var(--leanpde-fig-muted);
}

.leanpde-fig-caption strong {
  color: var(--leanpde-fig-ink);
  font-weight: 600;
}

.leanpde-fig-svg .lfs-ink { stroke: var(--leanpde-fig-ink); }
.leanpde-fig-svg .lfs-muted { stroke: var(--leanpde-fig-muted); }
.leanpde-fig-svg .lfs-accent { stroke: var(--leanpde-fig-accent); }
.leanpde-fig-svg .lfs-accent2 { stroke: var(--leanpde-fig-accent-2); }
.leanpde-fig-svg .lfs-band { stroke: var(--leanpde-fig-band); }
.leanpde-fig-svg .lfs-warn { stroke: var(--leanpde-fig-warn); }
.leanpde-fig-svg .lfs-surface { stroke: var(--leanpde-fig-surface); }

.leanpde-fig-svg .lff-ink { fill: var(--leanpde-fig-ink); }
.leanpde-fig-svg .lff-muted { fill: var(--leanpde-fig-muted); }
.leanpde-fig-svg .lff-accent { fill: var(--leanpde-fig-accent); }
.leanpde-fig-svg .lff-accent2 { fill: var(--leanpde-fig-accent-2); }
.leanpde-fig-svg .lff-band { fill: var(--leanpde-fig-band); }
.leanpde-fig-svg .lff-warn { fill: var(--leanpde-fig-warn); }
.leanpde-fig-svg .lff-surface { fill: var(--leanpde-fig-surface); }

/* HTML mathematics inside SVG uses the same roles as the drawn curves. */
.leanpde-fig-svg .lf-math-label.lff-ink { color: var(--leanpde-fig-ink); }
.leanpde-fig-svg .lf-math-label.lff-muted { color: var(--leanpde-fig-muted); }
.leanpde-fig-svg .lf-math-label.lff-accent { color: var(--leanpde-fig-accent); }
.leanpde-fig-svg .lf-math-label.lff-accent2 { color: var(--leanpde-fig-accent-2); }
.leanpde-fig-svg .lf-math-label.lff-band { color: var(--leanpde-fig-band); }
.leanpde-fig-svg .lf-math-label.lff-warn { color: var(--leanpde-fig-warn); }
.leanpde-fig-svg .lf-math-label.lff-surface { color: var(--leanpde-fig-surface); }

.leanpde-fig-svg .lf-math-label { overflow: visible; }
.leanpde-fig-svg .lf-math {
  width: max-content;
  max-width: none;
  white-space: nowrap;
  line-height: 1.2;
  transform: translate(var(--lf-math-anchor), -50%);
}
.leanpde-fig-svg .lf-math .katex {
  font-size: 1em;
  color: inherit;
}
.leanpde-fig-svg .lf-math-halo {
  text-shadow: 0 0 2px var(--leanpde-fig-surface),
               0 0 3px var(--leanpde-fig-surface);
}
.leanpde-fig-caption .katex { font-size: 1em; }

/* A label that crosses a curve keeps the surface colour behind its glyphs. */
.leanpde-fig-svg .lfh {
  paint-order: stroke;
  stroke: var(--leanpde-fig-surface);
  stroke-width: 2.5px;
  stroke-linejoin: round;
}

.leanpde-fig-pause {
  margin-left: 0.4rem;
  padding: 0 0.4rem;
  font: inherit;
  font-size: 0.8rem;
  color: var(--leanpde-fig-muted);
  background: transparent;
  border: 1px solid var(--leanpde-fig-muted);
  border-radius: 3px;
  cursor: pointer;
}

.leanpde-fig-pause:hover,
.leanpde-fig-pause:focus {
  color: var(--leanpde-fig-ink);
  border-color: var(--leanpde-fig-ink);
}

/* Keep mobile labels near their drawn size, with a little enlargement: a
   9-unit label in a 640-unit viewBox becomes 11.25px. The width follows the
   viewBox within bounds, and the figure contains the horizontal scrolling. */
@media screen and (max-width: 700px) {
  .leanpde-fig {
    overflow-x: auto;
  }

  /* Keep the caption and its animation control visible while the SVG pans. */
  .leanpde-fig-caption {
    position: sticky;
    left: 0;
  }

  .leanpde-fig-svg {
    width: clamp(34rem, calc(var(--leanpde-fig-viewbox-width) * 1.25), 60rem);
    max-width: none;
  }
}
"##

/-- Figure animation controls, including the reader's reduced-motion preference. -/
def figureJs : String := r##"
/* Animated figures. CSS cannot stop a SMIL animation, so a reader who asked for
   reduced motion gets the SVG paused at time zero, which is the frame the
   static attributes already hold. The button pauses and resumes one figure. */
(function () {
  var selector = '.leanpde-fig svg[data-leanpde-animated="1"]';
  var reduce = window.matchMedia ? window.matchMedia('(prefers-reduced-motion: reduce)') : null;

  function button(svg) {
    var figure = svg.closest('.leanpde-fig');
    return figure ? figure.querySelector('.leanpde-fig-pause') : null;
  }

  function label(svg, paused) {
    var control = button(svg);
    if (!control) { return; }
    control.textContent = paused ? 'Play' : 'Pause';
    control.setAttribute('aria-pressed', paused ? 'true' : 'false');
  }

  function stop(svg, rewind) {
    if (typeof svg.pauseAnimations !== 'function') { return; }
    svg.pauseAnimations();
    if (rewind && typeof svg.setCurrentTime === 'function') { svg.setCurrentTime(0); }
    label(svg, true);
  }

  function play(svg) {
    if (typeof svg.unpauseAnimations !== 'function') { return; }
    svg.unpauseAnimations();
    label(svg, false);
  }

  function each(action) {
    Array.prototype.forEach.call(document.querySelectorAll(selector), action);
  }

  function honourMotionPreference() {
    each(function (svg) {
      if (reduce && reduce.matches) { stop(svg, true); } else { play(svg); }
    });
  }

  function wire() {
    each(function (svg) {
      var control = button(svg);
      if (!control || control.getAttribute('data-leanpde-wired')) { return; }
      control.setAttribute('data-leanpde-wired', '1');
      control.addEventListener('click', function () {
        if (control.getAttribute('aria-pressed') === 'true') { play(svg); } else { stop(svg, false); }
      });
    });
    honourMotionPreference();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', wire);
  } else {
    wire();
  }
  if (reduce && reduce.addEventListener) {
    reduce.addEventListener('change', honourMotionPreference);
  }
})();
"##

/-- The classes carrying a mark's colour roles. -/
private def markClasses (mark : Mark) : Array String :=
  (if roles.contains mark.stroke then #["lfs-" ++ mark.stroke] else #[]) ++
    (if roles.contains mark.fill then #["lff-" ++ mark.fill] else #[]) ++
    (if mark.halo == "1" then #["lfh"] else #[])

open Verso.Output.Html in
private def renderAnim (animation : Anim) : Verso.Output.Html :=
  .tag animation.tag (animation.attrs.push ("repeatCount", "indefinite")) (.seq #[])

open Verso.Output.Html in
private def renderMark (mark : Mark) : Verso.Output.Html :=
  let classes := markClasses mark
  let attrs := mark.attrs
  let attrs :=
    if classes.isEmpty then attrs
    else attrs.push ("class", String.intercalate " " classes.toList)
  let attrs :=
    if mark.tex.isEmpty then attrs
    else attrs.push ("data-leanpde-tex", mark.tex)
  -- An SVG shape with no fill role is an outline: say so, or it comes out black.
  let attrs :=
    if mark.fill.isEmpty && mark.tag != "text" then attrs.push ("fill", "none") else attrs
  let animations := mark.anims.map renderAnim
  let body : Verso.Output.Html :=
    if mark.tag == "text" then .seq (#[Verso.Output.Html.text true mark.text] ++ animations)
    else .seq animations
  let element := Verso.Output.Html.tag mark.tag attrs body
  if mark.clip.isEmpty then element
  else .tag "g" #[("clip-path", "url(#" ++ mark.clip ++ ")")] element

open Verso.Output.Html in
private def renderClip (clip : Clip) : Verso.Output.Html :=
  {{
    <clipPath id={{clip.id}}>
      <rect x={{clip.x}} y={{clip.y}} width={{clip.w}} height={{clip.h}}/>
    </clipPath>
  }}

open Verso.Output.Html in
private def renderSvg (figure : Figure) : Verso.Output.Html :=
  let viewBox := "0 0 " ++ figure.width ++ " " ++ figure.height
  let defs : Verso.Output.Html :=
    if figure.clips.isEmpty then .seq #[]
    else {{ <defs>{{figure.clips.map renderClip}}</defs> }}
  {{
    <svg class="leanpde-fig-svg" viewBox={{viewBox}} role="img" "aria-label"={{figure.alt}}
         style={{"--leanpde-fig-viewbox-width: " ++ figure.width ++ "px"}}
         "data-leanpde-animated"={{if figure.animated.isEmpty then "0" else "1"}}
         xmlns="http://www.w3.org/2000/svg">
      {{defs}}
      {{figure.marks.map renderMark}}
    </svg>
  }}

open Verso.Output.Html in
private def renderFigure (figure : Figure) : Verso.Output.Html :=
  let control : Verso.Output.Html :=
    if figure.animated.isEmpty then .seq #[]
    else {{ <button class="leanpde-fig-pause" type="button" "aria-pressed"="false">"Pause"</button> }}
  {{
    <figure class="leanpde-fig" "data-leanpde-figure"={{figure.id}}>
      {{renderSvg figure}}
      <figcaption class="leanpde-fig-caption">
        <strong>{{.text true figure.title}}</strong>". "{{.text true figure.caption}}{{control}}
      </figcaption>
    </figure>
  }}

open Verso Doc Elab Genre Manual in
block_extension Block.figure (payload : String) where
  data := toJson payload
  traverse _id _data _contents := pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _blocks ↦ do
      let payload : String ←
        match ← Informal.ExtensionDecode.decode? (α := String) data
            (fun err ↦ s!"Malformed data in Block.figure ({err})") with
        | some payload => pure payload
        | Option.none => pure ""
      let figure := decodeOne payload
      pure <| .text s!"Figure: {figure.title}. The drawing is in the HTML edition of the book."
  toHtml :=
    open Verso.Doc.Html in
    some <| fun _goI _goB _id data _blocks ↦ do
      let payload : String ←
        match ← Informal.ExtensionDecode.decode? (α := String) data
            (fun err ↦ s!"Malformed data in Block.figure ({err})") with
        | some payload => pure payload
        | Option.none => pure ""
      return renderFigure (decodeOne payload)
  extraCss := [figureCss]
  extraJs := [figureJs]

/-- Select one figure of the generated model. -/
private def mkFigureBlock (id : String) : PartElabM (TSyntax `term) := do
  let (found, ids) ←
    match findFigure LeanPDE.FiguresData.json id with
    | .ok result => pure result
    | .error error => throwError "LeanPDE figure data is malformed: {error}"
  let some value := found
    | throwError "leanpde_figure: unknown figure {id}; known figures: {ids}"
  ``(Verso.Doc.Block.other
    (LeanPDE.Figures.Block.figure $(quote (Json.compress value))) #[])

/-- Which figure of the generated model a block shows. -/
structure FigureConfig where
  id : String

instance : Verso.ArgParse.FromArgs FigureConfig PartElabM where
  fromArgs := FigureConfig.mk <$> .positional' `id

open PartElabM in
/-- Insert a named figure from the generated drawing model, rejecting unknown names. -/
@[part_command Lean.Doc.Syntax.command]
public meta def figure : PartCommand
  | `(block|command{leanpde_figure $args*}) => do
    let cfg ← Verso.ArgParse.parseThe FigureConfig (← parseArgs args)
    addBlock (← mkFigureBlock cfg.id)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end LeanPDE.Figures
