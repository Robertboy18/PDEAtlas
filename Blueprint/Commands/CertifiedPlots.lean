/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Generated.CertifiedPlots
import Blueprint.Generated.CertifiedPlotsData
import Blueprint.Repository
import Lean
import Verso
import VersoManual
import VersoBlueprint.Lib.ExtensionDecode

/-!
# Certified plots

`{leanpde_certified_plot "heat"}`, `{leanpde_certified_plot "wave"}` and
`{leanpde_certified_plot "rarefaction"}` render the plots whose drawing model
is the JSON literal in `Blueprint.Generated.CertifiedPlotsData`. Every shaded
panel of a plot is one theorem of `Blueprint.Generated.CertifiedPlots`: on the
panel's rational interval of
the horizontal axis the plotted function lies between the two stated rational
bounds, proved by `cega` and checked by the kernel when the module is
compiled. Importing the generated module here is what makes the Blueprint build
compile those theorems.

The renderer does no arithmetic. `Blueprint/Tools/build-certified-plots.py` writes
the SVG coordinates of every bar and tick next to the mathematical data, and
`--check` verifies that the model lists exactly the theorems in the file, so
the picture and the statements cannot drift apart. Each bar links to the row of
the theorem listing below the plot, and the listing links to the theorem's
line in the generated module.
-/

namespace LeanPDE.CertifiedPlots

open Lean Elab Command
open Verso Doc Elab Syntax
open Verso.Genre Manual

-- The HTML templates and the embedded stylesheet below keep their natural line
-- lengths; Verso templates and raw strings are not Lean code.
set_option linter.style.longLine false

/-- One shaded panel: its rational bounds, its theorem and its SVG coordinates. -/
structure Bar where
  a : String
  b : String
  lo : String
  hi : String
  loDecimal : String
  hiDecimal : String
  name : String
  line : Nat
  statement : String
  x : String
  width : String
  y : String
  height : String
deriving FromJson, ToJson, Inhabited

/-- One curve of a plot, that is one value of the time parameter. -/
structure Curve where
  id : String
  param : String
  paramTeX : String
  color : String
  goal : String
  bars : Array Bar
deriving FromJson, ToJson, Inhabited

/-- The frame of the plotting area in SVG user units. -/
structure View where
  width : Nat
  height : Nat
  plotLeft : String
  plotTop : String
  plotRight : String
  plotBottom : String
deriving FromJson, ToJson, Inhabited

/-- A tick of the horizontal axis. -/
structure XTick where
  label : String
  x : String
deriving FromJson, ToJson, Inhabited

/-- A tick of the vertical axis. -/
structure YTick where
  label : String
  y : String
deriving FromJson, ToJson, Inhabited

/-- One plot: an explicit solution at several times. -/
structure Family where
  id : String
  title : String
  formulaTeX : String
  xLabel : String
  yLabel : String
  xMin : String
  xMax : String
  panels : Nat
  view : View
  xTicks : Array XTick
  yTicks : Array YTick
  curves : Array Curve
deriving FromJson, ToJson, Inhabited

/-- The generated drawing model. -/
structure PlotData where
  schemaVersion : Nat
  generator : String
  theorems : Nat
  families : Array Family
deriving FromJson, ToJson, Inhabited

/-- Decode the generated drawing model. -/
def decodePlots (encoded : String) : Except String PlotData := do
  let value ← Json.parse encoded
  fromJson? value

/-- Decode one plot previously serialized with `toJson`. -/
private def decodeFamily (encoded : String) : Family :=
  match Json.parse encoded with
  | .error error => panic! s!"LeanPDE certified plot JSON is malformed: {error}"
  | .ok value =>
    match fromJson? value with
    | .error error => panic! s!"LeanPDE certified plot data is malformed: {error}"
    | .ok payload => payload

/-- The page anchor of a theorem's row in the listing. -/
def rowId (name : String) : String :=
  "leanpde-cp-" ++ (name.replace "." "-")

/-- Layout and colours for certified range panels and their theorem listings. -/
def plotCss : String := r#"
.leanpde-cp {
  margin: 1.2rem 0 1.8rem;
}

.leanpde-cp-title {
  margin: 0 0 0.5rem;
  font-size: 0.95rem;
  color: #0f172a;
}

.leanpde-cp-svg {
  display: block;
  width: 100%;
  height: auto;
  max-width: 46rem;
  background: #ffffff;
  border: 1px solid #e2e8f0;
  border-radius: 6px;
}

.leanpde-cp-axis {
  stroke: #475569;
  stroke-width: 1;
}

.leanpde-cp-grid {
  stroke: #e2e8f0;
  stroke-width: 1;
}

.leanpde-cp-tick-label {
  font-family: "Helvetica Neue", "Segoe UI", Roboto, Arial, sans-serif;
  font-size: 10px;
  fill: #475569;
}

.leanpde-cp-axis-label {
  font-family: "Helvetica Neue", "Segoe UI", Roboto, Arial, sans-serif;
  font-size: 11px;
  font-style: italic;
  fill: #0f172a;
}

.leanpde-cp-bar rect {
  fill-opacity: 0.78;
  stroke: #ffffff;
  stroke-width: 0.4;
  transition: fill-opacity 0.12s ease-in-out;
}

.leanpde-cp-bar:hover rect,
.leanpde-cp-bar:focus rect {
  fill-opacity: 1;
  stroke: #0f172a;
  stroke-width: 1;
}

.leanpde-cp-bar:focus {
  outline: none;
}

.leanpde-cp-legend {
  display: flex;
  flex-wrap: wrap;
  gap: 0.35rem 1.1rem;
  margin: 0.55rem 0 0;
  font-size: 0.86rem;
  color: #334155;
}

.leanpde-cp-swatch {
  display: inline-block;
  width: 0.9rem;
  height: 0.9rem;
  margin-right: 0.35rem;
  border-radius: 2px;
  vertical-align: -0.12rem;
}

.leanpde-cp-note {
  margin: 0.35rem 0 0;
  font-size: 0.86rem;
  color: #475569;
}

.leanpde-cp-theorems {
  margin-top: 0.7rem;
}

.leanpde-cp-theorems > summary {
  cursor: pointer;
  color: #1d4ed8;
  font-size: 0.9rem;
}

.leanpde-cp-scroll {
  overflow-x: auto;
  margin-top: 0.5rem;
}

.leanpde-cp-table {
  width: 100%;
  border-collapse: collapse;
  font-size: 0.82rem;
  line-height: 1.4;
}

.leanpde-cp-table th,
.leanpde-cp-table td {
  padding: 0.3rem 0.5rem;
  border-bottom: 1px solid #e2e8f0;
  text-align: left;
  vertical-align: top;
}

.leanpde-cp-table th {
  background: #f8fafc;
  font-weight: 600;
  white-space: nowrap;
}

.leanpde-cp-table td.leanpde-cp-num {
  white-space: nowrap;
  font-variant-numeric: tabular-nums;
}

.leanpde-cp-table code {
  font-size: 0.78rem;
  white-space: pre-wrap;
  overflow-wrap: anywhere;
}

.leanpde-cp-table tr:target {
  background: #fef9c3;
}

.leanpde-cp-table tr:target td {
  border-bottom-color: #facc15;
}

.leanpde-cp-curve-marker {
  display: inline-block;
  width: 0.65rem;
  height: 0.65rem;
  border-radius: 2px;
  margin-right: 0.3rem;
  vertical-align: -0.05rem;
}
"#

open Verso.Output.Html in
private def renderBar (curve : Curve) (bar : Bar) : Verso.Output.Html :=
  let tooltip :=
    s!"t = {curve.param}, x ∈ [{bar.a}, {bar.b}]: value in [{bar.loDecimal}, {bar.hiDecimal}] " ++
      s!"(theorem {bar.name})"
  {{
    <a class="leanpde-cp-bar" href={{"#" ++ rowId bar.name}} "data-leanpde-theorem"={{bar.name}}>
      <rect x={{bar.x}} y={{bar.y}} width={{bar.width}} height={{bar.height}} fill={{curve.color}}>
        <title>{{.text true tooltip}}</title>
      </rect>
    </a>
  }}

open Verso.Output.Html in
private def renderXTick (view : View) (tick : XTick) : Verso.Output.Html :=
  {{
    <g>
      <line class="leanpde-cp-grid" x1={{tick.x}} x2={{tick.x}} y1={{view.plotTop}} y2={{view.plotBottom}}/>
      <text class="leanpde-cp-tick-label" x={{tick.x}} y={{s!"{view.height - 24}"}} "text-anchor"="middle">{{.text true tick.label}}</text>
    </g>
  }}

open Verso.Output.Html in
private def renderYTick (view : View) (tick : YTick) : Verso.Output.Html :=
  {{
    <g>
      <line class="leanpde-cp-grid" x1={{view.plotLeft}} x2={{view.plotRight}} y1={{tick.y}} y2={{tick.y}}/>
      <text class="leanpde-cp-tick-label" x={{s!"{view.plotLeft}"}} dx="-6" y={{tick.y}} dy="3.5" "text-anchor"="end">{{.text true tick.label}}</text>
    </g>
  }}

open Verso.Output.Html in
private def renderSvg (family : Family) : Verso.Output.Html :=
  let view := family.view
  let viewBox := s!"0 0 {view.width} {view.height}"
  let bars := family.curves.foldl (init := 0) fun acc curve ↦ acc + curve.bars.size
  let label :=
    s!"{family.title}: {bars} certified panels for {family.curves.size} times on x in [{family.xMin}, {family.xMax}]"
  {{
    <svg class="leanpde-cp-svg" viewBox={{viewBox}} role="img" "aria-label"={{label}} xmlns="http://www.w3.org/2000/svg">
      {{family.xTicks.map (renderXTick view)}}
      {{family.yTicks.map (renderYTick view)}}
      <line class="leanpde-cp-axis" x1={{view.plotLeft}} x2={{view.plotLeft}} y1={{view.plotTop}} y2={{view.plotBottom}}/>
      <line class="leanpde-cp-axis" x1={{view.plotLeft}} x2={{view.plotRight}} y1={{view.plotBottom}} y2={{view.plotBottom}}/>
      {{family.curves.map fun curve ↦
        {{ <g class="leanpde-cp-curve" "data-leanpde-curve"={{curve.id}}>{{curve.bars.map (renderBar curve)}}</g> }} }}
      <text class="leanpde-cp-axis-label" x={{view.plotRight}} y={{s!"{view.height - 6}"}} "text-anchor"="end">{{.text true family.xLabel}}</text>
      <text class="leanpde-cp-axis-label" x="6" y={{view.plotTop}} dy="10">{{.text true family.yLabel}}</text>
    </svg>
  }}

open Verso.Output.Html in
private def renderRow (target : LeanPDE.Repository.Target) (curve : Curve) (bar : Bar) :
    Verso.Output.Html :=
  let shortName := (bar.name.splitOn ".").getLastD bar.name
  let source := LeanPDE.Repository.sourceRef target "Blueprint/Generated/CertifiedPlots.lean"
    bar.line "The theorem in the generated module" (label := some {{<code>{{.text true shortName}}</code>}})
  {{
    <tr id={{rowId bar.name}} class="leanpde-cp-row">
      <td class="leanpde-cp-num">
        <span class="leanpde-cp-curve-marker" style={{s!"background: {curve.color}"}}></span>
        {{.text true curve.param}}
      </td>
      <td class="leanpde-cp-num">{{.text true s!"[{bar.a}, {bar.b}]"}}</td>
      <td class="leanpde-cp-num">{{.text true s!"[{bar.lo}, {bar.hi}]"}}</td>
      <td>{{source}}</td>
      <td><code>{{.text true bar.statement}}</code></td>
    </tr>
  }}

open Verso.Output.Html in
private def renderPlot (target : LeanPDE.Repository.Target) (family : Family) :
    Verso.Output.Html :=
  let bars := family.curves.foldl (init := 0) fun acc curve ↦ acc + curve.bars.size
  let legend : Verso.Output.Html :=
    {{
      <p class="leanpde-cp-legend">
        {{family.curves.map fun curve ↦
          {{ <span><span class="leanpde-cp-swatch" style={{s!"background: {curve.color}"}}></span>{{.text true s!"t = {curve.param}"}}</span> }} }}
      </p>
    }}
  let rows := family.curves.map fun curve ↦
    Verso.Output.Html.seq (curve.bars.map (renderRow target curve))
  {{
    <figure class="leanpde-cp" "data-leanpde-plot"={{family.id}} "data-leanpde-bars"={{toString bars}}>
      <p class="leanpde-cp-title">
        <strong>{{.text true family.title}}</strong>
        ", "
        <code class="bp_math inline">{{.text true family.formulaTeX}}</code>
      </p>
      {{renderSvg family}}
      {{legend}}
      <p class="leanpde-cp-note">
        {{.text true s!"{bars} shaded panels, {family.panels} per curve. The vertical extent of a panel is the certified range of the function on that panel of the x-axis; the curve runs inside it. Select a panel to open its theorem below."}}
      </p>
      <details class="leanpde-cp-theorems">
        <summary>{{.text true s!"The {bars} theorems behind this plot"}}</summary>
        <div class="leanpde-cp-scroll">
          <table class="leanpde-cp-table">
            <thead>
              <tr>
                <th>"t"</th>
                <th>"Panel"</th>
                <th>"Certified range"</th>
                <th>"Theorem"</th>
                <th>"Statement"</th>
              </tr>
            </thead>
            <tbody>{{rows}}</tbody>
          </table>
        </div>
      </details>
    </figure>
  }}

open Verso Doc Elab Genre Manual in
block_extension Block.certifiedPlot (payload : Family) where
  data := toJson payload
  traverse _id _data _contents := pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _blocks ↦ do
      let payload : Family ←
        match ← Informal.ExtensionDecode.decode? (α := Family) data
            (fun err ↦ s!"Malformed data in Block.certifiedPlot ({err})") with
        | some payload => pure payload
        | Option.none => pure default
      let bars := payload.curves.foldl (init := 0) fun acc curve ↦ acc + curve.bars.size
      pure <| .text s!"The certified plot of the {payload.title} ({bars} kernel-checked panels, theorems in Blueprint/Generated/CertifiedPlots.lean) is available in the HTML output."
  toHtml :=
    open Verso.Doc.Html in
    some <| fun _goI _goB _id data _blocks ↦ do
      let payload : Family ←
        match ← Informal.ExtensionDecode.decode? (α := Family) data
            (fun err ↦ s!"Malformed data in Block.certifiedPlot ({err})") with
        | some payload => pure payload
        | Option.none => pure default
      let target ← LeanPDE.Repository.readTarget
      return renderPlot target payload
  extraCss := [plotCss]

/-- Select one plot of the generated model. -/
private def mkPlotBlock (id : String) : PartElabM (TSyntax `term) := do
  let data ←
    match decodePlots LeanPDE.CertifiedPlotsData.json with
    | .ok data => pure data
    | .error error => throwError "LeanPDE certified plot data is malformed: {error}"
  let some family := data.families.find? (·.id == id)
    | throwError "leanpde_certified_plot: unknown plot {id}; known plots: {data.families.map (·.id)}"
  let payloadJson := Json.compress (toJson family)
  ``(Verso.Doc.Block.other
    (LeanPDE.CertifiedPlots.Block.certifiedPlot (decodeFamily $(quote payloadJson))) #[])

/-- Which plot of the generated model a block shows. -/
structure PlotConfig where
  id : String

instance : Verso.ArgParse.FromArgs PlotConfig PartElabM where
  fromArgs := PlotConfig.mk <$> .positional' `id

open PartElabM in
/-- Insert the requested certified plot and its panel certificates into the chapter. -/
@[part_command Lean.Doc.Syntax.command]
public meta def certifiedPlot : PartCommand
  | `(block|command{leanpde_certified_plot $args*}) => do
    let cfg ← Verso.ArgParse.parseThe PlotConfig (← parseArgs args)
    addBlock (← mkPlotBlock cfg.id)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end LeanPDE.CertifiedPlots
