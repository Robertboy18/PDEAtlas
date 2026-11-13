/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic
import Blueprint.Chapters.Fluid
import Blueprint.Chapters.Foundations
import Blueprint.Chapters.Hyperbolic
import Blueprint.Chapters.Parabolic
import Blueprint.Chapters.Sobolev
import Blueprint.Chapters.Variational
import Blueprint.Commands.ComputationLedger
import Blueprint.Generated.CasLedgerData
import Blueprint.Generated.TextbookMapData
import Blueprint.Repository
import Lean
import Verso
import VersoManual
import VersoBlueprint.Environment
import VersoBlueprint.Lib.ExtensionDecode
import VersoBlueprint.TraversalIndex

/-!
# Textbook coverage map

`{leanpde_textbook_map "evans-pde"}` renders the recorded outline of Evans's
*Partial Differential Equations* with, for every section, the statement cards
whose cited pages fall in it; `{leanpde_textbook_map "others"}` renders the
briefer per-location tables of the remaining source documents. The data comes
from `Blueprint.Generated.TextbookMapData`, which `Blueprint/Tools/build-textbook-map.mjs`
regenerates from the chapter sources through the Blueprint release script.
Section starts were checked against the contents of the AMS second edition (2010).
Section-only citations retain their source reference and appear separately from
the page-based table; they do not supply a page number or a section boundary.

At elaboration time every card is matched against the registered Blueprint
nodes and the computation ledger: a card receives a `CAS` marker when
one of its Lean declarations owns a `cas`, `cega` or `#cas` call site recorded
in the production rows of `Blueprint.Generated.CasLedgerData`. This records a
calculation inside a declaration without measuring how much of its proof the
calculation supplies. Card links are resolved at render time through the traversal
index, as the ledger does.
-/

namespace LeanPDE.TextbookMap

open Lean Elab Command
open Verso Doc Elab Syntax
open Verso.Genre Manual

-- The HTML templates and the embedded stylesheet below keep their natural line
-- lengths; Verso templates and raw strings are not Lean code.
set_option linter.style.longLine false

/-- One card citation as recorded by the generator. -/
structure MapCard where
  label : String
  kind : String
  page : Option String := none
  citation : Option String := none
  file : String
  line : Nat
deriving FromJson, ToJson, Inhabited, Repr

/-- A section of the cited textbook with the cards placed in it. -/
structure MapSection where
  number : String
  title : String
  pageStart : Nat
  pageEnd : Nat
  approx : Bool
  role : String
  cards : Array MapCard
deriving FromJson, ToJson, Inhabited, Repr

/-- A chapter (or the block of appendices) of the cited textbook. -/
structure MapUnit where
  number : String
  title : String
  pageStart : Nat
  pageEnd : Nat
  approx : Bool
  sections : Array MapSection
deriving FromJson, ToJson, Inhabited, Repr

/-- One cited location of a document that has no table of contents in the map. -/
structure MapLocation where
  page : Option String := none
  citation : Option String := none
  cards : Array MapCard
deriving FromJson, ToJson, Inhabited, Repr

/-- One source document with either a table of contents (`layout = "toc"`) or a
list of cited locations (`layout = "list"`). -/
structure MapDocument where
  id : String
  title : String
  layout : String
  citations : Nat
  cards : Nat
  units : Array MapUnit
  unplaced : Array MapCard
  locations : Array MapLocation
deriving FromJson, ToJson, Inhabited, Repr

/-- Whole-map counts written by the generator. -/
structure MapSummary where
  citations : Nat
  cards : Nat
  documents : Nat
  evansSections : Nat
  evansCoveredSections : Nat
  evansUnplaced : Nat
deriving FromJson, ToJson, Inhabited, Repr

/-- The generated coverage-map document. -/
structure MapData where
  schemaVersion : Nat
  generator : String
  sourceRoot : String
  summary : MapSummary
  documents : Array MapDocument
deriving FromJson, ToJson, Inhabited

/-- A card together with the elaboration-time facts the renderer needs. -/
structure RenderedCard where
  card : MapCard
  /-- The card exists as a registered Blueprint node. -/
  known : Bool
  /-- One of the card's Lean declarations owns a call site in the computation ledger. -/
  cas : Bool
deriving FromJson, ToJson, Inhabited

/-- A section with enriched cards. -/
structure RenderedSection where
  section_ : MapSection
  cards : Array RenderedCard
deriving FromJson, ToJson, Inhabited

/-- A chapter with enriched sections. -/
structure RenderedUnit where
  unit : MapUnit
  sections : Array RenderedSection
deriving FromJson, ToJson, Inhabited

/-- A cited location with enriched cards. -/
structure RenderedLocation where
  page : Option String := none
  citation : Option String := none
  cards : Array RenderedCard
deriving FromJson, ToJson, Inhabited

/-- A document with enriched cards. -/
structure RenderedDocument where
  document : MapDocument
  units : Array RenderedUnit
  unplaced : Array RenderedCard
  locations : Array RenderedLocation
deriving FromJson, ToJson, Inhabited

/-- Payload of one rendered map block. -/
structure MapBlockData where
  scope : String
  summary : MapSummary
  documents : Array RenderedDocument
deriving FromJson, ToJson, Inhabited

/-- Decode the generated map JSON. -/
def decodeMap (encoded : String) : Except String MapData := do
  let value ← Json.parse encoded
  fromJson? value

/-- Decode a map block payload previously serialized with `toJson`. -/
private def decodeMapBlock (encoded : String) : MapBlockData :=
  match Json.parse encoded with
  | .error error => panic! s!"LeanPDE textbook map JSON is malformed: {error}"
  | .ok value =>
    match fromJson? value with
    | .error error => panic! s!"LeanPDE textbook map data is malformed: {error}"
    | .ok payload => payload

/-- Lean declarations of every production `cas`, `cega` or `#cas` call site. -/
def ledgerDeclarations (ledger : LeanPDE.Ledger.LedgerData) : NameSet :=
  ledger.rows.foldl (init := {}) fun acc row ↦
    if row.scope != "production" then acc else
    match row.decl.bind (·.fullName) with
    | some fullName => acc.insert fullName.toName
    | Option.none => acc

/-- Whether a registered node owns a declaration in the ledger. -/
def nodeIsCasChecked (checked : NameSet) (node : Informal.Data.Node) : Bool :=
  node.leanDecls.any fun decl ↦ checked.contains decl.eraseMacroScopes

/-- Enrich a card with the node registry and the ledger. -/
private def enrichCard (state : Informal.Environment.State) (checked : NameSet)
    (card : MapCard) : RenderedCard :=
  match state.data.get? (Name.mkSimple card.label) with
  | some registered => { card, known := true, cas := nodeIsCasChecked checked registered }
  | Option.none => { card, known := false, cas := false }

/-- Enrich every card of a document. -/
private def enrichDocument (state : Informal.Environment.State) (checked : NameSet)
    (document : MapDocument) : RenderedDocument :=
  let enrich := enrichCard state checked
  { document
    units := document.units.map fun unit ↦
      { unit
        sections := unit.sections.map fun section_ ↦
          { section_, cards := section_.cards.map enrich } }
    unplaced := document.unplaced.map enrich
    locations := document.locations.map fun location ↦
      { page := location.page, citation := location.citation,
        cards := location.cards.map enrich } }

/-- Layout and coverage shading for the textbook section tables. -/
def mapCss : String := r#"
.leanpde-tm {
  margin: 1rem 0 1.75rem;
}

.leanpde-tm-summary {
  margin: 0 0 0.6rem;
  color: #475569;
  font-size: 0.92rem;
}

.leanpde-tm-summary strong {
  color: #0f172a;
}

.leanpde-tm-legend {
  display: flex;
  flex-wrap: wrap;
  gap: 0.4rem 0.9rem;
  margin: 0 0 0.9rem;
  font-size: 0.82rem;
  color: #475569;
}

.leanpde-tm-legend-swatch {
  display: inline-block;
  width: 0.9rem;
  height: 0.9rem;
  margin-right: 0.3rem;
  border-radius: 3px;
  vertical-align: -0.12rem;
  border: 1px solid #cbd5e1;
}

.leanpde-tm-chapter {
  margin: 1.1rem 0 0.4rem;
  font-size: 1.05rem;
  font-weight: 600;
}

.leanpde-tm-chapter small {
  font-weight: 400;
  color: #64748b;
  margin-left: 0.4rem;
}

.leanpde-tm-scroll {
  overflow-x: auto;
}

.leanpde-tm-table {
  width: 100%;
  border-collapse: collapse;
  font-size: 0.86rem;
  line-height: 1.4;
}

.leanpde-tm-table th,
.leanpde-tm-table td {
  padding: 0.35rem 0.55rem;
  border-bottom: 1px solid #e2e8f0;
  text-align: left;
  vertical-align: top;
}

.leanpde-tm-table th {
  background: #f8fafc;
  font-weight: 600;
  white-space: nowrap;
}

.leanpde-tm-pages {
  white-space: nowrap;
  font-variant-numeric: tabular-nums;
  color: #475569;
}

.leanpde-tm-approx {
  color: #94a3b8;
  cursor: help;
}

.leanpde-tm-count {
  white-space: nowrap;
  font-variant-numeric: tabular-nums;
}

.leanpde-tm-cell {
  display: inline-block;
  min-width: 2.2rem;
  padding: 0.05rem 0.45rem;
  border-radius: 4px;
  text-align: center;
  font-weight: 600;
  border: 1px solid #cbd5e1;
}

.leanpde-tm-level-0 { background: #f1f5f9; color: #64748b; }
.leanpde-tm-level-1 { background: #dcfce7; color: #166534; }
.leanpde-tm-level-2 { background: #86efac; color: #14532d; }
.leanpde-tm-level-3 { background: #22c55e; color: #052e16; }
.leanpde-tm-level-4 { background: #15803d; color: #f0fdf4; border-color: #166534; }

.leanpde-tm-none {
  color: #b91c1c;
  font-size: 0.8rem;
  font-weight: 600;
  letter-spacing: 0.02em;
}

.leanpde-tm-muted {
  color: #94a3b8;
  font-size: 0.8rem;
  font-style: italic;
}

.leanpde-tm-cas {
  display: inline-block;
  margin-left: 0.35rem;
  padding: 0 0.4rem;
  border-radius: 999px;
  background: #dbeafe;
  color: #1e40af;
  font-size: 0.72rem;
  font-weight: 600;
  white-space: nowrap;
}

.leanpde-tm-cards > summary {
  cursor: pointer;
  color: #1d4ed8;
  font-size: 0.82rem;
}

.leanpde-tm-cards ul {
  margin: 0.3rem 0 0.2rem;
  padding-left: 1.1rem;
  columns: 2;
  column-gap: 1.5rem;
}

.leanpde-tm-cards li {
  break-inside: avoid;
  font-size: 0.82rem;
}

.leanpde-tm-cards li code {
  font-size: 0.78rem;
  overflow-wrap: anywhere;
}

.leanpde-tm-kind {
  color: #64748b;
  font-size: 0.72rem;
  text-transform: uppercase;
  letter-spacing: 0.03em;
  margin-right: 0.25rem;
}

.leanpde-tm-page, .leanpde-tm-citation {
  color: #64748b;
  font-size: 0.76rem;
  margin-left: 0.25rem;
}

.leanpde-tm-page {
  white-space: nowrap;
}

/* A theorem title can be longer than the mobile card list. */
.leanpde-tm-citation {
  white-space: normal;
  overflow-wrap: anywhere;
}

.leanpde-tm-card-cas {
  color: #1e40af;
  font-size: 0.72rem;
  margin-left: 0.25rem;
}

.leanpde-tm-doc {
  margin: 1.4rem 0 0.4rem;
  font-size: 1.05rem;
  font-weight: 600;
}

.leanpde-tm-doc small {
  font-weight: 400;
  color: #64748b;
  margin-left: 0.4rem;
}

@media (max-width: 760px) {
  .leanpde-tm-cards ul {
    columns: 1;
  }
}
"#

/-- Coverage level of a section from its card count; `0` means no card. -/
def coverageLevel (count : Nat) : Nat :=
  if count == 0 then 0
  else if count ≤ 2 then 1
  else if count ≤ 9 then 2
  else if count ≤ 24 then 3
  else 4

/-- Human-readable description of the coverage levels, used by the legend. -/
def coverageLegend : Array (Nat × String) :=
  #[(0, "no card"), (1, "1 to 2 cards"), (2, "3 to 9 cards"), (3, "10 to 24 cards"),
    (4, "25 or more cards")]

/-- Display name of a card kind. -/
private def kindText (kind : String) : String :=
  match kind with
  | "definition" => "Definition"
  | "theorem" => "Theorem"
  | "lemma" => "Lemma"
  | "proposition" => "Proposition"
  | "corollary" => "Corollary"
  | other => other

open Verso.Output.Html in
private def renderSourceLocation (page citation : Option String) : Verso.Output.Html :=
  let pageHtml : Verso.Output.Html :=
    match page with
    | some page => {{ <span class="leanpde-tm-page">{{.text true s!"p. {page}"}}</span> }}
    | none => .empty
  let citationHtml : Verso.Output.Html :=
    match citation with
    | some citation => {{ <span class="leanpde-tm-citation">{{.text true citation}}</span> }}
    | none => .empty
  .seq #[pageHtml, citationHtml]

open Verso.Output.Html in
private def renderCardLink (target : LeanPDE.Repository.Target) (s : TraverseState)
    (rendered : RenderedCard) : Verso.Output.Html :=
  let card := rendered.card
  let href? := Informal.TraversalIndex.Nodes.href? s (Name.mkSimple card.label)
  let name : Verso.Output.Html :=
    match href? with
    | some href => {{ <a href={{href}} title="Open the statement card"><code>{{.text true card.label}}</code></a> }}
    | Option.none =>
      LeanPDE.Repository.sourceRef target card.file card.line "The chapter source"
        (label := some {{ <code>{{.text true card.label}}</code> }})
  let cas : Verso.Output.Html :=
    if rendered.cas then {{ <span class="leanpde-tm-card-cas" title="A declaration of this card has a calculator call site in the ledger">"CAS"</span> }}
    else .empty
  {{
    <li "data-leanpde-map-card"={{card.label}}>
      <span class="leanpde-tm-kind">{{.text true (kindText card.kind)}}</span>
      {{name}}
      {{renderSourceLocation card.page card.citation}}
      {{cas}}
    </li>
  }}

open Verso.Output.Html in
private def renderCardList (target : LeanPDE.Repository.Target) (s : TraverseState) (cards : Array RenderedCard) (summary : String) :
    Verso.Output.Html :=
  if cards.isEmpty then .empty
  else
    {{
      <details class="leanpde-tm-cards">
        <summary>{{.text true summary}}</summary>
        <ul>{{cards.map (renderCardLink target s)}}</ul>
      </details>
    }}

open Verso.Output.Html in
/-- The count cell of a section row with its coverage colour. -/
private def renderCountCell (count casCount : Nat) : Verso.Output.Html :=
  let level := coverageLevel count
  let casChip : Verso.Output.Html :=
    if casCount == 0 then .empty
    else {{ <span class="leanpde-tm-cas" title="Cards with a declaration that has a calculator call site in the ledger">{{.text true s!"{casCount} CAS"}}</span> }}
  {{
    <span class="leanpde-tm-count">
      <span class={{s!"leanpde-tm-cell leanpde-tm-level-{level}"}}>{{.text true (toString count)}}</span>
      {{casChip}}
    </span>
  }}

open Verso.Output.Html in
private def renderPages (pageStart pageEnd : Nat) (approx : Bool) : Verso.Output.Html :=
  let range := if pageStart == pageEnd then toString pageStart else s!"{pageStart}-{pageEnd}"
  let mark : Verso.Output.Html :=
    if approx then {{ <span class="leanpde-tm-approx" title="Section boundary inferred, not confirmed by a cited page">" ≈"</span> }}
    else .empty
  {{ <span class="leanpde-tm-pages">{{.text true range}}{{mark}}</span> }}

open Verso.Output.Html in
private def renderSectionRow (target : LeanPDE.Repository.Target) (s : TraverseState) (rendered : RenderedSection) : Verso.Output.Html :=
  let section_ := rendered.section_
  let count := rendered.cards.size
  let casCount := rendered.cards.filter (·.cas) |>.size
  let status : Verso.Output.Html :=
    if count > 0 then
      renderCardList target s rendered.cards
        (if count == 1 then "1 card" else s!"{count} cards")
    else if section_.role == "problems" then
      {{ <span class="leanpde-tm-muted">"exercises; not a formalization target"</span> }}
    else if section_.role == "references" then
      {{ <span class="leanpde-tm-muted">"bibliography; not a formalization target"</span> }}
    else
      {{ <span class="leanpde-tm-none">"no mapped card"</span> }}
  {{
    <tr class="leanpde-tm-row" "data-leanpde-section"={{section_.number}} "data-leanpde-cards"={{toString count}}>
      <td><strong>{{.text true section_.number}}</strong>" "{{.text true section_.title}}</td>
      <td>{{renderPages section_.pageStart section_.pageEnd section_.approx}}</td>
      <td>{{renderCountCell count casCount}}</td>
      <td>{{status}}</td>
    </tr>
  }}

open Verso.Output.Html in
private def renderUnit (target : LeanPDE.Repository.Target) (s : TraverseState) (rendered : RenderedUnit) : Verso.Output.Html :=
  let unit := rendered.unit
  let resultSections := rendered.sections.filter (·.section_.role == "section")
  let covered := resultSections.filter (·.cards.size > 0) |>.size
  let cards := rendered.sections.foldl (init := 0) fun acc section_ ↦ acc + section_.cards.size
  let approxNote := if unit.approx then " ≈" else ""
  let headline :=
    s!"pp. {unit.pageStart}-{unit.pageEnd}{approxNote}; {covered} of {resultSections.size} sections " ++
      s!"have a card; {cards} cards"
  {{
    <section class="leanpde-tm-unit" "data-leanpde-chapter"={{unit.number}}>
      <h4 class="leanpde-tm-chapter">
        {{.text true s!"Chapter {unit.number}. {unit.title}"}}
        <small>{{.text true headline}}</small>
      </h4>
      <div class="leanpde-tm-scroll">
        <table class="leanpde-tm-table">
          <thead>
            <tr>
              <th>"Section"</th>
              <th>"Pages"</th>
              <th>"Cards"</th>
              <th>"Mapped statement cards"</th>
            </tr>
          </thead>
          <tbody>{{rendered.sections.map (renderSectionRow target s)}}</tbody>
        </table>
      </div>
    </section>
  }}

open Verso.Output.Html in
private def renderLegend : Verso.Output.Html :=
  {{
    <p class="leanpde-tm-legend">
      {{coverageLegend.map fun (level, description) ↦
        {{ <span><span class={{s!"leanpde-tm-legend-swatch leanpde-tm-level-{level}"}}></span>{{.text true description}}</span> }} }}
    </p>
  }}

open Verso.Output.Html in
private def renderTocDocument (target : LeanPDE.Repository.Target) (s : TraverseState) (rendered : RenderedDocument) : Verso.Output.Html :=
  let document := rendered.document
  let sections := rendered.units.foldl (init := (#[] : Array RenderedSection)) fun acc unit ↦
    acc ++ unit.sections.filter (·.section_.role == "section")
  let covered := sections.filter (·.cards.size > 0) |>.size
  let casCards := rendered.units.foldl (init := 0) fun acc unit ↦
    unit.sections.foldl (init := acc) fun acc section_ ↦ acc + (section_.cards.filter (·.cas)).size
  let summary :=
    s!"{document.citations} citations on {document.cards} cards place statements in {covered} of " ++
      s!"{sections.size} sections; {casCards} citations are on cards with recorded calculator call sites. " ++
      "Counts describe cited cards; section starts were checked against the AMS second edition (2010)."
  let unplaced : Verso.Output.Html :=
    if rendered.unplaced.isEmpty then .empty
    else
      {{
        <section class="leanpde-tm-unit" "data-leanpde-chapter"="unplaced">
          <h4 class="leanpde-tm-chapter">"Citations without a mapped page"</h4>
          {{renderCardList target s rendered.unplaced s!"{rendered.unplaced.size} cards"}}
        </section>
      }}
  {{
    <section class="leanpde-tm" "data-leanpde-textbook-map"={{document.id}} "data-leanpde-layout"="toc">
      <p class="leanpde-tm-summary">
        <strong>{{.text true document.title}}</strong>
        ". "
        {{.text true summary}}
      </p>
      {{renderLegend}}
      {{rendered.units.map (renderUnit target s)}}
      {{unplaced}}
    </section>
  }}

open Verso.Output.Html in
private def renderLocationRow (target : LeanPDE.Repository.Target) (s : TraverseState) (location : RenderedLocation) : Verso.Output.Html :=
  let count := location.cards.size
  let casCount := location.cards.filter (·.cas) |>.size
  {{
    <tr class="leanpde-tm-row" "data-leanpde-location"={{(toJson (location.page, location.citation)).compress}} "data-leanpde-cards"={{toString count}}>
      <td>{{renderSourceLocation location.page location.citation}}</td>
      <td>{{renderCountCell count casCount}}</td>
      <td>
        <details class="leanpde-tm-cards" open="open">
          <summary>{{.text true (if count == 1 then "1 card" else s!"{count} cards")}}</summary>
          <ul>{{location.cards.map (renderCardLink target s)}}</ul>
        </details>
      </td>
    </tr>
  }}

open Verso.Output.Html in
private def renderListDocument (target : LeanPDE.Repository.Target) (s : TraverseState) (rendered : RenderedDocument) : Verso.Output.Html :=
  let document := rendered.document
  {{
    <section class="leanpde-tm-unit" "data-leanpde-textbook-map"={{document.id}} "data-leanpde-layout"="list">
      <h4 class="leanpde-tm-doc">
        {{.text true document.title}}
        <small>{{.text true s!"{document.citations} citations on {document.cards} cards"}}</small>
      </h4>
      <div class="leanpde-tm-scroll">
        <table class="leanpde-tm-table">
          <thead>
            <tr>
              <th>"Cited location"</th>
              <th>"Cards"</th>
              <th>"Mapped statement cards"</th>
            </tr>
          </thead>
          <tbody>{{rendered.locations.map (renderLocationRow target s)}}</tbody>
        </table>
      </div>
    </section>
  }}

open Verso.Output.Html in
private def renderMap (target : LeanPDE.Repository.Target) (s : TraverseState) (payload : MapBlockData) : Verso.Output.Html :=
  if payload.scope == "others" then
    let docs := payload.documents.filter (·.document.layout == "list")
    let citations := docs.foldl (init := 0) fun acc doc ↦ acc + doc.document.citations
    {{
      <section class="leanpde-tm" "data-leanpde-textbook-map"="others" "data-leanpde-layout"="list">
        <p class="leanpde-tm-summary">
          <strong>"Other source documents"</strong>
          ". "
          {{.text true s!"{citations} citations across {docs.size} documents, grouped by the location each card cites. Counts describe cited cards; mathematical correspondence requires review of each statement."}}
        </p>
        {{docs.map (renderListDocument target s)}}
      </section>
    }}
  else
    .seq (payload.documents.filter (·.document.layout == "toc") |>.map (renderTocDocument target s))

open Verso Doc Elab Genre Manual in
block_extension Block.textbookMap (payload : MapBlockData) where
  data := toJson payload
  traverse _id _data _contents := pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _blocks ↦ do
      let payload : MapBlockData ←
        match ← Informal.ExtensionDecode.decode? (α := MapBlockData) data
            (fun err ↦ s!"Malformed data in Block.textbookMap ({err})") with
        | some payload => pure payload
        | Option.none => pure { scope := "", summary := default, documents := #[] }
      pure <| .text s!"The textbook coverage map ({payload.summary.citations} citations on {payload.summary.cards} cards, {payload.summary.evansCoveredSections} of {payload.summary.evansSections} sections of Evans with a card) is available in the HTML output."
  toHtml :=
    open Verso.Doc.Html in
    some <| fun _goI _goB _id data _blocks ↦ do
      let payload : MapBlockData ←
        match ← Informal.ExtensionDecode.decode? (α := MapBlockData) data
            (fun err ↦ s!"Malformed data in Block.textbookMap ({err})") with
        | some payload => pure payload
        | Option.none => pure { scope := "", summary := default, documents := #[] }
      let s ← HtmlT.state
      let target ← LeanPDE.Repository.readTarget
      return renderMap target s payload
  extraCss := [mapCss]

/-- Decode the generated map and the ledger, enrich every card, and build the block payload. -/
private def mkMapBlock (scope : String) : PartElabM (TSyntax `term) := do
  let map ←
    match decodeMap LeanPDE.TextbookMapData.json with
    | .ok map => pure map
    | .error error => throwError "LeanPDE textbook map data is malformed: {error}"
  let ledger ←
    match LeanPDE.Ledger.decodeLedger LeanPDE.CasLedger.json with
    | .ok ledger => pure ledger
    | .error error => throwError "LeanPDE computation ledger data is malformed: {error}"
  let state := Informal.Environment.informalExt.getState (← getEnv)
  let checked := ledgerDeclarations ledger
  let documents := map.documents.map (enrichDocument state checked)
  let unknown := documents.foldl (init := (#[] : Array String)) fun acc doc ↦
    let acc := doc.unplaced.foldl (init := acc) fun acc card ↦
      if card.known then acc else acc.push card.card.label
    let fromUnits := doc.units.foldl (init := acc) fun acc unit ↦
      unit.sections.foldl (init := acc) fun acc section_ ↦
        section_.cards.foldl (init := acc) fun acc card ↦
          if card.known then acc else acc.push card.card.label
    doc.locations.foldl (init := fromUnits) fun acc location ↦
      location.cards.foldl (init := acc) fun acc card ↦
        if card.known then acc else acc.push card.card.label
  unless unknown.isEmpty do
    throwError "LeanPDE textbook map cites cards that are not registered Blueprint nodes: {unknown}"
  let payload : MapBlockData := { scope, summary := map.summary, documents }
  let payloadJson := Json.compress (toJson payload)
  ``(Verso.Doc.Block.other
    (LeanPDE.TextbookMap.Block.textbookMap (decodeMapBlock $(quote payloadJson))) #[])

/-- Which part of the map a block shows. -/
structure MapConfig where
  scope : String

instance : Verso.ArgParse.FromArgs MapConfig PartElabM where
  fromArgs := MapConfig.mk <$> .positional' `scope

open PartElabM in
/-- Insert the Evans coverage map or the table of other sources from registered cards. -/
@[part_command Lean.Doc.Syntax.command]
public meta def textbookMap : PartCommand
  | `(block|command{leanpde_textbook_map $args*}) => do
    let cfg ← Verso.ArgParse.parseThe MapConfig (← parseArgs args)
    unless cfg.scope == "evans-pde" || cfg.scope == "others" do
      throwError "leanpde_textbook_map expects \"evans-pde\" or \"others\", got {cfg.scope}"
    addBlock (← mkMapBlock cfg.scope)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end LeanPDE.TextbookMap
