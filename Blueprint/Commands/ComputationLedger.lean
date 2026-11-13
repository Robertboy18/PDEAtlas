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
import Blueprint.Generated.CasLedgerData
import Blueprint.Repository
import Lean
import Verso
import VersoManual
import VersoBlueprint.Environment
import VersoBlueprint.Lib.ExtensionDecode
import VersoBlueprint.TraversalIndex

/-!
# Computation ledger data

This module owns the schema and decoder of the generated call-site data in
`Blueprint.Generated.CasLedgerData`: every `cas`, `cega` and `#cas` call site
of the `PDE` library with its module, line, enclosing declaration,
tactic form and statement, written by `Blueprint/Tools/build-cas-ledger.py` on
every Blueprint build. The textbook coverage map and the card index read the
data through `decodeLedger`, and the inline role `{casCount "..."}`
prints its totals in the prose of the computation chapter, so the numbers
quoted there are recomputed on every build.

The block `{leanpde_computation_ledger "production"}` (or `"examples"`)
renders the same data as tables in which a call site inside a declaration that
owns a statement card links to that card, rows without a card carry a `source`
chip to the module source, and every module and line cell links to the source
line. The block can be embedded wherever a full listing is wanted.
The chapter imports make every registered node visible to the card lookup,
exactly as `Blueprint.Commands.DependencyGraph` does for the atlas.
-/

namespace LeanPDE.Ledger

open Lean Elab Command
open Verso Doc Elab Syntax
open Verso.Genre Manual

/-- The declaration enclosing a call site, as recorded by the scanner. -/
structure LedgerDecl where
  kind : String
  name : Option String := none
  fullName : Option String := none
  line : Nat
  binders : String := ""
deriving FromJson, ToJson, Inhabited, Repr

/-- One `cas`, `cega` or `#cas` call site. -/
structure LedgerRow where
  scope : String
  library : String
  module : String
  path : String
  line : Nat
  tactic : String
  form : String
  statement : String
  decl : Option LedgerDecl := none
deriving FromJson, ToJson, Inhabited, Repr

/-- The generated ledger document; fields other than `rows` are informational. -/
structure LedgerData where
  rows : Array LedgerRow
deriving FromJson, ToJson, Inhabited

/-- A row together with the label of the statement card that links its declaration. -/
structure RenderedRow where
  row : LedgerRow
  card : Option Name := none
deriving FromJson, ToJson, Inhabited

/-- Payload of one rendered ledger table. -/
structure LedgerBlockData where
  scope : String
  rows : Array RenderedRow
deriving FromJson, ToJson, Inhabited

/-- Decode the generated ledger JSON. -/
def decodeLedger (encoded : String) : Except String LedgerData := do
  let value ← Json.parse encoded
  fromJson? value

/-- The number of distinct modules containing the given call sites. -/
def moduleCount (rows : Array LedgerRow) : Nat :=
  (rows.map (·.module)).toList.eraseDups.length

/-- One figure of the generated data, selected by name: `production`, `examples` and `pde`
count call sites, the same names with the suffix `-modules` count the modules that contain
them, and `tactic:<form>` counts the production sites written with one tactic form, for
example `tactic:cas`. -/
def countFor (ledger : LedgerData) (key : String) : Option Nat :=
  let production := ledger.rows.filter (·.scope == "production")
  let examples := ledger.rows.filter (·.scope == "examples")
  let pde := production.filter (·.library == "PDE")
  match key with
  | "production" => some production.size
  | "production-modules" => some (moduleCount production)
  | "examples" => some examples.size
  | "examples-modules" => some (moduleCount examples)
  | "pde" => some pde.size
  | "pde-modules" => some (moduleCount pde)
  | _ =>
    if key.startsWith "tactic:" then
      some (production.filter (·.tactic == key.drop "tactic:".length)).size
    else
      none

/-- The figure that `{casCount "..."}` prints; see `countFor` for the names. -/
structure CountArgs where
  key : String

instance : Verso.ArgParse.FromArgs CountArgs DocElabM where
  fromArgs := CountArgs.mk <$> .positional' `key

/-- Print one figure of the generated call-site data as ordinary text, so that the counts
quoted in the computation chapter are recomputed from the data on every build. The role is
used as `{casCount "production"}` after `open LeanPDE.Ledger (casCount)`. -/
@[role casCount]
public meta def casCount : RoleExpanderOf CountArgs
  | { key }, #[] => do
    let ledger ←
      match decodeLedger LeanPDE.CasLedger.json with
      | .ok ledger => pure ledger
      | .error error => throwError "LeanPDE computation ledger data is malformed: {error}"
    let some count := countFor ledger key
      | throwError "casCount does not know the figure {key}"
    ``(Verso.Doc.Inline.text $(quote (toString count)))
  | _, _ => throwError "casCount takes no contents"

/-- Decode a ledger table payload previously serialized with `toJson`. -/
private def decodeLedgerBlock (encoded : String) : LedgerBlockData :=
  match Json.parse encoded with
  | .error error => panic! s!"LeanPDE computation ledger JSON is malformed: {error}"
  | .ok value =>
    match fromJson? value with
    | .error error => panic! s!"LeanPDE computation ledger data is malformed: {error}"
    | .ok payload => payload

/-- The Blueprint card owning a declaration, when one exists. -/
private def cardFor (state : Informal.Environment.State) (fullName : String) : Option Name :=
  match state.leanNameLabels.get? fullName.toName with
  | some labels => labels[0]?
  | Option.none => none

/-- Stylesheet of the rendered ledger tables, chips and filter toolbar. -/
def ledgerCss : String := r#"
.leanpde-ledger {
  margin: 1rem 0 1.75rem;
}

.leanpde-ledger-summary {
  margin: 0 0 0.6rem;
  color: #475569;
  font-size: 0.92rem;
}

.leanpde-ledger-summary strong {
  color: #0f172a;
}

.leanpde-ledger-scroll {
  overflow-x: auto;
}

.leanpde-ledger-table {
  width: 100%;
  border-collapse: collapse;
  font-size: 0.86rem;
  line-height: 1.4;
}

.leanpde-ledger-table th,
.leanpde-ledger-table td {
  padding: 0.4rem 0.55rem;
  border-bottom: 1px solid #e2e8f0;
  text-align: left;
  vertical-align: top;
}

.leanpde-ledger-table th {
  background: #f8fafc;
  font-weight: 600;
  white-space: nowrap;
}

.leanpde-ledger-table code {
  font-size: 0.82rem;
  white-space: pre-wrap;
  overflow-wrap: anywhere;
}

.leanpde-ledger-line {
  text-align: right !important;
  font-variant-numeric: tabular-nums;
  white-space: nowrap;
}

.leanpde-ledger-kind {
  display: block;
  color: #64748b;
  font-size: 0.74rem;
  text-transform: uppercase;
  letter-spacing: 0.03em;
}

.leanpde-ledger-card {
  display: inline-block;
  margin-left: 0.4rem;
  padding: 0 0.4rem;
  border-radius: 999px;
  background: #dcfce7;
  color: #166534;
  font-size: 0.72rem;
  font-weight: 600;
  text-decoration: none;
  white-space: nowrap;
}

.leanpde-ledger-card:hover {
  background: #bbf7d0;
}

.leanpde-ledger-empty,
.leanpde-ledger-no-match {
  color: #475569;
  font-style: italic;
}

.leanpde-ledger-toolbar {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 0.5rem 0.75rem;
  margin: 0 0 0.6rem;
  font-size: 0.88rem;
}

.leanpde-ledger-toolbar label {
  font-weight: 600;
}

.leanpde-ledger-filter {
  flex: 1 1 16rem;
  min-width: 12rem;
  max-width: 32rem;
  padding: 0.3rem 0.5rem;
  border: 1px solid #cbd5e1;
  border-radius: 4px;
  font: inherit;
}

.leanpde-ledger-count {
  color: #475569;
  font-variant-numeric: tabular-nums;
}

.leanpde-ledger-sortable {
  cursor: pointer;
  user-select: none;
}

.leanpde-ledger-sortable:focus-visible {
  outline: 2px solid #2563eb;
  outline-offset: -2px;
}

.leanpde-ledger-sortable[aria-sort="ascending"]::after {
  content: " \25B2";
  font-size: 0.7em;
}

.leanpde-ledger-sortable[aria-sort="descending"]::after {
  content: " \25BC";
  font-size: 0.7em;
}

.leanpde-ledger-source {
  display: inline-block;
  margin-left: 0.4rem;
  padding: 0 0.4rem;
  border-radius: 999px;
  background: #e2e8f0;
  color: #1e293b;
  font-size: 0.72rem;
  font-weight: 600;
  text-decoration: none;
  white-space: nowrap;
}

.leanpde-ledger-source:hover {
  background: #cbd5e1;
}
"#

/-- Progressive enhancement of the rendered tables: a filter box that keeps the
rows containing every typed word, and sortable column headings for the module,
line, declaration and tactic columns. Without JavaScript the tables stay in
their generated module-and-line order. -/
def ledgerJs : String := r##"
(function () {
  function ledgerText(element) {
    return (element.textContent || "").replace(/\s+/g, " ").trim().toLowerCase();
  }

  function enhanceLedger(section) {
    var table = section.querySelector("table.leanpde-ledger-table");
    if (!table || !table.tBodies[0]) return;
    var tbody = table.tBodies[0];
    var rows = Array.prototype.slice.call(tbody.rows);
    rows.forEach(function (row, index) {
      row.setAttribute("data-leanpde-order", String(index));
    });
    var headers = table.tHead ? Array.prototype.slice.call(table.tHead.rows[0].cells) : [];
    var scope = section.getAttribute("data-leanpde-ledger-scope") || "ledger";
    var inputId = "leanpde-ledger-filter-" + scope;

    var toolbar = document.createElement("div");
    toolbar.className = "leanpde-ledger-toolbar";
    var label = document.createElement("label");
    label.setAttribute("for", inputId);
    label.textContent = "Filter";
    var input = document.createElement("input");
    input.type = "search";
    input.id = inputId;
    input.className = "leanpde-ledger-filter";
    input.placeholder = "module, declaration, tactic or statement";
    input.setAttribute("aria-describedby", inputId + "-count");
    var count = document.createElement("span");
    count.className = "leanpde-ledger-count";
    count.id = inputId + "-count";
    count.setAttribute("role", "status");
    count.setAttribute("aria-live", "polite");
    toolbar.appendChild(label);
    toolbar.appendChild(input);
    toolbar.appendChild(count);
    var scroll = section.querySelector(".leanpde-ledger-scroll");
    section.insertBefore(toolbar, scroll);
    var noMatch = document.createElement("p");
    noMatch.className = "leanpde-ledger-no-match";
    noMatch.textContent = "No rows contain every filter word.";
    noMatch.hidden = true;
    section.appendChild(noMatch);

    function applyFilter() {
      var terms = input.value.toLowerCase().split(/\s+/).filter(Boolean);
      var shown = 0;
      rows.forEach(function (row) {
        var text = ledgerText(row);
        var visible = terms.every(function (term) { return text.indexOf(term) >= 0; });
        row.hidden = !visible;
        if (visible) shown += 1;
      });
      count.textContent = shown === rows.length
        ? rows.length + " rows"
        : shown + " of " + rows.length + " rows";
      noMatch.hidden = shown > 0;
    }
    input.addEventListener("input", applyFilter);
    applyFilter();

    var sortState = { column: -1, descending: false };
    function cellKey(row, column) {
      var cell = row.cells[column];
      if (!cell) return "";
      if (cell.classList.contains("leanpde-ledger-line")) {
        return Number.parseInt(cell.textContent, 10) || 0;
      }
      return ledgerText(cell.querySelector("code") || cell);
    }
    function sortBy(column) {
      var descending = sortState.column === column && !sortState.descending;
      sortState = { column: column, descending: descending };
      var sorted = rows.slice().sort(function (a, b) {
        var keyA = cellKey(a, column);
        var keyB = cellKey(b, column);
        if (keyA === keyB) {
          // Ties keep the generated module-and-line order.
          return Number(a.getAttribute("data-leanpde-order"))
            - Number(b.getAttribute("data-leanpde-order"));
        }
        var order = keyA < keyB ? -1 : 1;
        return descending ? -order : order;
      });
      sorted.forEach(function (row) { tbody.appendChild(row); });
      headers.forEach(function (header, index) {
        if (!header.classList.contains("leanpde-ledger-sortable")) return;
        var sortState = index === column ? (descending ? "descending" : "ascending") : "none";
        header.setAttribute("aria-sort", sortState);
      });
    }
    headers.forEach(function (header, index) {
      // The statement column holds Lean signatures; ordering them alphabetically is not useful.
      if (index > 3) return;
      header.classList.add("leanpde-ledger-sortable");
      header.setAttribute("tabindex", "0");
      header.setAttribute("role", "button");
      header.setAttribute("aria-sort", "none");
      header.title = "Sort by " + ledgerText(header);
      header.addEventListener("click", function () { sortBy(index); });
      header.addEventListener("keydown", function (event) {
        if (event.key === "Enter" || event.key === " ") {
          event.preventDefault();
          sortBy(index);
        }
      });
    });
  }

  function enhanceAll() {
    document.querySelectorAll("section.leanpde-ledger").forEach(enhanceLedger);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", enhanceAll, { once: true });
  } else {
    enhanceAll();
  }
})();
"##

open Verso.Output.Html in
private def renderRow (target : LeanPDE.Repository.Target) (s : TraverseState)
    (rendered : RenderedRow) : Verso.Output.Html :=
  let row := rendered.row
  let sourceText := LeanPDE.Repository.sourceText row.path row.line
  let moduleCell := LeanPDE.Repository.linkOrText target row.path row.line row.path
    {{<code>{{.text true row.module}}</code>}}
  let lineCell := LeanPDE.Repository.linkOrText target row.path row.line sourceText
    (.text true (toString row.line))
  let declName : String :=
    match row.decl with
    | some decl => (decl.fullName <|> decl.name).getD decl.kind
    | Option.none => "#cas command"
  let declKind : String :=
    match row.decl with
    | some decl => decl.kind
    | Option.none => "command"
  let cardChip : Verso.Output.Html :=
    match rendered.card.bind (Informal.TraversalIndex.Nodes.href? s ·) with
    | some href => {{
        <a class="leanpde-ledger-card" href={{href}} title="Open the Blueprint statement card">
          "card"
        </a>
      }}
    | Option.none =>
      LeanPDE.Repository.linkOrText target row.path row.line sourceText (.text true "source")
        (class? := some "leanpde-ledger-source")
  {{
    <tr class="leanpde-ledger-row" "data-leanpde-scope"={{row.scope}}>
      <td>{{moduleCell}}</td>
      <td class="leanpde-ledger-line">{{lineCell}}</td>
      <td>
        <span class="leanpde-ledger-kind">{{.text true declKind}}</span>
        <code>{{.text true declName}}</code>
        {{cardChip}}
      </td>
      <td><code>{{.text true row.form}}</code></td>
      <td><code>{{.text true row.statement}}</code></td>
    </tr>
  }}

open Verso.Output.Html in
private def renderLedger (target : LeanPDE.Repository.Target) (s : TraverseState)
    (payload : LedgerBlockData) : Verso.Output.Html :=
  let modules := payload.rows.foldl (init := (#[] : Array String)) fun acc rendered ↦
    if acc.contains rendered.row.module then acc else acc.push rendered.row.module
  let linked := payload.rows.filter (·.card.isSome) |>.size
  let title : String :=
    if payload.scope == "examples" then "Instructional examples" else "Production modules"
  let summary : String :=
    s!"{payload.rows.size} call sites in {modules.size} modules; " ++
      s!"{linked} inside declarations that own a statement card."
  let body : Verso.Output.Html :=
    if payload.rows.isEmpty then
      {{ <p class="leanpde-ledger-empty">"No call sites are recorded for this scope."</p> }}
    else
      {{
        <div class="leanpde-ledger-scroll">
          <table class="leanpde-ledger-table">
            <thead>
              <tr>
                <th>"Module"</th>
                <th>"Line"</th>
                <th>"Declaration"</th>
                <th>"Tactic"</th>
                <th>"Statement"</th>
              </tr>
            </thead>
            <tbody>
              {{payload.rows.map (renderRow target s)}}
            </tbody>
          </table>
        </div>
      }}
  {{
    <section class="leanpde-ledger" "data-leanpde-ledger-scope"={{payload.scope}}>
      <p class="leanpde-ledger-summary">
        <strong>{{.text true title}}</strong>
        ". "
        {{.text true summary}}
      </p>
      {{body}}
    </section>
  }}

open Verso Doc Elab Genre Manual in
block_extension Block.casLedger (payload : LedgerBlockData) where
  data := toJson payload
  traverse _id _data _contents := pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id _data _blocks ↦
      pure <| .text "The computation ledger is available in the HTML output."
  toHtml :=
    open Verso.Doc.Html in
    some <| fun _goI _goB _id data _blocks ↦ do
      let payload : LedgerBlockData ←
        match ← Informal.ExtensionDecode.decode? (α := LedgerBlockData) data
            (fun err ↦ s!"Malformed data in Block.casLedger ({err})") with
        | some payload => pure payload
        | Option.none => pure { scope := "", rows := #[] }
      let s ← HtmlT.state
      let target ← LeanPDE.Repository.readTarget
      return renderLedger target s payload
  extraCss := [ledgerCss]
  extraJs := [ledgerJs]

/-- Rows of one scope, enriched with the labels of the cards owning their declarations. -/
private def mkLedgerBlock (scope : String) : PartElabM (TSyntax `term) := do
  let ledger ←
    match decodeLedger LeanPDE.CasLedger.json with
    | .ok ledger => pure ledger
    | .error error => throwError "LeanPDE computation ledger data is malformed: {error}"
  let state := Informal.Environment.informalExt.getState (← getEnv)
  let rows := ledger.rows.filter (·.scope == scope) |>.map fun row ↦
    { row, card := (row.decl.bind (·.fullName)).bind (cardFor state) : RenderedRow }
  let payload : LedgerBlockData := { scope, rows }
  let payloadJson := Json.compress (toJson payload)
  ``(Verso.Doc.Block.other
    (LeanPDE.Ledger.Block.casLedger (decodeLedgerBlock $(quote payloadJson))) #[])

/-- Which population of call sites a ledger table shows. -/
structure LedgerConfig where
  scope : String

instance : Verso.ArgParse.FromArgs LedgerConfig PartElabM where
  fromArgs := LedgerConfig.mk <$> .positional' `scope

open PartElabM in
/-- Insert the generated computation ledger for production declarations or examples. -/
@[part_command Lean.Doc.Syntax.command]
public meta def computationLedger : PartCommand
  | `(block|command{leanpde_computation_ledger $args*}) => do
    let cfg ← Verso.ArgParse.parseThe LedgerConfig (← parseArgs args)
    unless cfg.scope == "production" || cfg.scope == "examples" do
      throwError
        "leanpde_computation_ledger expects \"production\" or \"examples\", got {cfg.scope}"
    addBlock (← mkLedgerBlock cfg.scope)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end LeanPDE.Ledger
