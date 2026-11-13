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
import Blueprint.Commands.TextbookMap
import Blueprint.Generated.CasLedgerData
import Lean
import Verso
import VersoManual
import VersoBlueprint.Environment
import VersoBlueprint.Lib.ExtensionDecode

/-!
# Card index data file

`{leanpde_card_index}` writes `-verso-data/leanpde-cards.json` during
traversal: one entry per registered statement card with the card's kind, its
group, its authored tags and whether one of its Lean declarations owns a call
site in the generated computation audit. The rendered-site audit checks the
file against the Blueprint manifest and the audit data, and the site script can
read it to find the dependency-atlas view of a card's group. In the book the
block renders one sentence stating the counts.

The entries are computed at elaboration time from the same Blueprint
environment that renders the cards, so the file cannot disagree with the
cards on the page.
-/

namespace LeanPDE.CardIndex

open Lean Elab Command
open Verso Doc Elab Syntax
open Verso.Genre Manual

-- The HTML template below keeps its natural line length; Verso templates are not Lean code.
set_option linter.style.longLine false

/-- One statement card as seen by the site script. -/
structure CardEntry where
  /-- The authored label without guillemets, for example `parabolic.heat_kernel`. -/
  label : String
  /-- The card's kind as a lower-case word. -/
  kind : String
  /-- The label of the card's `:::group`, or the empty string. -/
  group : String
  /-- The authored `(tags := ...)`. -/
  tags : Array String
  /-- One of the card's Lean declarations owns a computation-ledger call site. -/
  cas : Bool
deriving FromJson, ToJson, Inhabited

/-- Payload of the card index block. -/
structure CardIndexData where
  cards : Array CardEntry
deriving FromJson, ToJson, Inhabited

/-- Site-relative path of the data file, below `-verso-data/`. -/
def dataFileName : String := "leanpde-cards.json"

/-- Compact JSON object keyed by label, as read by the site script. -/
def CardIndexData.toDataJson (data : CardIndexData) : Json :=
  let cards := data.cards.map fun card ↦
    (card.label, Json.mkObj [
      ("k", card.kind),
      ("g", card.group),
      ("t", toJson card.tags),
      ("c", card.cas)])
  Json.mkObj [("schemaVersion", (1 : Nat)), ("cards", Json.mkObj cards.toList)]

/-- Decode a card index payload previously serialized with `toJson`. -/
private def decodeCardIndex (encoded : String) : CardIndexData :=
  match Json.parse encoded with
  | .error error => panic! s!"LeanPDE card index JSON is malformed: {error}"
  | .ok value =>
    match fromJson? value with
    | .error error => panic! s!"LeanPDE card index data is malformed: {error}"
    | .ok payload => payload

/-- Lower-case kind word of a node. -/
private def kindWord (kind : Informal.Data.NodeKind) : String :=
  match kind with
  | .definition => "definition"
  | .proposition => "proposition"
  | .lemma => "lemma"
  | .theorem => "theorem"
  | .corollary => "corollary"

/-- Every registered node as a card entry, sorted by label. -/
def collectCards (state : Informal.Environment.State) (checked : NameSet) : Array CardEntry :=
  let entries := state.data.foldl (init := (#[] : Array CardEntry)) fun acc label node ↦
    acc.push {
      label := label.toString (escape := false)
      kind := kindWord node.kind
      group := (node.parent.map (·.toString (escape := false))).getD ""
      tags := node.tags
      cas := LeanPDE.TextbookMap.nodeIsCasChecked checked node }
  entries.qsort fun a b ↦ a.label < b.label

open Verso.Output.Html in
/-- The visible note rendered where the block is placed; the data file is the real product. -/
private def renderIndexNote (payload : CardIndexData) : Verso.Output.Html :=
  let count := toString payload.cards.size
  let tagged := toString (payload.cards.filter (·.tags.contains "provenance:leanpde")).size
  let cas := toString (payload.cards.filter (·.cas)).size
  let summary :=
    s!", an index of the {count} statement cards with their kind, group and tags; " ++
      s!"{cas} of them have a declaration proved with the checked CAS."
  {{
    <p class="leanpde-card-index" "data-leanpde-cards"={{count}} "data-leanpde-cards-leanpde"={{tagged}} "data-leanpde-cards-cas"={{cas}}>
      "The same build writes "
      <code>{{.text true s!"-verso-data/{dataFileName}"}}</code>
      {{.text true summary}}
    </p>
  }}

open Verso Doc Elab Genre Manual in
block_extension Block.cardIndex (payload : CardIndexData) where
  data := toJson payload
  traverse _id data _contents := do
    match ← Informal.ExtensionDecode.decode? (α := CardIndexData) data
        (fun err ↦ s!"Malformed data in Block.cardIndex ({err})") with
    | some payload =>
      let contents := (Json.compress payload.toDataJson).toUTF8
      modify fun (st : TraverseState) ↦
        st.modifyHtmlAssets fun assets ↦
          { assets with
            extraDataFiles := assets.extraDataFiles.insert { filename := dataFileName, contents } }
    | Option.none => pure ()
    pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id _data _blocks ↦ pure .empty
  toHtml :=
    open Verso.Doc.Html in
    some <| fun _goI _goB _id data _blocks ↦ do
      let payload : CardIndexData ←
        match ← Informal.ExtensionDecode.decode? (α := CardIndexData) data
            (fun err ↦ s!"Malformed data in Block.cardIndex ({err})") with
        | some payload => pure payload
        | Option.none => pure { cards := #[] }
      return renderIndexNote payload

/-- Build the card index from the Blueprint environment and the ledger. -/
private def mkCardIndexBlock : PartElabM (TSyntax `term) := do
  let ledger ←
    match LeanPDE.Ledger.decodeLedger LeanPDE.CasLedger.json with
    | .ok ledger => pure ledger
    | .error error => throwError "LeanPDE computation ledger data is malformed: {error}"
  let state := Informal.Environment.informalExt.getState (← getEnv)
  let checked := LeanPDE.TextbookMap.ledgerDeclarations ledger
  let payload : CardIndexData := { cards := collectCards state checked }
  if payload.cards.isEmpty then
    throwError "LeanPDE card index found no registered Blueprint nodes"
  let payloadJson := Json.compress (toJson payload)
  ``(Verso.Doc.Block.other
    (LeanPDE.CardIndex.Block.cardIndex (decodeCardIndex $(quote payloadJson))) #[])

open PartElabM in
/-- Insert the statement index used to connect cards, computation records, and atlas views. -/
@[part_command Lean.Doc.Syntax.command]
public meta def cardIndex : PartCommand
  | `(block|command{leanpde_card_index}) => do
    addBlock (← mkCardIndexBlock)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end LeanPDE.CardIndex
