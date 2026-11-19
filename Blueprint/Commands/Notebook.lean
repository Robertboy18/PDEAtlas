/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Verso
import VersoManual

/-!
# Worked examples and interactive mathematics

The Introduction places `{leanpde_notebook}` where the worked examples belong.
The site builder fills this marker with proof excerpts from the same checkout,
including their source locations. Keeping the marker in the prose makes the
placement independent of paragraph wording or figure order.
The same mechanism places the mode explorer and the reading routes. Their formulas
and links are filled in by the site builder.
-/

namespace LeanPDE.Notebook

open Lean
open Verso Doc Elab Syntax
open Verso.Genre Manual

block_extension Block.openingNotebook where
  data := Json.null
  traverse _id _data _contents := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI _goB _id _data _blocks ↦ do
      return {{ <div "data-leanpde-notebook"="opening"></div> }}
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id _data _blocks ↦
      pure (.text "The HTML edition includes three worked examples with their Lean proofs.")

open PartElabM in
/-- Place the worked examples at this point in the chapter. -/
@[part_command Lean.Doc.Syntax.command]
public meta def notebook : PartCommand
  | `(block|command{leanpde_notebook}) => do
    addBlock (← ``(Verso.Doc.Block.other LeanPDE.Notebook.Block.openingNotebook #[]))
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

block_extension Block.modeExplorer where
  data := Json.null
  traverse _id _data _contents := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI _goB _id _data _blocks ↦ do
      return {{ <div "data-leanpde-learning"="modes"></div> }}
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id _data _blocks ↦
      pure (.text "The HTML edition compares heat and wave modes on a rod.")

open PartElabM in
/-- Place the comparison of heat and wave evolution. -/
@[part_command Lean.Doc.Syntax.command]
public meta def modeExplorer : PartCommand
  | `(block|command{leanpde_mode_explorer}) => do
    addBlock (← ``(Verso.Doc.Block.other LeanPDE.Notebook.Block.modeExplorer #[]))
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

block_extension Block.readingRoutes where
  data := Json.null
  traverse _id _data _contents := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI _goB _id _data _blocks ↦ do
      return {{ <div "data-leanpde-learning"="routes"></div> }}
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id _data _blocks ↦
      pure (.text "Reading routes follow Evans and symbolic computation.")

open PartElabM in
/-- Place the starting points for the book. -/
@[part_command Lean.Doc.Syntax.command]
public meta def readingRoutes : PartCommand
  | `(block|command{leanpde_reading_routes}) => do
    addBlock (← ``(Verso.Doc.Block.other LeanPDE.Notebook.Block.readingRoutes #[]))
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end LeanPDE.Notebook
