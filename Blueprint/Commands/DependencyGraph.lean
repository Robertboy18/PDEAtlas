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
import Blueprint.Chapters.Symbolic
import Blueprint.Chapters.Variational
import VersoBlueprint.Commands.Graph

/-!
# LeanPDE dependency graph

This module loads every mathematical chapter and renders all registered
Blueprint statements in one graph block.

The graph keeps the authored `parent` groups, so Verso produces the full graph
with one dashed cluster per group, a synthetic group overview, and one focused
subgraph per group. Node labels are shortened to their last two identifier
segments because the group cluster already names the owning subject; when two
nodes would share that short label, both keep their last three segments so
that no view shows two nodes with the same label.
-/

namespace LeanPDE.DocGraph

open Lean Elab Command
open Verso Doc Elab Syntax
open Verso.Genre Manual

/-- Decode graph data previously serialized by `GraphBlockData.toJson`.

The dependency atlas contains hundreds of nodes. Embedding that value directly
as quoted Lean syntax creates a deeply nested term whose elaboration needs an
artificially large recursion limit. A JSON string keeps the generated syntax
shallow while preserving the same typed graph data. -/
private def decodeGraphBlockData (encoded : String) :
    Informal.Commands.GraphBlockData :=
  match Json.parse encoded with
  | .error error =>
      panic! s!"LeanPDE dependency graph JSON is malformed: {error}"
  | .ok value =>
      match fromJson? value with
      | .error error =>
          panic! s!"LeanPDE dependency graph data is malformed: {error}"
      | .ok graphData => graphData

/-- Node labels longer than this many characters break at the segment boundary. -/
private def displayLabelBreakWidth : Nat := 28

/-- Readable graph label for a Blueprint node identifier.

Verso prints atomic labels such as `«hyperbolic.transport.uniqueness»`. The
unescaped name is used and only the last `segments` dot-separated segments are
kept (two by default); the cluster label names the owning group. Long labels
break before their last segment so Graphviz boxes stay compact. -/
def displayLabelFor (label : Name) (segments : Nat := 2) : String :=
  let raw := label.toString (escape := false)
  let parts := raw.splitOn "."
  let shown := parts.drop (parts.length - segments)
  let joined := String.intercalate "." shown
  if joined.length > displayLabelBreakWidth && shown.length ≥ 2 then
    String.intercalate "." (shown.dropLast) ++ "\n" ++ shown.getLast!
  else
    joined

/-- Display labels for all nodes: two segments, or three where the two-segment
label would be shared by several nodes. -/
def displayLabels (labels : Array Name) : Array String :=
  let short := labels.map (displayLabelFor · 2)
  let counts : Std.HashMap String Nat :=
    short.foldl (init := {}) fun acc l ↦ acc.insert l (acc.getD l 0 + 1)
  labels.zipWith (fun label s ↦
    if counts.getD s 0 > 1 then displayLabelFor label 3 else s) short

/-- Render the complete LeanPDE Blueprint dependency graph. -/
private def mkDependencyGraphBlock : PartElabM (TSyntax `term) := do
  Informal.Environment.reportImportedConflicts
  let state := Informal.Environment.informalExt.getState (← getEnv)
  let graphModel := Informal.Graph.buildModel state (state.data.toArray.map (·.1))
    (groupTitles := state.groups.toArray)
  let labels := displayLabels (graphModel.nodes.map (·.label))
  let graphModel := {
    graphModel with
      nodes := graphModel.nodes.zipWith (fun node label ↦
        { node with displayLabel := label }) labels
  }
  let graphData : Informal.Commands.GraphBlockData := {
    graphModel := some graphModel
    options := { pack := true }
    previewMode := .pinned
    previewPlacement := .docked
  }
  let graphDataJson := Json.compress (toJson graphData)
  ``(Verso.Doc.Block.other
    (Informal.Commands.Block.graph
      (decodeGraphBlockData $(quote graphDataJson))) #[])

open PartElabM in
/-- Insert the dependency atlas built from the chapter's registered statement cards. -/
@[part_command Lean.Doc.Syntax.command]
public meta def dependencyGraph : PartCommand
  | `(block|command{leanpde_dependency_graph}) => do
    addBlock (← mkDependencyGraphBlock)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end LeanPDE.DocGraph
