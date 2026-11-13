/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.Construction
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.RigidGraph

/-!
# Operational atlases from differentiable graph boundary

A bounded open set with differentiable graph boundary admits the operational atlas used
by Sobolev extension and trace theorems. Local graph flattening supplies global chart
representatives of the same order. Compactness and the partition construction supply
the finite atlas and all cutoff fields without changing those representatives.

The chosen atlas can be installed locally with
`let := hgraph.c1ExtensionAtlas hopen hbounded`. No extension or trace estimate is
part of the geometric hypothesis.
-/

@[expose] public section

open Set

namespace SobolevSpace.Boundary

/-- A bounded open set with `C^m` graph boundary admits an operational extension atlas
whose total chart and inverse representatives are globally `C^m`. -/
theorem HasContDiffGraphBoundary.exists_c1ExtensionAtlas
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {m : ℕ∞}
    (hgraph : HasContDiffGraphBoundary m Ω) (hm : 1 ≤ m)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ∃ atlas : C1ExtensionAtlas n Ω,
      (∀ i, ContDiff ℝ m (atlas.chart i)) ∧
      (∀ i, ContDiff ℝ m (atlas.chart i).symm) := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 (Fact.out : 0 < 0)).elim
  | succ d =>
    exact exists_c1ExtensionAtlas_of_global_charts hm hopen hbounded
      (fun x ↦ hgraph.global_flattening_charts hm x x.property)

variable {n : ℕ} {Ω : Set (ℝ^(n + 1))}

/-- Every bounded open set with C1 graph boundary admits an operational extension atlas. -/
theorem HasC1GraphBoundary.nonempty_c1ExtensionAtlas (hgraph : HasC1GraphBoundary Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    Nonempty (C1ExtensionAtlas (n + 1) Ω) := by
  obtain ⟨atlas, _, _⟩ :=
    (hasContDiffGraphBoundary_one_iff.mpr hgraph).exists_c1ExtensionAtlas
      le_rfl hopen hbounded
  exact ⟨atlas⟩

/-- Choose the operational atlas constructed from C1 graph boundary on a bounded open set. -/
@[instance_reducible]
noncomputable def HasC1GraphBoundary.c1ExtensionAtlas (hgraph : HasC1GraphBoundary Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    C1ExtensionAtlas (n + 1) Ω :=
  Classical.choice (hgraph.nonempty_c1ExtensionAtlas hopen hbounded)

end SobolevSpace.Boundary
