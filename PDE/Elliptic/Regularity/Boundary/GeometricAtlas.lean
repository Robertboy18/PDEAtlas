/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction

/-!
# Elliptic boundary atlases from local graphs

A bounded open set with `C^m` graph boundary, for `m ≥ 2`, admits a `C2BoundaryAtlas`
whose total chart and inverse representatives remain globally `C^m`. This supplies the
geometric inputs of the boundary regularity theorems directly from local graph data.

At finite order `k + 2`, both maps have that order, hence in particular the forward order
`k + 2` and inverse order `k + 1` used by the elliptic bootstrap. Local smooth graphs give
one atlas with smooth total representatives. If only finite-order graph descriptions
are given separately, the construction gives an atlas at each requested finite order.
-/

@[expose] public section

open Set

namespace SobolevSpace.Boundary

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {m : ℕ∞}

/-- Local graph geometry constructs a twice differentiable boundary atlas while retaining
the full global differentiability order of both chart representatives. -/
theorem HasContDiffGraphBoundary.exists_c2BoundaryAtlas
    (hgraph : HasContDiffGraphBoundary m Ω) (hm : 2 ≤ m)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ∃ atlas : SobolevSpace.C2BoundaryAtlas n Ω,
      (∀ i, ContDiff ℝ m (atlas.toC1ExtensionAtlas.chart i)) ∧
      (∀ i, ContDiff ℝ m (atlas.toC1ExtensionAtlas.chart i).symm) := by
  obtain ⟨atlas, hf, hg⟩ :=
    hgraph.exists_c1ExtensionAtlas ((by norm_num : (1 : ℕ∞) ≤ 2).trans hm) hopen hbounded
  exact ⟨{ toC1ExtensionAtlas := atlas
           chart_contDiff_two := fun i ↦ (hf i).of_le (WithTop.coe_le_coe.mpr hm)
           chart_symm_contDiff_two := fun i ↦ (hg i).of_le (WithTop.coe_le_coe.mpr hm) },
    hf, hg⟩

/-- Choose the boundary atlas constructed from local graph geometry. -/
noncomputable def HasContDiffGraphBoundary.c2BoundaryAtlas
    (hgraph : HasContDiffGraphBoundary m Ω) (hm : 2 ≤ m)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    SobolevSpace.C2BoundaryAtlas n Ω :=
  Classical.choose (hgraph.exists_c2BoundaryAtlas hm hopen hbounded)

/-- The chosen atlas preserves the full global regularity of the forward charts. -/
theorem HasContDiffGraphBoundary.c2BoundaryAtlas_chart_contDiff
    (hgraph : HasContDiffGraphBoundary m Ω) (hm : 2 ≤ m)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (i : Fin (hgraph.c2BoundaryAtlas hm hopen hbounded).toC1ExtensionAtlas.N) :
    ContDiff ℝ m ((hgraph.c2BoundaryAtlas hm hopen hbounded).toC1ExtensionAtlas.chart i) :=
  (Classical.choose_spec (hgraph.exists_c2BoundaryAtlas hm hopen hbounded)).1 i

/-- The chosen atlas preserves the full global regularity of the inverse charts. -/
theorem HasContDiffGraphBoundary.c2BoundaryAtlas_chart_symm_contDiff
    (hgraph : HasContDiffGraphBoundary m Ω) (hm : 2 ≤ m)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (i : Fin (hgraph.c2BoundaryAtlas hm hopen hbounded).toC1ExtensionAtlas.N) :
    ContDiff ℝ m
      ((hgraph.c2BoundaryAtlas hm hopen hbounded).toC1ExtensionAtlas.chart i).symm :=
  (Classical.choose_spec (hgraph.exists_c2BoundaryAtlas hm hopen hbounded)).2 i

/-- A bounded open set with C2 graph boundary admits the operational C2 atlas. -/
theorem HasContDiffGraphBoundary.nonempty_c2BoundaryAtlas
    (hgraph : HasContDiffGraphBoundary 2 Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    Nonempty (SobolevSpace.C2BoundaryAtlas n Ω) :=
  ⟨hgraph.c2BoundaryAtlas le_rfl hopen hbounded⟩

/-- A `C^{k+2}` boundary supplies the forward and inverse chart orders used in higher
elliptic boundary regularity; no atlas is assumed. -/
theorem HasContDiffGraphBoundary.exists_higherOrderBoundaryAtlas
    (k : ℕ) (hgraph : HasContDiffGraphBoundary (k + 2) Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ∃ atlas : SobolevSpace.C2BoundaryAtlas n Ω,
      (∀ i, ContDiff ℝ (k + 2) (atlas.toC1ExtensionAtlas.chart i)) ∧
      (∀ i, ContDiff ℝ (k + 1) (atlas.toC1ExtensionAtlas.chart i).symm) := by
  obtain ⟨atlas, hf, hg⟩ := hgraph.exists_c2BoundaryAtlas (by simp) hopen hbounded
  refine ⟨atlas, ?_, ?_⟩
  · simpa using hf
  · intro i
    exact (hg i).of_le (by norm_cast; omega)

/-- Local smooth graph descriptions give one operational atlas with globally smooth
forward and inverse representatives. -/
theorem HasContDiffGraphBoundary.exists_smoothBoundaryAtlas
    (hgraph : HasContDiffGraphBoundary ⊤ Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ∃ atlas : SobolevSpace.C2BoundaryAtlas n Ω,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (atlas.toC1ExtensionAtlas.chart i)) ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (atlas.toC1ExtensionAtlas.chart i).symm) :=
  hgraph.exists_c2BoundaryAtlas le_top hopen hbounded

/-- Separate graph descriptions at every positive finite order supply the geometric
inputs for each finite stage of elliptic boundary regularity. The atlas may depend on the order. -/
theorem exists_boundaryAtlases_of_forall_hasContDiffGraphBoundary
    (hgraph : ∀ k : ℕ, 1 ≤ k → HasContDiffGraphBoundary k Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ∀ k : ℕ, ∃ atlas : SobolevSpace.C2BoundaryAtlas n Ω,
      (∀ i, ContDiff ℝ (k + 2) (atlas.toC1ExtensionAtlas.chart i)) ∧
      (∀ i, ContDiff ℝ (k + 1) (atlas.toC1ExtensionAtlas.chart i).symm) := by
  intro k
  have hg : HasContDiffGraphBoundary (k + 2) Ω := by
    simpa using hgraph (k + 2) (by omega)
  exact hg.exists_higherOrderBoundaryAtlas k hopen hbounded

end SobolevSpace.Boundary
