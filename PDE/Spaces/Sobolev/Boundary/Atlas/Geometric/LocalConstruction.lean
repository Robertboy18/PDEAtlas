/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Construction

/-!
# Finite atlases preserving chart regularity

A bounded open set covered at its boundary by bounded flattening charts admits a finite
operational extension atlas. The finite subcover and smooth partition construction retain
the supplied total chart maps and their inverses, hence retain their global regularity.
The order may be any finite order at least one, or infinity.
-/

@[expose] public section

open Set

namespace SobolevSpace.Boundary

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A finite operational atlas preserves the global regularity of bounded flattenings
covering the boundary. The chart maps are unchanged when selecting the finite subcover. -/
theorem exists_c1ExtensionAtlas_of_global_charts {m : ℕ∞} (hm : 1 ≤ m)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hcharts : ∀ x : frontier Ω, ∃ c : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      (x : ℝ^n) ∈ c.source ∧ ContDiff ℝ m c ∧ ContDiff ℝ m c.symm ∧
      Bornology.IsBounded c.source ∧ Bornology.IsBounded c.target ∧
      ∀ y ∈ c.source, y ∈ Ω ↔ c y ∈ HalfSpace.upper n) :
    ∃ atlas : C1ExtensionAtlas n Ω,
      (∀ i, ContDiff ℝ m (atlas.chart i)) ∧
      (∀ i, ContDiff ℝ m (atlas.chart i).symm) := by
  classical
  choose chart hmem hforward hinverse hsource htarget hflatten using hcharts
  have hcompact : IsCompact (frontier Ω) :=
    hbounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun x ↦ (chart x).source) (fun x ↦ (chart x).open_source)
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  let index : Fin s.card → frontier Ω := fun i ↦ (s.equivFin.symm i).val
  let cover : FiniteBoundaryCover n Ω :=
    { isOpen := hopen
      bounded := hbounded
      N := s.card
      boundaryPatch := fun i ↦ (chart (index i)).source
      boundaryPatch_open := fun i ↦ (chart (index i)).open_source
      boundaryPatch_bounded := fun i ↦ hsource (index i)
      frontier_subset_iUnion := by
        intro x hx
        obtain ⟨y, hys, hy⟩ := mem_iUnion₂.mp (hs hx)
        refine mem_iUnion.2 ⟨s.equivFin ⟨y, hys⟩, ?_⟩
        simpa only [index, Equiv.symm_apply_apply] using hy }
  let charts : C1FlatteningCharts cover :=
    { chart := fun i ↦ chart (index i)
      cutoff_support_subset_source := cover.boundaryCutoff_support
      chart_contDiff := fun i ↦ (hforward (index i)).of_le (by exact_mod_cast hm)
      chart_symm_contDiff := fun i ↦ (hinverse (index i)).of_le (by exact_mod_cast hm)
      chart_mem_iff_upper := fun i ↦ hflatten (index i)
      chart_target_bounded := fun i ↦ htarget (index i) }
  exact ⟨charts.toC1ExtensionAtlas, fun i ↦ hforward (index i),
    fun i ↦ hinverse (index i)⟩

end SobolevSpace.Boundary
