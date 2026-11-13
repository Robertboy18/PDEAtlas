/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.SupportGap
public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs

/-!
# Support gaps supplied by the operational C1 atlas

The atlas provides compact partition supports and compact transported
supports inside open chart patches. Their positive gaps justify the artificial
edge steps in fractional extension. These radii depend on the fixed atlas and
its cutoffs, never on the function being extended.
-/

@[expose] public section

open Set

namespace SobolevSpace.Fractional.Localization

open SobolevSpace.Boundary SobolevSpace.Boundary.C1ExtensionAtlas.DerivedCutoffs
open SobolevSpace.HalfSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} [hΩ : C1ExtensionAtlas n Ω]

/-- The interior partition support has a positive gap from the physical complement. -/
theorem exists_interiorSupport_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ interiorSupport (n := n) (Ω := Ω),
      ∀ y ∉ Ω, δ ≤ dist x y :=
  exists_pos_le_dist_of_isCompact_subset_open isCompact_interiorSupport hΩ.isOpen
    interiorSupport_subset_domain

/-- The boundary partition support is separated from its artificial source edge. -/
theorem exists_boundarySupport_gap (i : Fin hΩ.N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ boundarySupport (n := n) (Ω := Ω) i,
      ∀ y ∉ (hΩ.chart i).source, δ ≤ dist x y :=
  exists_pos_le_dist_of_isCompact_subset_open (isCompact_boundarySupport i)
    (hΩ.chart i).open_source (boundarySupport_subset_source i)

/-- The transported boundary support is separated from the target edge.
It can meet the boundary of the upper half-space. -/
theorem exists_boundarySupportInTarget_gap (i : Fin hΩ.N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ boundarySupportInTarget (n := n) (Ω := Ω) i,
      ∀ y ∉ (hΩ.chart i).target, δ ≤ dist x y :=
  exists_pos_le_dist_of_isCompact_subset_open (isCompact_boundarySupportInTarget i)
    (hΩ.chart i).open_target (boundarySupportInTarget_subset_target i)

/-- Relocalizing the reflected extension gives a new compact support with its own gap. -/
theorem exists_targetCutoffSupport_gap (i : Fin hΩ.N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ targetCutoffSupport (n := n) (Ω := Ω) i,
      ∀ y ∉ (hΩ.chart i).target, δ ≤ dist x y :=
  exists_pos_le_dist_of_isCompact_subset_open (isCompact_targetCutoffSupport i)
    (hΩ.chart i).open_target (targetCutoffSupport_subset_target i)

/-- The relocalized inverse-chart support permits zero extension to the whole space. -/
theorem exists_pullbackSupport_gap (i : Fin hΩ.N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ pullbackSupport (n := n) (Ω := Ω) i,
      ∀ y ∉ (hΩ.chart i).source, δ ≤ dist x y :=
  exists_pos_le_dist_of_isCompact_subset_open (isCompact_pullbackSupport i)
    (hΩ.chart i).open_source (pullbackSupport_subset_source i)

/-- The source partition factor supplies a relative gap uniformly for all inputs. -/
theorem exists_boundaryCutoff_relative_gap (i : Fin hΩ.N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ^n → ℝ,
      ∀ x ∈ (hΩ.chart i).source ∩ Ω,
        (hΩ.boundaryCutoff i).toFun x * u x ≠ 0 →
          ∀ y ∈ Ω \ ((hΩ.chart i).source ∩ Ω), δ ≤ dist x y :=
  exists_pos_le_dist_mul_sdiff_inter (hΩ.boundaryCutoff i).hasCompactSupport
    (hΩ.chart i).open_source (hΩ.boundaryCutoff_support i)

/-- After flattening, the partition product has a gap only from the added
part of the upper half-space. No boundary vanishing condition is introduced. -/
theorem exists_transportedBoundaryCutoff_relative_gap (i : Fin hΩ.N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ^n → ℝ,
      ∀ x ∈ (hΩ.chart i).target ∩ upper n,
        (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm x) *
            u ((hΩ.chart i).symm x) ≠ 0 →
          ∀ y ∈ upper n \ ((hΩ.chart i).target ∩ upper n), δ ≤ dist x y := by
  obtain ⟨δ, hδ, hgap⟩ := exists_boundarySupportInTarget_gap (n := n) (Ω := Ω) i
  refine ⟨δ, hδ, fun u x hx hprod y hy ↦ hgap x ?_ y ?_⟩
  · refine ⟨(hΩ.chart i).symm x, ?_, (hΩ.chart i).right_inv hx.1⟩
    exact subset_closure
      (show (hΩ.chart i).symm x ∈ Function.support (hΩ.boundaryCutoff i).toFun from
        (mul_ne_zero_iff.mp hprod).1)
  · exact fun hyTarget ↦ hy.2 ⟨hyTarget, hy.1⟩

/-- The target cutoff, pulled back after reflection, supplies the gap for the
final whole-space zero extension in source coordinates. -/
theorem exists_relocalizedPullback_gap (i : Fin hΩ.N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ^n → ℝ, ∀ x ∈ (hΩ.chart i).source,
      (targetSupportCutoff (n := n) (Ω := Ω) i).toFun (hΩ.chart i x) *
          v (hΩ.chart i x) ≠ 0 →
        ∀ y ∉ (hΩ.chart i).source, δ ≤ dist x y := by
  obtain ⟨δ, hδ, hgap⟩ := exists_pullbackSupport_gap (n := n) (Ω := Ω) i
  refine ⟨δ, hδ, fun v x hx hprod y hy ↦ hgap x ?_ y hy⟩
  refine ⟨hΩ.chart i x, ?_, (hΩ.chart i).left_inv hx⟩
  exact subset_closure
    (show hΩ.chart i x ∈ Function.support
      (targetSupportCutoff (n := n) (Ω := Ω) i).toFun from
        (mul_ne_zero_iff.mp hprod).1)

end SobolevSpace.Fractional.Localization
