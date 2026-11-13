/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Elliptic.Classical.Harmonic.Definitions
import PDE.FDeriv.Laplacian.Congruence

/-!
# Gluing local harmonic representatives

Continuous representatives that agree almost everywhere agree pointwise on open overlaps.
This gives a well-defined harmonic representative on the union. A countable subcover carries
the almost-everywhere identification from the patches to the whole domain.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace LaplacianEquation

/-- Local harmonic representatives of the same function glue to one harmonic
representative. No regularity or measurability of the original pointwise representative is
needed beyond the local almost-everywhere identifications. -/
theorem exists_isHarmonicPDE_ae_eq_of_locally
    {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ}
    (hlocal : ∀ x ∈ Ω, ∃ V : Set (ℝ^n), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∃ v : ℝ^n → ℝ, IsHarmonicPDE n v V ∧ u =ᵐ[volume.restrict V] v) :
    ∃ h : ℝ^n → ℝ, IsHarmonicPDE n h Ω ∧ u =ᵐ[volume.restrict Ω] h := by
  classical
  choose V hVo hxV hVU v hv hae using fun x : Ω ↦ hlocal x x.property
  have hcompat (i j : Ω) : EqOn (v i) (v j) (V i ∩ V j) := by
    have hi : u =ᵐ[volume.restrict (V i ∩ V j)] v i :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae i)
    have hj : u =ᵐ[volume.restrict (V i ∩ V j)] v j :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hae j)
    exact Measure.eqOn_open_of_ae_eq (hi.symm.trans hj) ((hVo i).inter (hVo j))
      ((hv i).contDiffOn.continuousOn.mono inter_subset_left)
      ((hv j).contDiffOn.continuousOn.mono inter_subset_right)
  let h : ℝ^n → ℝ := fun x ↦ if hx : x ∈ Ω then v ⟨x, hx⟩ x else 0
  have heq (i : Ω) : EqOn h (v i) (V i) := by
    intro x hx
    have hxΩ : x ∈ Ω := hVU i hx
    have hc := hcompat (⟨x, hxΩ⟩ : Ω) i ⟨hxV ⟨x, hxΩ⟩, hx⟩
    simpa only [h, dite_eq_left hxΩ] using hc
  have hnear (x : ℝ^n) (hx : x ∈ Ω) : h =ᶠ[𝓝 x] v ⟨x, hx⟩ :=
    Filter.eventually_of_mem ((hVo ⟨x, hx⟩).mem_nhds (hxV ⟨x, hx⟩))
      (fun _ hy ↦ heq ⟨x, hx⟩ hy)
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    have hvx := (hv ⟨x, hx⟩).contDiffAt_of_isOpen (hVo ⟨x, hx⟩) (hxV ⟨x, hx⟩)
    exact (hvx.congr_of_eventuallyEq (hnear x hx)).contDiffWithinAt
  · intro x hx
    rw [EuclideanLaplacian.laplacian_congr_nhds (hnear x hx)]
    exact (hv ⟨x, hx⟩).laplacian_eq_zero (hxV ⟨x, hx⟩)
  · have hcover : Ω ⊆ ⋃ i : Ω, V i := by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
    obtain ⟨J, hJ, hJcover⟩ :=
      (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover V hVo hcover
    apply ae_restrict_of_ae_restrict_of_subset hJcover
    apply (ae_eq_restrict_biUnion_iff V hJ u h).mpr
    intro i _
    filter_upwards [hae i, ae_restrict_mem (hVo i).measurableSet] with x hux hx
    exact hux.trans (heq i hx).symm

end LaplacianEquation
