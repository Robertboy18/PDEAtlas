/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import PDE.Common.Euclidean
import Mathlib.Analysis.Calculus.TangentCone.Prod
import PDE.Analysis.Calculus.HalfSpaceGluing

/-!
# Spatial derivatives of time slices of jointly `C¹` fields

Let `F : E × ℝ → G` be `C¹` on `univ ×ˢ J` for a set of times `J` with unique derivatives. Every
time slice `y ↦ F (y, t)`, `t ∈ J`, is differentiable with derivative the joint derivative within
`univ ×ˢ J` restricted to the spatial directions, so the spatial derivatives of the slices are
jointly continuous on `univ ×ˢ J`.

For a field on `ℝ² × ℝ` that vanishes on the closed upper half-plane outside a disc at every
time of a compact interval `[a, b]`, the field and the spatial derivatives of its slices are then
bounded on the closed half-plane uniformly in `t ∈ [a, b]`, and continuous in time uniformly on the
closed half-plane.

## Main results

* `hasFDerivAt_slice_of_contDiffOn`: a time slice has the spatial part of the joint derivative
  within `univ ×ˢ J` as its derivative.
* `continuousOn_fderiv_slice`: the spatial derivatives of the slices are jointly continuous.
* `fderiv_slice_eq_zero`: on the closed half-plane outside the support disc the spatial
  derivative of a slice vanishes.
* `exists_bounds_of_contDiffOn`: the uniform bounds and the uniform continuity in time of the
  field and of the spatial derivatives of its slices on the closed half-plane.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology

namespace PDE.Analysis

section Slice

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {F : E × ℝ → G} {J : Set ℝ}

/-- A time slice of a jointly `C¹` field has the spatial part of the joint derivative within
`univ ×ˢ J` as its derivative. -/
theorem hasFDerivAt_slice_of_contDiffOn (hF : ContDiffOn ℝ 1 F (univ ×ˢ J)) {x : E} {t : ℝ}
    (ht : t ∈ J) :
    HasFDerivAt (fun y ↦ F (y, t))
      ((fderivWithin ℝ F (univ ×ˢ J) (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  have hp : (x, t) ∈ univ ×ˢ J := ⟨mem_univ x, ht⟩
  have hd : HasFDerivWithinAt F (fderivWithin ℝ F (univ ×ˢ J) (x, t)) (univ ×ˢ J) (x, t) :=
    ((hF.differentiableOn one_ne_zero) (x, t) hp).hasFDerivWithinAt
  have hi : HasFDerivWithinAt (fun y : E ↦ (y, t)) (ContinuousLinearMap.inl ℝ E ℝ) univ x :=
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)).hasFDerivWithinAt
  have hcomp := hd.comp x hi (fun y _ ↦ (⟨mem_univ y, ht⟩ : (y, t) ∈ univ ×ˢ J))
  exact hasFDerivWithinAt_univ.mp hcomp

/-- The spatial derivative of a time slice of a jointly `C¹` field. -/
theorem fderiv_slice_of_contDiffOn (hF : ContDiffOn ℝ 1 F (univ ×ˢ J)) {x : E} {t : ℝ}
    (ht : t ∈ J) :
    fderiv ℝ (fun y ↦ F (y, t)) x =
      (fderivWithin ℝ F (univ ×ˢ J) (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ) :=
  (hasFDerivAt_slice_of_contDiffOn hF ht).fderiv

/-- The spatial derivatives of the time slices of a jointly `C¹` field are jointly continuous. -/
theorem continuousOn_fderiv_slice (hF : ContDiffOn ℝ 1 F (univ ×ˢ J)) (hJ : UniqueDiffOn ℝ J) :
    ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ (fun y ↦ F (y, p.2)) p.1) (univ ×ˢ J) := by
  have hc : ContinuousOn (fderivWithin ℝ F (univ ×ˢ J)) (univ ×ˢ J) :=
    hF.continuousOn_fderivWithin (UniqueDiffOn.prod uniqueDiffOn_univ hJ) le_rfl
  have hc' : ContinuousOn
      (fun p : E × ℝ ↦ (fderivWithin ℝ F (univ ×ˢ J) p).comp (ContinuousLinearMap.inl ℝ E ℝ))
      (univ ×ˢ J) :=
    hc.clm_comp continuousOn_const
  refine hc'.congr fun p hp ↦ ?_
  simpa using fderiv_slice_of_contDiffOn hF hp.2 (x := p.1)

end Slice

section HalfPlane

variable {f : ℝ^2 → ℝ → ℝ} {I : Set ℝ} {a b R : ℝ}

/-- On the closed half-plane outside the support disc the spatial derivative of a slice
vanishes. -/
theorem fderiv_slice_eq_zero {t : ℝ} (hd : Differentiable ℝ (fun y ↦ f y t))
    (hR : ∀ x : ℝ^2, 0 ≤ x 1 → R < ‖x‖ → f x t = 0) {x : ℝ^2} (hx : 0 ≤ x 1)
    (hxR : R < ‖x‖) : fderiv ℝ (fun y ↦ f y t) x = 0 := by
  have hU : {y : ℝ^2 | R < ‖y‖} ∈ 𝓝 x := isOpen_lt continuous_const continuous_norm |>.mem_nhds hxR
  have hzero : HasFDerivWithinAt (fun y ↦ f y t) (0 : ℝ^2 →L[ℝ] ℝ) {y : ℝ^2 | 0 ≤ y 1} x := by
    apply (hasFDerivWithinAt_const (0 : ℝ) x {y : ℝ^2 | 0 ≤ y 1}).congr_of_eventuallyEq
    · filter_upwards [inter_mem_nhdsWithin {y : ℝ^2 | 0 ≤ y 1} hU] with y hy
      exact hR y hy.1 hy.2
    · exact hR x hx hxR
  have hu : UniqueDiffWithinAt ℝ {y : ℝ^2 | 0 ≤ y 1} x :=
    uniqueDiffOn_coordinateHalfSpace (1 : Fin 2) x hx
  exact hu.eq ((hd x).hasFDerivAt.hasFDerivWithinAt) hzero

/-- **Uniform bounds of a jointly `C¹` field with bounded support.** If `f` is `C¹` on
`univ ×ˢ I`, `[a, b] ⊆ I` with `a < b`, and `f` vanishes on the closed half-plane outside the disc
of radius `R` at every `t ∈ [a, b]`, then `f` and the spatial derivatives of its slices are
bounded on the closed half-plane uniformly in `t ∈ [a, b]`, and both are continuous in time
uniformly on the closed half-plane. -/
theorem exists_bounds_of_contDiffOn (hab : a < b) (hI : Icc a b ⊆ I)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ I))
    (hR : ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → R < ‖x‖ → f x t = 0) :
    ∃ B B₁ : ℝ, 0 ≤ B ∧ 0 ≤ B₁ ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → |f x t| ≤ B) ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderiv ℝ (fun y ↦ f y t) x‖ ≤ B₁) ∧
      (∀ t ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ →
        ∀ x : ℝ^2, 0 ≤ x 1 → |f x s - f x t| ≤ ε) ∧
      (∀ t ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ →
        ∀ x : ℝ^2, 0 ≤ x 1 →
          ‖fderiv ℝ (fun y ↦ f y s) x - fderiv ℝ (fun y ↦ f y t) x‖ ≤ ε) := by
  set K : Set (ℝ^2 × ℝ) := closedBall (0 : ℝ^2) R ×ˢ Icc a b
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hfab : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ Icc a b) :=
    hf.mono (prod_mono subset_rfl hI)
  have hJ : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hc0 : ContinuousOn (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) K :=
    hfab.continuousOn.mono (prod_mono (subset_univ _) subset_rfl)
  have hc1 : ContinuousOn (fun p : ℝ^2 × ℝ ↦ fderiv ℝ (fun y ↦ f y p.2) p.1) K :=
    (continuousOn_fderiv_slice hfab hJ).mono (prod_mono (subset_univ _) subset_rfl)
  have hdiff (t : ℝ) (ht : t ∈ Icc a b) : Differentiable ℝ (fun y ↦ f y t) :=
    fun x ↦ (hasFDerivAt_slice_of_contDiffOn hfab ht (x := x)).differentiableAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc0
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn hc1
  have hB0 : ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → |f x t| ≤ max B 0 := by
    intro t ht x hx
    by_cases hxR : ‖x‖ ≤ R
    · exact (hB (x, t) ⟨mem_closedBall_zero_iff.mpr hxR, ht⟩).trans (le_max_left _ _)
    · rw [hR t ht x hx (lt_of_not_ge hxR), abs_zero]
      exact le_max_right _ _
  have hB₁0 : ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderiv ℝ (fun y ↦ f y t) x‖ ≤ max B₁ 0 := by
    intro t ht x hx
    by_cases hxR : ‖x‖ ≤ R
    · exact (hB₁ (x, t) ⟨mem_closedBall_zero_iff.mpr hxR, ht⟩).trans (le_max_left _ _)
    · rw [fderiv_slice_eq_zero (hdiff t ht) (hR t ht) hx (lt_of_not_ge hxR), norm_zero]
      exact le_max_right _ _
  have hu0 := hK.uniformContinuousOn_of_continuous hc0
  have hu1 := hK.uniformContinuousOn_of_continuous hc1
  refine ⟨max B 0, max B₁ 0, le_max_right _ _, le_max_right _ _, hB0, hB₁0, ?_, ?_⟩
  · intro t ht ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.mp hu0 ε hε
    refine ⟨δ, hδ, fun s hs hst x hx ↦ ?_⟩
    by_cases hxR : ‖x‖ ≤ R
    · have hxs : (x, s) ∈ K := ⟨mem_closedBall_zero_iff.mpr hxR, hs⟩
      have hxt : (x, t) ∈ K := ⟨mem_closedBall_zero_iff.mpr hxR, ht⟩
      have hd : dist (x, s) (x, t) < δ := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq]
        simpa using hst
      have := hδε (x, s) hxs (x, t) hxt hd
      rw [Real.dist_eq] at this
      exact this.le
    · rw [hR s hs x hx (lt_of_not_ge hxR), hR t ht x hx (lt_of_not_ge hxR), sub_zero, abs_zero]
      exact hε.le
  · intro t ht ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.mp hu1 ε hε
    refine ⟨δ, hδ, fun s hs hst x hx ↦ ?_⟩
    by_cases hxR : ‖x‖ ≤ R
    · have hxs : (x, s) ∈ K := ⟨mem_closedBall_zero_iff.mpr hxR, hs⟩
      have hxt : (x, t) ∈ K := ⟨mem_closedBall_zero_iff.mpr hxR, ht⟩
      have hd : dist (x, s) (x, t) < δ := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq]
        simpa using hst
      have := hδε (x, s) hxs (x, t) hxt hd
      rw [dist_eq_norm] at this
      exact this.le
    · rw [fderiv_slice_eq_zero (hdiff s hs) (hR s hs) hx (lt_of_not_ge hxR),
        fderiv_slice_eq_zero (hdiff t ht) (hR t ht) hx (lt_of_not_ge hxR), sub_zero, norm_zero]
      exact hε.le

end HalfPlane

end PDE.Analysis
