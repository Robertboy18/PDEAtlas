/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Linear growth of a `C¹` function from a zero

A function `C¹` on a closed convex set `s` of a proper real normed space with unique derivatives,
vanishing at the origin `0 ∈ s`, has its derivative within `s` bounded on every bounded part of
`s`, and the mean value inequality along the segments from the origin gives `‖f y‖ ≤ C ‖y‖` there.

## Main results

* `exists_norm_le_mul_norm_of_contDiffOn`: on `s ∩ closedBall 0 R` the derivative within `s` is
  bounded by some `C` and `‖f y‖ ≤ C ‖y‖`.
* `exists_norm_le_mul_norm_of_contDiff`: the case `s = univ`, on `closedBall 0 R`.
-/

@[expose] public section

open Set Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- **A `C¹` function vanishing at the origin grows at most linearly on bounded sets** of a closed
convex set `s` with unique derivatives: on `s ∩ closedBall 0 R` the derivative within `s` is
bounded by some `C` and `‖f y‖ ≤ C ‖y‖`. -/
theorem exists_norm_le_mul_norm_of_contDiffOn {f : E → F} {s : Set E} (hs : Convex ℝ s)
    (hsc : IsClosed s) (hu : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ 1 f s) (h0 : (0 : E) ∈ s)
    (hf0 : f 0 = 0) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ s, ‖y‖ ≤ R → ‖fderivWithin ℝ f s y‖ ≤ C ∧ ‖f y‖ ≤ C * ‖y‖ := by
  set K := s ∩ closedBall (0 : E) R
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_left hsc
  have hcont : ContinuousOn (fderivWithin ℝ f s) s := hf.continuousOn_fderivWithin hu le_rfl
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hcont.mono inter_subset_left)
  refine ⟨max C₀ 0, le_max_right _ _, fun y hy hyR ↦ ⟨?_, ?_⟩⟩
  · exact (hC₀ y ⟨hy, mem_closedBall_zero_iff.2 hyR⟩).trans (le_max_left _ _)
  · have hKc : Convex ℝ K := hs.inter (convex_closedBall 0 R)
    have hd : ∀ z ∈ K, HasFDerivWithinAt f (fderivWithin ℝ f s z) K z := fun z hz ↦
      ((hf.differentiableOn one_ne_zero z hz.1).hasFDerivWithinAt).mono inter_subset_left
    have hb : ∀ z ∈ K, ‖fderivWithin ℝ f s z‖ ≤ max C₀ 0 := fun z hz ↦
      (hC₀ z hz).trans (le_max_left _ _)
    have h0K : (0 : E) ∈ K := ⟨h0, mem_closedBall_self (le_trans (norm_nonneg y) hyR)⟩
    have := hKc.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb h0K
      ⟨hy, mem_closedBall_zero_iff.2 hyR⟩
    simpa [hf0] using this

/-- **A `C¹` function vanishing at the origin grows at most linearly on balls**: on
`closedBall 0 R` its derivative is bounded by some `C` and `‖f y‖ ≤ C ‖y‖`. -/
theorem exists_norm_le_mul_norm_of_contDiff {f : E → F} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0)
    (R : ℝ) : ∃ C, 0 ≤ C ∧ ∀ y : E, ‖y‖ ≤ R → ‖fderiv ℝ f y‖ ≤ C ∧ ‖f y‖ ≤ C * ‖y‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_mul_norm_of_contDiffOn convex_univ isClosed_univ
    uniqueDiffOn_univ hf.contDiffOn (mem_univ 0) hf0 R
  exact ⟨C, hC0, fun y hy ↦ by simpa [fderivWithin_univ] using hC y (mem_univ y) hy⟩

end PDE
