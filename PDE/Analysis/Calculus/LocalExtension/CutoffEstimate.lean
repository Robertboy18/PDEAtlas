/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Lipschitz estimates for cutoffs

If a map vanishes at the center and is locally Lipschitz, multiplication by a bounded
scalar cutoff gives a global Lipschitz estimate in terms of the cutoff radius and slope.
A compactly supported `C²` map also has a globally Lipschitz derivative.
-/

@[expose] public section

open Function Metric Set
open scoped NNReal Topology

/-- The derivative of a compactly supported `C²` map is globally Lipschitz. -/
theorem ContDiff.lipschitzWith_fderiv_of_hasCompactSupport
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ K : ℝ≥0, LipschitzWith K (fderiv ℝ f) := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdc : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  exact ContDiff.lipschitzWith_of_hasCompactSupport
    (𝕂 := ℝ) (E' := E) (F' := E →L[ℝ] F) (f := fderiv ℝ f) hdc hdf (by simp)

/-- The cutoff product has Lipschitz constant at most `L + B L R`: the value bound
`‖N x‖ ≤ L R` controls the term in which the scalar cutoff is differentiated. -/
theorem LipschitzOnWith.smul_of_tsupport_subset_closedBall
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {N : E → F} {φ : E → ℝ}
    {L B : ℝ≥0} {R δ : ℝ} (hN : LipschitzOnWith L N (ball 0 δ))
    (hNd : Differentiable ℝ N) (hφd : Differentiable ℝ φ)
    (hφ : LipschitzWith B φ) (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (hsupport : tsupport (fun x ↦ φ x • N x) ⊆ closedBall 0 R)
    (hN0 : N 0 = 0) (hR : 0 ≤ R) (hRδ : R < δ) :
    LipschitzWith (L + B * L * ⟨R, hR⟩) (fun x ↦ φ x • N x) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hφd.smul hNd)
  intro x
  change ‖fderiv ℝ (fun y ↦ φ y • N y) x‖ ≤ (L : ℝ) + B * L * R
  by_cases hx : ‖x‖ ≤ R
  · have hxδ : x ∈ ball 0 δ := mem_ball_zero_iff.mpr (hx.trans_lt hRδ)
    have hDN : ‖fderiv ℝ N x‖ ≤ L :=
      norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hxδ) hN
    have hval : ‖N x‖ ≤ L * R := by
      have hv := hN.norm_sub_le hxδ (mem_ball_self (hR.trans_lt hRδ))
      simp only [hN0, sub_zero] at hv
      exact hv.trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
    calc
      ‖fderiv ℝ (fun y ↦ φ y • N y) x‖ =
          ‖φ x • fderiv ℝ N x + (fderiv ℝ φ x).smulRight (N x)‖ := by
        rw [fderiv_fun_smul (hφd x) (hNd x)]
      _ ≤ ‖φ x‖ * ‖fderiv ℝ N x‖ + ‖fderiv ℝ φ x‖ * ‖N x‖ := by
        simpa only [norm_smul, ContinuousLinearMap.norm_smulRight_apply] using
          norm_add_le (φ x • fderiv ℝ N x) ((fderiv ℝ φ x).smulRight (N x))
      _ ≤ 1 * L + B * (L * R) := by
        gcongr
        · exact hbound x
        · exact norm_fderiv_le_of_lipschitz ℝ hφ
      _ = (L : ℝ) + B * L * R := by ring
  · have hxout : x ∉ tsupport (fun y ↦ φ y • N y) := by
      intro h
      exact hx (mem_closedBall_zero_iff.mp (hsupport h))
    rw [fderiv_of_notMem_tsupport ℝ hxout, norm_zero]
    positivity
