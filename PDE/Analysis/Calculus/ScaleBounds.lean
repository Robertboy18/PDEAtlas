/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import PDE.Common.Euclidean

/-!
# Bounds of dynamic scales and derivatives of dilations

A positive solution of `f' = r f` with `|r| ≤ M` on `[0, b]` stays between `f(0) e^{-M b}` and
`f(0) e^{M b}` (`exp_neg_mul_le_and_le_exp_mul`): its logarithm has derivative `r`. The derivative
of `x ↦ a g(c x)` at `x` is `a c` times the derivative of `g` at `c x`
(`fderiv_const_smul_comp_smul`).

## Main results

* `PDE.Analysis.exp_neg_mul_le_and_le_exp_mul`.
* `PDE.Analysis.fderiv_const_smul_comp_smul`.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis

set_option linter.missingDocs true

/-- **Two-sided exponential bounds for a positive solution of `f' = r f`** with `|r| ≤ M` on
`[0, b]`: `f(0) e^{-M b} ≤ f(b) ≤ f(0) e^{M b}`. -/
theorem exp_neg_mul_le_and_le_exp_mul {f r : ℝ → ℝ} {M b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ s ∈ Icc 0 b, HasDerivAt f (r s * f s) s) (hpos : ∀ s ∈ Icc 0 b, 0 < f s)
    (hr : ∀ s ∈ Icc 0 b, |r s| ≤ M) :
    f 0 * Real.exp (-(M * b)) ≤ f b ∧ f b ≤ f 0 * Real.exp (M * b) := by
  have hg : ∀ s ∈ Icc 0 b, HasDerivWithinAt (fun s ↦ Real.log (f s)) (r s) (Icc 0 b) s := by
    intro s hs
    have := (hf s hs).log (hpos s hs).ne'
    rw [mul_div_assoc, div_self (hpos s hs).ne', mul_one] at this
    exact this.hasDerivWithinAt
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' hg (fun s hs ↦ by
    rw [Real.norm_eq_abs]
    exact hr s (Ico_subset_Icc_self hs)) b ⟨hb, le_rfl⟩
  rw [Real.norm_eq_abs, sub_zero, abs_le] at hbound
  have h0 := hpos 0 ⟨le_rfl, hb⟩
  have hb' := hpos b ⟨hb, le_rfl⟩
  constructor
  · rw [← Real.exp_log h0, ← Real.exp_log hb', ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [hbound.1])
  · rw [← Real.exp_log h0, ← Real.exp_log hb', ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [hbound.2])

/-- The derivative of `x ↦ a g(c x)` at `x` is `a c` times the derivative of `g` at `c x`. -/
theorem fderiv_const_smul_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ^2 → E} {x : ℝ^2} (a c : ℝ) (hg : DifferentiableAt ℝ g (c • x)) :
    fderiv ℝ (fun z ↦ a • g (c • z)) x = (a * c) • fderiv ℝ g (c • x) := by
  have h1 : HasFDerivAt (fun z : ℝ^2 ↦ c • z) (c • ContinuousLinearMap.id ℝ (ℝ^2)) x :=
    (hasFDerivAt_id x).const_smul c
  have h2 := (hg.hasFDerivAt.comp x h1).const_smul a
  rw [show (fun z ↦ a • g (c • z)) = a • (g ∘ HSMul.hSMul c) from rfl, h2.fderiv]
  ext v
  simp [smul_smul]

end PDE.Analysis
