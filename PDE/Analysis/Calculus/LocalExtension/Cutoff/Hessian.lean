/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Hessian error from multiplication by a scalar cutoff

The second derivative of a scalar-times-vector product has two mixed terms.
After subtracting the undifferentiated scalar times the vector Hessian, their
full bilinear operator norms are controlled by the product of the first
derivative norms. The remaining term is controlled by the vector value and
the scalar Hessian. Only local second-order regularity is required.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace PDE.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplication by a scalar cutoff changes the full Fréchet Hessian by two
mixed first-derivative terms and the vector value times the cutoff Hessian.
The estimate uses the operator norm on `E →L[ℝ] E →L[ℝ] F`; neither finite
dimensionality nor completeness is required. -/
theorem norm_fderiv_fderiv_smul_sub_le
    {χ : E → ℝ} {Q : E → F} {x : E}
    (hχ : ContDiffAt ℝ 2 χ x) (hQ : ContDiffAt ℝ 2 Q x) :
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ χ y • Q y)) x -
        χ x • fderiv ℝ (fderiv ℝ Q) x‖ ≤
      2 * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ Q x‖ +
        ‖Q x‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖ := by
  have hχd := hχ.differentiableAt two_ne_zero
  have hQd := hQ.differentiableAt two_ne_zero
  have hDχ := (hχ.fderiv_right (m := 1) (by decide)).differentiableAt_one
  have hDQ := (hQ.fderiv_right (m := 1) (by decide)).differentiableAt_one
  let S := ContinuousLinearMap.smulRightL ℝ E F
  let M := (fderiv ℝ χ x).smulRight (fderiv ℝ Q x)
  let R := (S.flip (Q x)).comp (fderiv ℝ (fderiv ℝ χ) x)
  have hnear : fderiv ℝ (fun y ↦ χ y • Q y) =ᶠ[𝓝 x]
      fun y ↦ χ y • fderiv ℝ Q y + S (fderiv ℝ χ y) (Q y) := by
    filter_upwards [hχ.eventually (by simp), hQ.eventually (by simp)] with y hyχ hyQ
    exact fderiv_fun_smul (hyχ.differentiableAt two_ne_zero)
      (hyQ.differentiableAt two_ne_zero)
  have hformula : HasFDerivAt
      (fun y ↦ χ y • fderiv ℝ Q y + S (fderiv ℝ χ y) (Q y))
      ((χ x • fderiv ℝ (fderiv ℝ Q) x + M) +
        (S.precompR E (fderiv ℝ χ x) (fderiv ℝ Q x) +
          S.precompL E (fderiv ℝ (fderiv ℝ χ) x) (Q x))) x := by
    exact (hχd.hasFDerivAt.smul hDQ.hasFDerivAt).add
      (S.hasFDerivAt_of_bilinear hDχ.hasFDerivAt hQd.hasFDerivAt)
  have hcross : S.precompR E (fderiv ℝ χ x) (fderiv ℝ Q x) = M.flip := by
    ext v w
    rfl
  have hremaining : S.precompL E (fderiv ℝ (fderiv ℝ χ) x) (Q x) = R := by
    ext v w
    rfl
  have hHessian : fderiv ℝ (fderiv ℝ (fun y ↦ χ y • Q y)) x =
      χ x • fderiv ℝ (fderiv ℝ Q) x + (M + M.flip + R) := by
    calc
      _ = (χ x • fderiv ℝ (fderiv ℝ Q) x + M) +
          (S.precompR E (fderiv ℝ χ x) (fderiv ℝ Q x) +
            S.precompL E (fderiv ℝ (fderiv ℝ χ) x) (Q x)) :=
        hnear.fderiv_eq.trans hformula.fderiv
      _ = _ := by
        rw [hcross, hremaining]
        simp only [add_assoc]
  have hR : ‖R‖ ≤ ‖Q x‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖ := by
    refine R.opNorm_le_bound
      (mul_nonneg (norm_nonneg (Q x)) (fderiv ℝ (fderiv ℝ χ) x).opNorm_nonneg) ?_
    intro v
    change ‖(fderiv ℝ (fderiv ℝ χ) x v).smulRight (Q x)‖ ≤
      (‖Q x‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖) * ‖v‖
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc
      _ ≤ (‖fderiv ℝ (fderiv ℝ χ) x‖ * ‖v‖) * ‖Q x‖ :=
        mul_le_mul_of_nonneg_right
          ((fderiv ℝ (fderiv ℝ χ) x).le_opNorm v) (norm_nonneg _)
      _ = _ := by ac_rfl
  rw [hHessian, add_sub_cancel_left]
  calc
    ‖M + M.flip + R‖ ≤ ‖M‖ + ‖M.flip‖ + ‖R‖ :=
      (norm_add_le (M + M.flip) R).trans (add_le_add (norm_add_le M M.flip) le_rfl)
    _ ≤ ‖M‖ + ‖M.flip‖ + ‖Q x‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖ :=
      add_le_add le_rfl hR
    _ = _ := by
      simp only [ContinuousLinearMap.opNorm_flip, M,
        ContinuousLinearMap.norm_smulRight_apply, ← two_mul, mul_assoc]

end PDE.Analysis
