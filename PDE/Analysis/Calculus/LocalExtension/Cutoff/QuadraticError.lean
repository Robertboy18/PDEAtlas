/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Cutoff.Hessian

import CAS.ExactTactic

/-!
# Quantitative error for a quadratically vanishing cutoff product

Local quadratic value and derivative estimates combine with weighted cutoff
bounds to control the actual product and its first two Fréchet derivatives.
The full Hessian product estimate is supplied by `norm_fderiv_fderiv_smul_sub_le`.

The Taylor estimates are hypotheses, not conclusions of this file. The scalar
constant `A` bounds the variation of the quadratic Hessian; `F` denotes the
codomain. All estimates are pointwise and require only local `C²` regularity.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local quadratic estimates and weighted cutoff bounds give quantitative
value, first-derivative, and full Hessian error bounds for `χ • Q`.

The radius may be zero: no estimate divides by `r`. No inner product,
completeness, finite dimension, or support assumption is required. -/
theorem quadratic_cutoff_error_bounds
    {χ : E → ℝ} {Q : E → F} {x : E}
    {B : E →L[ℝ] E →L[ℝ] F} {M A K r δ L : ℝ}
    (hχ : ContDiffAt ℝ 2 χ x) (hQ : ContDiffAt ℝ 2 Q x)
    (hχrange : χ x ∈ Icc (0 : ℝ) 1)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hr : r ∈ Icc (0 : ℝ) δ) (hδ : δ ≤ 1) (hL : 1 ≤ L)
    (hQ0 : ‖Q x‖ ≤ M * r ^ 2 / 2)
    (hQ1 : ‖fderiv ℝ Q x‖ ≤ M * r + A * r ^ 2 / 2)
    (hQ2 : ‖fderiv ℝ (fderiv ℝ Q) x - B‖ ≤ A * r)
    (hχ1 : r * ‖fderiv ℝ χ x‖ ≤ K / L)
    (hχ2 : r ^ 2 * ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ K / L) :
    ‖χ x • Q x‖ ≤ M * δ ^ 2 / 2 ∧
      ‖fderiv ℝ (fun y ↦ χ y • Q y) x‖ ≤
        (M + A / 2 + K * M / 2) * δ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ χ y • Q y)) x - χ x • B‖ ≤
        A * (1 + K) * δ + (5 / 2 : ℝ) * K * M / L := by
  have hr0 : 0 ≤ r := hr.1
  have hrδ : r ≤ δ := hr.2
  have hδ0 : 0 ≤ δ := hr0.trans hrδ
  have hχnorm : ‖χ x‖ ≤ 1 := (Real.norm_of_nonneg hχrange.1).trans_le hχrange.2
  have hrsq : r ^ 2 ≤ r := pow_le_of_le_one hr0 (hrδ.trans hδ) two_ne_zero
  have hKL : K / L ≤ K := div_le_self hK hL
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_smul]
    calc _ ≤ 1 * (M * r ^ 2 / 2) := by gcongr
      _ ≤ M * δ ^ 2 / 2 := by rw [one_mul]; gcongr
  · rw [fderiv_fun_smul (hχ.differentiableAt two_ne_zero) (hQ.differentiableAt two_ne_zero)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
    -- the cutoff gradient against the value of `Q`
    have hcut : ‖fderiv ℝ χ x‖ * ‖Q x‖ ≤ K * M / 2 * δ :=
      calc _ ≤ ‖fderiv ℝ χ x‖ * (M * r ^ 2 / 2) := by gcongr
        _ = M * r / 2 * (r * ‖fderiv ℝ χ x‖) := by cas
        _ ≤ M * δ / 2 * K := by gcongr; exact hχ1.trans hKL
        _ = _ := by cas
    linarith [mul_le_of_le_one_left (norm_nonneg (fderiv ℝ Q x)) hχnorm,
      mul_le_mul_of_nonneg_left hrδ hM,
      mul_le_mul_of_nonneg_left (hrsq.trans hrδ) hA]
  · refine (norm_sub_le_norm_sub_add_norm_sub _ (χ x • fderiv ℝ (fderiv ℝ Q) x) _).trans ?_
    have hbase : ‖χ x • fderiv ℝ (fderiv ℝ Q) x - χ x • B‖ ≤ A * r := by
      rw [show χ x • fderiv ℝ (fderiv ℝ Q) x - χ x • B =
        χ x • (fderiv ℝ (fderiv ℝ Q) x - B) from (smul_sub _ _ _).symm]
      exact (ContinuousLinearMap.opNorm_smul_le _ _).trans <|
        (mul_le_of_le_one_left (norm_nonneg (fderiv ℝ (fderiv ℝ Q) x - B)) hχnorm).trans hQ2
    -- the cross term and the cutoff curvature against the jets of `Q`
    have hcross : 2 * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ Q x‖ ≤ (2 * M + A * r) * (K / L) :=
      calc _ ≤ 2 * ‖fderiv ℝ χ x‖ * (M * r + A * r ^ 2 / 2) := by gcongr
        _ = (2 * M + A * r) * (r * ‖fderiv ℝ χ x‖) := by cas
        _ ≤ _ := by gcongr
    have hcurv : ‖Q x‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M / 2 * (K / L) :=
      calc _ ≤ M * r ^ 2 / 2 * ‖fderiv ℝ (fderiv ℝ χ) x‖ := by gcongr
        _ = M / 2 * (r ^ 2 * ‖fderiv ℝ (fderiv ℝ χ) x‖) := by cas
        _ ≤ _ := by gcongr
    have hKM : (5 / 2 : ℝ) * K * M / L = 5 / 2 * (M * (K / L)) := by cas
    linarith [norm_fderiv_fderiv_smul_sub_le hχ hQ, mul_le_mul_of_nonneg_left hKL
      (mul_nonneg hA hr0), mul_le_mul_of_nonneg_left hrδ hA,
      mul_le_mul_of_nonneg_left hrδ (mul_nonneg hA hK)]

end PDE.Analysis
