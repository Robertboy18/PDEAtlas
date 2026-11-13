/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.AngularLipschitz
public import PDE.FDeriv.Euclidean.Norm
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivatives of radial factors with normalized angular fields

Normalization is differentiable away from zero, with derivative bounded by
twice the inverse radius. The product and chain rules give a quantitative
bound for the derivative of `f ‖x‖ • H (normalize x)`. The bound separates
the radial derivative from the angular derivative and preserves the radial
factor needed for decay estimates.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

open NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalization has the derivative given by the product rule for `‖x‖⁻¹ • x`. -/
theorem hasFDerivAt_normalize {x : E} (hx : x ≠ 0) :
    HasFDerivAt NormedSpace.normalize
      (‖x‖⁻¹ • ContinuousLinearMap.id ℝ E +
        ((-(‖x‖ ^ 2)⁻¹) • innerSL ℝ (normalize x)).smulRight x) x := by
  exact ((hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x
    (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx)).smul (hasFDerivAt_id x)

/-- The normalization derivative has operator norm at most twice the inverse radius. -/
theorem norm_fderiv_normalize_le {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ NormedSpace.normalize x‖ ≤ 2 / ‖x‖ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [(hasFDerivAt_normalize hx).fderiv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_inv, abs_of_nonneg (sq_nonneg _), innerSL_apply_norm, norm_normalize hx]
  calc
    _ ≤ ‖x‖⁻¹ * 1 + (‖x‖ ^ 2)⁻¹ * 1 * ‖x‖ :=
      add_le_add (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (inv_nonneg.mpr hr.le)) le_rfl
    _ = 2 / ‖x‖ := by field_simp; ring

/-- Differentiable radial and angular factors give a differentiable field away from zero. -/
theorem differentiableAt_radial_smul_normalize {f : ℝ → ℝ} {H : E → F} {x : E}
    (hx : x ≠ 0) (hf : DifferentiableAt ℝ f ‖x‖)
    (hH : DifferentiableAt ℝ H (normalize x)) :
    DifferentiableAt ℝ (fun y ↦ f ‖y‖ • H (normalize y)) x :=
  (hf.comp x (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx).differentiableAt).smul
    (hH.comp x (hasFDerivAt_normalize hx).differentiableAt)

/-- The derivative bound for a radial factor times an angular field keeps both
the radial and angular contributions explicit. -/
theorem norm_fderiv_radial_smul_normalize_le {f : ℝ → ℝ} {H : E → F} {x : E}
    (hx : x ≠ 0) (hf : DifferentiableAt ℝ f ‖x‖)
    (hH : DifferentiableAt ℝ H (normalize x)) :
    ‖fderiv ℝ (fun y ↦ f ‖y‖ • H (normalize y)) x‖ ≤
      |f ‖x‖| * ‖fderiv ℝ H (normalize x)‖ * (2 / ‖x‖) +
        |deriv f ‖x‖| * ‖H (normalize x)‖ := by
  have hn := EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx
  have hc := hf.hasDerivAt.comp_hasFDerivAt x hn
  have hnorm := hasFDerivAt_normalize hx
  have ha := hH.hasFDerivAt.comp x hnorm
  have hscalar : ‖(deriv f ‖x‖) • innerSL ℝ (normalize x)‖ ≤ |deriv f ‖x‖| := by
    rw [norm_smul, Real.norm_eq_abs, innerSL_apply_norm, norm_normalize hx, mul_one]
  have hangular : ‖(fderiv ℝ H (normalize x)).comp (fderiv ℝ NormedSpace.normalize x)‖ ≤
      ‖fderiv ℝ H (normalize x)‖ * (2 / ‖x‖) := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_fderiv_normalize_le hx) (norm_nonneg _))
  have hd := hc.smul ha
  change HasFDerivAt (fun y ↦ f ‖y‖ • H (normalize y)) _ x at hd
  rw [hd.fderiv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
  rw [hnorm.fderiv] at hangular
  calc
    _ ≤ |f ‖x‖| * (‖fderiv ℝ H (normalize x)‖ * (2 / ‖x‖)) +
        |deriv f ‖x‖| * ‖H (normalize x)‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hangular (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hscalar (norm_nonneg _))
    _ = _ := by ring

end PDE.Analysis.Radial
