/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.AngularDerivative

/-!
# Euler derivatives of normalized angular fields

The derivative of normalization annihilates the radial direction. Thus the
Euler derivative of a radial factor times a normalized angular field acts only
on the radial factor, independently of the angular field's variation.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

open NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The norm derivative evaluated in the radial direction equals the radius. -/
theorem inner_normalize_self {x : E} (hx : x ≠ 0) :
    inner ℝ (normalize x) x = ‖x‖ := by
  rw [NormedSpace.normalize, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hx]

/-- Normalization has zero derivative in the radial direction. -/
theorem fderiv_normalize_apply_self {x : E} (hx : x ≠ 0) :
    fderiv ℝ (normalize : E → E) x x = 0 := by
  rw [(hasFDerivAt_normalize hx).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_normalize_self hx, smul_eq_mul]
  rw [← add_smul]
  have hc : ‖x‖⁻¹ + -(‖x‖ ^ 2)⁻¹ * ‖x‖ = 0 := by
    field_simp [norm_ne_zero_iff.mpr hx]
    ring
  rw [hc, zero_smul]

/-- The Euler derivative of a radial-angular product differentiates only the radial factor. -/
theorem fderiv_radial_smul_normalize_apply_self {f : ℝ → ℝ} {H : E → F} {x : E}
    (hf : DifferentiableAt ℝ f ‖x‖)
    (hH : DifferentiableAt ℝ H (normalize x)) :
    fderiv ℝ (fun y ↦ f ‖y‖ • H (normalize y)) x x =
      (‖x‖ * deriv f ‖x‖) • H (normalize x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn := EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx
  have hc := hf.hasDerivAt.comp_hasFDerivAt x hn
  have ha := hH.hasFDerivAt.comp x (hasFDerivAt_normalize hx)
  have hd := hc.smul ha
  change HasFDerivAt (fun y ↦ f ‖y‖ • H (normalize y)) _ x at hd
  rw [hd.fderiv]
  change f ‖x‖ • ((fderiv ℝ H (normalize x))
      ((‖x‖⁻¹ • ContinuousLinearMap.id ℝ E +
        ((-(‖x‖ ^ 2)⁻¹) • innerSL ℝ (normalize x)).smulRight x) x)) +
    (deriv f ‖x‖ * inner ℝ (normalize x) x) • H (normalize x) = _
  rw [← (hasFDerivAt_normalize hx).fderiv, fderiv_normalize_apply_self hx, map_zero,
    smul_zero, zero_add,
    inner_normalize_self hx, mul_comm]

end PDE.Analysis.Radial
