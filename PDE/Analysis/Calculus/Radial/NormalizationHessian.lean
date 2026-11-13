/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.AngularDerivative
public import PDE.Analysis.Calculus.LocalExtension.Cutoff.Hessian
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Second derivative bounds for radius and normalization

The radius has Hessian bounded by `2/r`. Its inverse has Hessian bounded by
`4/r³`, and normalization has Hessian bounded by `6/r²`. These estimates retain
the singular radial denominators needed to control normalized angular fields.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

open NormedSpace Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radius derivative has unit operator norm off zero. -/
theorem norm_fderiv_norm_eq_one {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (norm : E → ℝ) x‖ = 1 := by
  rw [(EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx).fderiv,
    innerSL_apply_norm]
  exact norm_normalize hx

/-- The radius Hessian is controlled by the normalization derivative. -/
theorem norm_fderiv_fderiv_norm_le {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fderiv ℝ (norm : E → ℝ)) x‖ ≤ 2 / ‖x‖ := by
  have hnear : fderiv ℝ (norm : E → ℝ) =ᶠ[𝓝 x]
      fun y ↦ innerSL ℝ (NormedSpace.normalize y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hy).fderiv
  have hd := (innerSL ℝ (E := E)).hasFDerivAt.comp x (hasFDerivAt_normalize hx)
  change HasFDerivAt (fun y ↦ innerSL ℝ (NormedSpace.normalize y)) _ x at hd
  rw [hnear.fderiv_eq, hd.fderiv, ← (hasFDerivAt_normalize hx).fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_innerSL_le ℝ) (norm_fderiv_normalize_le hx)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

/-- The derivative of inverse radius has norm exactly `1/r²`. -/
theorem norm_fderiv_inv_norm {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E ↦ ‖y‖⁻¹) x‖ = 1 / ‖x‖ ^ 2 := by
  have hd := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x
    (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx)
  change HasFDerivAt (fun y : E ↦ ‖y‖⁻¹) _ x at hd
  rw [hd.fderiv, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv,
    abs_of_nonneg (sq_nonneg _), innerSL_apply_norm]
  change (‖x‖ ^ 2)⁻¹ * ‖NormedSpace.normalize x‖ = _
  rw [norm_normalize hx, mul_one, one_div]

/-- The inverse-square scalar derivative retains its full inverse-cubic coefficient. -/
theorem hasFDerivAt_neg_inv_norm_sq {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ -(‖y‖ ^ 2)⁻¹)
      ((2 / ‖x‖ ^ 3) • innerSL ℝ (NormedSpace.normalize x)) x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hpow : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * ‖x‖) ‖x‖ := by
    simpa using hasDerivAt_pow 2 ‖x‖
  have hs : HasDerivAt (fun t : ℝ ↦ -(t ^ 2)⁻¹)
      (2 * ‖x‖ / (‖x‖ ^ 2) ^ 2) ‖x‖ := by
    have hs0 : HasDerivAt (fun t : ℝ ↦ -(t ^ 2)⁻¹)
        (-(-(2 * ‖x‖) / (‖x‖ ^ 2) ^ 2)) ‖x‖ :=
      HasDerivAt.neg (HasDerivAt.inv hpow (pow_ne_zero 2 hr))
    simpa only [neg_div, neg_neg] using hs0
  have hd := hs.comp_hasFDerivAt x (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx)
  change HasFDerivAt (fun y : E ↦ -(‖y‖ ^ 2)⁻¹)
    ((2 * ‖x‖ / (‖x‖ ^ 2) ^ 2) • innerSL ℝ (NormedSpace.normalize x)) x at hd
  convert hd using 1
  congr 1
  field_simp

/-- The inverse radius has an inverse-cubic Hessian bound. -/
theorem norm_fderiv_fderiv_inv_norm_le {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fderiv ℝ (fun y : E ↦ ‖y‖⁻¹)) x‖ ≤ 4 / ‖x‖ ^ 3 := by
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnear : fderiv ℝ (fun y : E ↦ ‖y‖⁻¹) =ᶠ[𝓝 x]
      fun y ↦ -(‖y‖ ^ 2)⁻¹ • innerSL ℝ (NormedSpace.normalize y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact ((hasDerivAt_inv (norm_ne_zero_iff.mpr hy)).comp_hasFDerivAt y
      (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hy)).fderiv
  have hQ := (innerSL ℝ (E := E)).hasFDerivAt.comp x (hasFDerivAt_normalize hx)
  have hχ := hasFDerivAt_neg_inv_norm_sq hx
  have hd := hχ.smul hQ
  change HasFDerivAt (fun y ↦ -(‖y‖ ^ 2)⁻¹ • innerSL ℝ (NormedSpace.normalize y)) _ x at hd
  have hDQ : ‖(innerSL ℝ (E := E)).comp
      (fderiv ℝ (NormedSpace.normalize : E → E) x)‖ ≤ 2 / ‖x‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_innerSL_le ℝ) (norm_fderiv_normalize_le hx)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  rw [hnear.fderiv_eq, hd.fderiv]
  refine (norm_add_le (E := E →L[ℝ] E →L[ℝ] ℝ) _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_of_nonneg (sq_nonneg _),
    ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 / ‖x‖ ^ 3)]
  change (‖x‖ ^ 2)⁻¹ * ‖(innerSL ℝ (E := E)).comp _‖ +
      (2 / ‖x‖ ^ 3 * ‖innerSL ℝ (NormedSpace.normalize x)‖) *
        ‖innerSL ℝ (NormedSpace.normalize x)‖ ≤ _
  rw [innerSL_apply_norm, norm_normalize hx, mul_one, mul_one,
    ← (hasFDerivAt_normalize hx).fderiv]
  calc
    _ ≤ (‖x‖ ^ 2)⁻¹ * (2 / ‖x‖) + 2 / ‖x‖ ^ 3 :=
      add_le_add (mul_le_mul_of_nonneg_left hDQ (by positivity)) le_rfl
    _ = 4 / ‖x‖ ^ 3 := by field_simp; ring

/-- The full normalization Hessian has inverse-square operator norm. -/
theorem norm_fderiv_fderiv_normalize_le {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fderiv ℝ (NormedSpace.normalize : E → E)) x‖ ≤ 6 / ‖x‖ ^ 2 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hχ : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖⁻¹) x :=
    (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)
  have hbound := norm_fderiv_fderiv_smul_sub_le hχ (contDiffAt_id : ContDiffAt ℝ 2 id x)
  have hid : fderiv ℝ (id : E → E) = fun _ ↦ ContinuousLinearMap.id ℝ E := by
    funext y
    exact (hasFDerivAt_id y).fderiv
  simp only [hid, fderiv_fun_const, Pi.zero_apply, smul_zero, sub_zero, id_eq] at hbound
  change ‖fderiv ℝ (fderiv ℝ (NormedSpace.normalize : E → E)) x‖ ≤ _ at hbound
  refine hbound.trans ?_
  rw [norm_fderiv_inv_norm hx]
  calc
    _ ≤ 2 * (1 / ‖x‖ ^ 2) * 1 + ‖x‖ * (4 / ‖x‖ ^ 3) :=
      add_le_add (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity))
        (mul_le_mul_of_nonneg_left (norm_fderiv_fderiv_inv_norm_le hx) (norm_nonneg _))
    _ = _ := by field_simp; ring

end PDE.Analysis.Radial
