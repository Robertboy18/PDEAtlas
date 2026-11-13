/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.NormalizationHessian
public import PDE.Analysis.Calculus.LocalExtension.Logarithmic.Pullback

/-!
# Hessian bounds for radial factors with normalized angular fields

The full second derivative estimate keeps the value, first radial derivative,
and second radial derivative separate. It retains `1/r` and `1/r²` factors
from angular differentiation, so both local singularities and far-field decay
can be estimated from the actual radial mode.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

open NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a real scalar function, the full Hessian norm is the absolute second derivative. -/
theorem norm_fderiv_fderiv_real (f : ℝ → ℝ) (r : ℝ) :
    ‖fderiv ℝ (fderiv ℝ f) r‖ = |deriv (deriv f) r| := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs]

/-- The first derivative norm of a radial scalar factor is its radial derivative magnitude. -/
theorem norm_fderiv_comp_norm {f : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f ‖x‖) :
    ‖fderiv ℝ (fun y ↦ f ‖y‖) x‖ = |deriv f ‖x‖| := by
  have hd := hf.hasDerivAt.comp_hasFDerivAt x
    (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx)
  change HasFDerivAt (fun y ↦ f ‖y‖) _ x at hd
  rw [hd.fderiv, norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
  change |deriv f ‖x‖| * ‖NormedSpace.normalize x‖ = _
  rw [norm_normalize hx, mul_one]

/-- The radial scalar Hessian is bounded by the second radial derivative and a curvature term. -/
theorem norm_fderiv_fderiv_comp_norm_le {f : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ f ‖y‖)) x‖ ≤
      |deriv (deriv f) ‖x‖| + |deriv f ‖x‖| * (2 / ‖x‖) := by
  have hbound := norm_fderiv_fderiv_comp_le hf (contDiffAt_norm ℝ hx)
  change ‖fderiv ℝ (fderiv ℝ (fun y ↦ f ‖y‖)) x‖ ≤ _ at hbound
  rw [norm_fderiv_fderiv_real, norm_fderiv_norm_eq_one hx,
    one_pow, mul_one, ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] at hbound
  exact hbound.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (norm_fderiv_fderiv_norm_le hx) (abs_nonneg _)))

/-- The angular composition has its first derivative bounded by the inverse radius. -/
theorem norm_fderiv_comp_normalize_le {H : E → F} {x : E} (hx : x ≠ 0)
    (hH : DifferentiableAt ℝ H (NormedSpace.normalize x)) :
    ‖fderiv ℝ (fun y ↦ H (NormedSpace.normalize y)) x‖ ≤
      ‖fderiv ℝ H (NormedSpace.normalize x)‖ * (2 / ‖x‖) := by
  have hd := hH.hasFDerivAt.comp x (hasFDerivAt_normalize hx)
  change HasFDerivAt (fun y ↦ H (NormedSpace.normalize y)) _ x at hd
  rw [hd.fderiv, ← (hasFDerivAt_normalize hx).fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_fderiv_normalize_le hx) (norm_nonneg _))

/-- The angular composition has its full Hessian bounded by the inverse-square radius. -/
theorem norm_fderiv_fderiv_comp_normalize_le {H : E → F} {x : E} (hx : x ≠ 0)
    (hH : ContDiffAt ℝ 2 H (NormedSpace.normalize x)) :
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ H (NormedSpace.normalize y))) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ H) (NormedSpace.normalize x)‖ * (2 / ‖x‖) ^ 2 +
        ‖fderiv ℝ H (NormedSpace.normalize x)‖ * (6 / ‖x‖ ^ 2) := by
  have hn : ContDiffAt ℝ 2 (NormedSpace.normalize : E → E) x :=
    ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
  have hbound := norm_fderiv_fderiv_comp_le hH hn
  change ‖fderiv ℝ (fderiv ℝ (fun y ↦ H (NormedSpace.normalize y))) x‖ ≤ _ at hbound
  exact hbound.trans (add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (norm_fderiv_normalize_le hx) 2)
      (fderiv ℝ (fderiv ℝ H) (NormedSpace.normalize x)).opNorm_nonneg)
    (mul_le_mul_of_nonneg_left (norm_fderiv_fderiv_normalize_le hx) (norm_nonneg _)))

/-- The Hessian of a radial-angular field retains all three radial contributions. -/
theorem norm_fderiv_fderiv_radial_smul_normalize_le {f : ℝ → ℝ} {H : E → F} {x : E}
    (hx : x ≠ 0) (hf : ContDiffAt ℝ 2 f ‖x‖)
    (hH : ContDiffAt ℝ 2 H (NormedSpace.normalize x)) :
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ f ‖y‖ • H (NormedSpace.normalize y))) x‖ ≤
      |f ‖x‖| * (‖fderiv ℝ (fderiv ℝ H) (NormedSpace.normalize x)‖ * (2 / ‖x‖) ^ 2 +
        ‖fderiv ℝ H (NormedSpace.normalize x)‖ * (6 / ‖x‖ ^ 2)) +
      2 * |deriv f ‖x‖| * (‖fderiv ℝ H (NormedSpace.normalize x)‖ * (2 / ‖x‖)) +
      ‖H (NormedSpace.normalize x)‖ *
        (|deriv (deriv f) ‖x‖| + |deriv f ‖x‖| * (2 / ‖x‖)) := by
  let : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
  let A := fderiv ℝ (fderiv ℝ (fun y ↦ f ‖y‖ • H (NormedSpace.normalize y))) x
  let B := f ‖x‖ • fderiv ℝ (fderiv ℝ (fun y ↦ H (NormedSpace.normalize y))) x
  have hn : ContDiffAt ℝ 2 (NormedSpace.normalize : E → E) x :=
    ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
  have hprod := norm_fderiv_fderiv_smul_sub_le (hf.comp x (contDiffAt_norm ℝ hx))
    (hH.comp x hn)
  change ‖A - B‖ ≤
    2 * ‖fderiv ℝ (fun y ↦ f ‖y‖) x‖ *
      ‖fderiv ℝ (fun y ↦ H (NormedSpace.normalize y)) x‖ +
    ‖H (NormedSpace.normalize x)‖ *
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ f ‖y‖)) x‖ at hprod
  have hangular := norm_fderiv_fderiv_comp_normalize_le hx hH
  have hradial := norm_fderiv_fderiv_comp_norm_le hx hf
  have hfirst := norm_fderiv_comp_normalize_le hx (hH.differentiableAt two_ne_zero)
  rw [norm_fderiv_comp_norm hx (hf.differentiableAt two_ne_zero)] at hprod
  calc
    ‖A‖ ≤ ‖B‖ + ‖A - B‖ := norm_le_insert' A B
    _ ≤ |f ‖x‖| *
        (‖fderiv ℝ (fderiv ℝ H) (NormedSpace.normalize x)‖ * (2 / ‖x‖) ^ 2 +
          ‖fderiv ℝ H (NormedSpace.normalize x)‖ * (6 / ‖x‖ ^ 2)) +
        (2 * |deriv f ‖x‖| * (‖fderiv ℝ H (NormedSpace.normalize x)‖ * (2 / ‖x‖)) +
          ‖H (NormedSpace.normalize x)‖ *
            (|deriv (deriv f) ‖x‖| + |deriv f ‖x‖| * (2 / ‖x‖))) := by
      apply add_le_add
      · dsimp [B]
        exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
          (by simpa only [Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left hangular (norm_nonneg (f ‖x‖)))
      · exact hprod.trans (add_le_add
          (mul_le_mul_of_nonneg_left hfirst (by positivity))
          (mul_le_mul_of_nonneg_left hradial (norm_nonneg _)))
    _ = _ := by ring

end PDE.Analysis.Radial
