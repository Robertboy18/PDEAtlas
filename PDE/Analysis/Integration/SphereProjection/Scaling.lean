/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.SphereProjection.Integral

/-!
# Projection onto balls of arbitrary radius

Translation and scaling give the square-root kernel on an arbitrary ball.
Its finite, positive mass supplies integrability for every continuous numerator,
without a condition at the boundary of the ball.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Pointwise

namespace PDE.Analysis

variable {n : ℕ}

/-- The affine change of variables from the unit ball has Jacobian `r^n`. -/
theorem integral_ball_affine (f : ℝ^n → ℝ) (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    (∫ y in Metric.ball x r, f y) =
      r ^ n * ∫ y in Metric.ball (0 : ℝ^n) 1, f (x + r • y) := by
  have h := Measure.setIntegral_comp_smul_of_pos volume (fun y : ℝ^n ↦ f (x + y))
    (Metric.ball 0 1) hr
  have ht := ballIntegral_comp_add_left f x r
  simp only [ballIntegral] at ht
  simp only [finrank_euclideanSpace_fin, smul_ball hr.ne', smul_zero, Real.norm_eq_abs,
    abs_of_pos hr, mul_one, smul_eq_mul, ht] at h
  rw [h]
  field_simp

variable [Fact (0 < n)]

/-- Scaling the square-root kernel removes one power of the radius. -/
theorem integral_ball_sqrt_scale (f : ℝ^n → ℝ) (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    (∫ y in Metric.ball x r, f y / √(r ^ 2 - ‖y - x‖ ^ 2)) =
      r ^ (n - 1) * ∫ y in Metric.ball (0 : ℝ^n) 1,
        f (x + r • y) / √(1 - ‖y‖ ^ 2) := by
  rw [integral_ball_affine _ x hr]
  have he (y : ℝ^n) :
      f (x + r • y) / √(r ^ 2 - ‖x + r • y - x‖ ^ 2) =
        r⁻¹ * (f (x + r • y) / √(1 - ‖y‖ ^ 2)) := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      show r ^ 2 - (r * ‖y‖) ^ 2 = r ^ 2 * (1 - ‖y‖ ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
    field_simp
  simp_rw [he]
  rw [integral_const_mul, ← mul_assoc,
    show r ^ n * r⁻¹ = r ^ (n - 1) by
      rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt (Fact.out : 0 < n)), pow_succ]
      simp [hr.ne']]

/-- Projection of a sphere integral onto its central ball has density
`2r / √(r² - ‖y-x‖²)`. -/
theorem sphereIntegral_coordinateProjection {f : ℝ^n → ℝ} (hf : Continuous f)
    (z : ℝ^(n + 1)) {r : ℝ} (hr : 0 < r) :
    sphereIntegral (n + 1) (f ∘ coordinateProjection) z r =
      2 * r * ∫ y in Metric.ball (coordinateProjection z) r,
        f y / √(r ^ 2 - ‖y - coordinateProjection z‖ ^ 2) := by
  rw [integral_ball_sqrt_scale _ _ hr]
  have hc : Continuous (fun y : ℝ^n ↦ f (coordinateProjection z + r • y)) :=
    hf.comp (by fun_prop)
  have h := integral_sphere_eq_ball_weight hc
  simp only [sphereIntegral, Nat.add_sub_cancel, abs_of_pos hr, Function.comp_apply,
    map_add, map_smul]
  have hpow : r ^ (n - 1) * r = r ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt (Fact.out : 0 < n))]
  rw [h, ← hpow]
  ring

/-- The square-root kernel has mass equal to half the ambient unit-sphere
area, times `r^(n-1)`. -/
theorem integral_ball_sqrt_kernel (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    (∫ y in Metric.ball x r, 1 / √(r ^ 2 - ‖y - x‖ ^ 2)) =
      r ^ (n - 1) * (unitSphereArea (n + 1) / 2) := by
  rw [integral_ball_sqrt_scale _ x hr]
  have h := integral_sphere_eq_ball_weight (f := fun _ : ℝ^n ↦ (1 : ℝ)) continuous_const
  simp only [integral_const, smul_eq_mul, mul_one] at h
  change unitSphereArea (n + 1) = _ at h
  congr 1
  linarith

/-- A continuous numerator is integrable against the ball's singular square-root kernel. -/
theorem integrableOn_ball_sqrt_weight {f : ℝ^n → ℝ} (hf : Continuous f)
    (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y ↦ f y / √(r ^ 2 - ‖y - x‖ ^ 2)) (Metric.ball x r) := by
  have hk : IntegrableOn (fun y ↦ 1 / √(r ^ 2 - ‖y - x‖ ^ 2))
      (Metric.ball x r) :=
    Integrable.of_integral_ne_zero (by
      rw [integral_ball_sqrt_kernel x hr]
      exact (mul_pos (pow_pos hr _) (div_pos unitSphereArea_pos (by norm_num))).ne')
  obtain ⟨C, hC⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ᵐ y ∂volume.restrict (Metric.ball x r), ‖f y‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hC y (Metric.ball_subset_closedBall hy)
  simpa only [IntegrableOn, mul_one_div] using
    hk.bdd_mul hf.measurable.aestronglyMeasurable hb

end PDE.Analysis
