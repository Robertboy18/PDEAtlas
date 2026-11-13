/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.EuclideanBall.Dilation

/-!
# Spherical trace estimates for wave sources

Applying the ball divergence theorem to `u² (x-c)` bounds the surface square
integral by the interior square integrals of `u` and its derivative.
The radius factors are retained for estimates of retarded wave formulas.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Analysis Metric Set
open scoped RealInnerProductSpace

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} [Fact (0 < n)]

/-- A radius-explicit trace inequality obtained directly from Gauss's formula.
The function need only be C¹. -/
theorem mul_sphereIntegral_sq_le
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u) (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    r * sphereIntegral n (fun y ↦ u y ^ 2) c r ≤ (n + 1 : ℝ) * ballIntegral n (fun y ↦ u y ^ 2) c
      r + r ^ 2 * ballIntegral n (fun y ↦ ‖fderiv ℝ u y‖ ^ 2) c r := by
  have hpoint (y : ℝ^n) (hy : y ∈ ball c r) : 2 * (u y * fderiv ℝ u y (y - c)) ≤
        u y ^ 2 + r ^ 2 * ‖fderiv ℝ u y‖ ^ 2 := by
    have hn : ‖y - c‖ ≤ r :=
      le_of_lt (by simpa only [mem_ball, dist_eq_norm] using hy)
    have hd : |fderiv ℝ u y (y - c)| ≤ r * ‖fderiv ℝ u y‖ := by
      calc
        _ ≤ ‖fderiv ℝ u y‖ * ‖y - c‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ u y‖ * r := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
        _ = _ := mul_comm _ _
    have hp : u y * fderiv ℝ u y (y - c) ≤ |u y| * (r * ‖fderiv ℝ u y‖) :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    nlinarith [sq_nonneg (|u y| - r * ‖fderiv ℝ u y‖), sq_abs (u y)]
  have hint {v : ℝ^n → ℝ} (hv : Continuous v) : IntegrableOn v (ball c r) :=
    (hv.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  have hiu : IntegrableOn (fun y ↦ u y ^ 2) (ball c r) := by
    apply hint
    fun_prop
  have hiD : IntegrableOn (fun y ↦ ‖fderiv ℝ u y‖ ^ 2) (ball c r) := by
    apply hint
    exact (hu.continuous_fderiv one_ne_zero).norm.fun_pow 2
  have him : IntegrableOn (fun y ↦ u y * fderiv ℝ u y (y - c)) (ball c r) := hint (hu.continuous.mul
      ((hu.continuous_fderiv one_ne_zero).clm_apply (continuous_id.sub continuous_const)))
  have hb := integral_mono_ae (him.const_mul 2) (hiu.add (hiD.const_mul (r ^ 2)))
    ((ae_restrict_mem measurableSet_ball).mono hpoint)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add hiu (hiD.const_mul _), integral_const_mul] at hb
  rw [← ballIntegral_dilation_sq hu c hr]
  change (n : ℝ) * (∫ y in ball c r, u y ^ 2) +
    2 * (∫ y in ball c r, u y * fderiv ℝ u y (y - c)) ≤ _
  change _ ≤ (n + 1 : ℝ) * (∫ y in ball c r, u y ^ 2) +
    r ^ 2 * (∫ y in ball c r, ‖fderiv ℝ u y‖ ^ 2)
  linarith

end PDE.Hyperbolic.NonlinearWave.Cauchy
