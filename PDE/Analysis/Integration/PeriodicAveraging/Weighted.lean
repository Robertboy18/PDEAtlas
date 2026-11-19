/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Primitive
import CAS.ExactTactic

/-!
# Periodic averaging against a differentiable weight

Integration by parts moves the oscillation onto its bounded primitive. On the unit
interval this gives an explicit error bound for a weight and its derivative bounded
by the same constant.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.PeriodicAveraging

open MeasureTheory Set intervalIntegral
open scoped Interval

/-- Weighted periodic averaging, with the error controlled by the primitive bound. -/
theorem abs_weighted_rescale_sub_le {q F f : ℝ → ℝ} {K M ε x : ℝ}
    (hq : Continuous q) (hF : ∀ y, HasDerivAt F (f y) y) (hf : Continuous f)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hb : ∀ y, |fluctuation q y| ≤ K)
    (hFM : ∀ y ∈ Icc (0 : ℝ) 1, |F y| ≤ M)
    (hfM : ∀ y ∈ Icc (0 : ℝ) 1, |f y| ≤ M)
    (hε : ε ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    |(∫ y in (0 : ℝ)..x, F y * q (y / ε)) - mean q * primitive F x| ≤
      2 * M * (|ε| * K) := by
  let R (y : ℝ) := primitive (fun z ↦ q (z / ε)) y - mean q * y
  have hqε : Continuous (fun y ↦ q (y / ε)) := hq.comp (continuous_id.div_const ε)
  have hFc : Continuous F :=
    (show Differentiable ℝ F from fun y ↦ (hF y).differentiableAt).continuous
  have hR (y : ℝ) : HasDerivAt R (q (y / ε) - mean q) y := by
    convert (hasDerivAt_primitive hqε y).fun_sub
      ((hasDerivAt_id y).const_mul (mean q)) using 1 <;> simp [R]
  have hRc : Continuous R :=
    (show Differentiable ℝ R from fun y ↦ (hR y).differentiableAt).continuous
  have hRb (y : ℝ) : |R y| ≤ |ε| * K := abs_primitive_rescale_sub_le hb hε y
  have hR0 : R 0 = 0 := by simp [R]
  have hi := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := x) hFc.continuousOn hRc.continuousOn
    (fun y _ ↦ hF y) (fun y _ ↦ hR y)
    (hf.intervalIntegrable 0 x) ((hqε.sub continuous_const).intervalIntegrable 0 x)
  have heq : (∫ y in (0 : ℝ)..x, F y * q (y / ε)) - mean q * primitive F x =
      F x * R x - ∫ y in (0 : ℝ)..x, f y * R y := by
    rw [hR0, mul_zero, sub_zero] at hi
    rw [← hi]
    simp_rw [mul_sub]
    rw [integral_sub (f := fun y ↦ F y * q (y / ε)) (g := fun y ↦ F y * mean q)
      ((hFc.mul hqε).intervalIntegrable 0 x)
      ((hFc.mul continuous_const).intervalIntegrable 0 x), intervalIntegral.integral_mul_const]
    simp only [primitive, mul_comm (mean q)]
  have hinterval : ∀ y ∈ Ι (0 : ℝ) x, y ∈ Icc (0 : ℝ) 1 := by
    intro y hy
    have hy' : y ∈ Icc (0 : ℝ) x := by
      simpa only [uIcc_of_le hx.1] using uIoc_subset_uIcc hy
    exact ⟨hy'.1, hy'.2.trans hx.2⟩
  have hi_bound : |∫ y in (0 : ℝ)..x, f y * R y| ≤ M * (|ε| * K) := by
    have hn := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := x)
      (C := M * (|ε| * K)) (f := fun y ↦ f y * R y) (fun y hy ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hfM y (hinterval y hy)) (hRb y) (abs_nonneg _) hM)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx.1] at hn
    exact hn.trans (mul_le_of_le_one_right (mul_nonneg hM (mul_nonneg (abs_nonneg _) hK)) hx.2)
  rw [heq]
  calc
    |F x * R x - ∫ y in (0 : ℝ)..x, f y * R y| ≤
        |F x * R x| + |∫ y in (0 : ℝ)..x, f y * R y| := abs_sub _ _
    _ ≤ M * (|ε| * K) + M * (|ε| * K) := by
      apply add_le_add _ hi_bound
      rw [abs_mul]
      exact mul_le_mul (hFM x hx) (hRb x) (abs_nonneg _) hM
    _ = 2 * M * (|ε| * K) := by cas

end PDE.Analysis.PeriodicAveraging
