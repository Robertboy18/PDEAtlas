/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convolution
public import PDE.Analysis.Integration.EuclideanBall

/-!
# Radial averaging from spherical means

If all spherical averages about a point equal its value, integration against any radial weight
in an admissible ball gives that value times the mass of the weight. The weight may change sign;
only the two integrability assumptions are needed. A normalized radial kernel therefore fixes
the function at that point.

For Weyl regularity this identity is applied to smooth harmonic mollifications.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace PDE.Analysis

/-- A radial factor is constant on each sphere, including the degenerate radius zero. -/
theorem sphereIntegral_radial_mul {n : ℕ}
    (w : ℝ → ℝ) (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) :
    sphereIntegral n (fun y ↦ w (dist y x) * u y) x r =
      w |r| * sphereIntegral n u x r := by
  have hdist (ω : Metric.sphere (0 : ℝ^n) 1) :
      dist (x + r • (ω : ℝ^n)) x = |r| := by
    have hω : ‖(ω : ℝ^n)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
    simp [dist_eq_norm, norm_smul, hω]
  unfold sphereIntegral
  simp_rw [hdist, integral_const_mul]
  ring

/-- Spherical mean values determine every integrable radial weighted average on a ball.

Only the mean values about `x` are required. Neither continuity of `u` nor positivity or
smoothness of the radial weight is assumed. -/
theorem integral_radial_mul_eq_of_sphereAverage_eq {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {w : ℝ → ℝ} {x : ℝ^n} {r : ℝ}
    (hmean : ∀ s, 0 < s → s ≤ r → u x = sphereAverage n u x s)
    (hw : IntegrableOn (fun y ↦ w (dist y x)) (Metric.ball x r))
    (hwu : IntegrableOn (fun y ↦ w (dist y x) * u y) (Metric.ball x r)) :
    (∫ y in Metric.ball x r, w (dist y x) * u y) =
      u x * ∫ y in Metric.ball x r, w (dist y x) := by
  have hsphere (s : ℝ) (hs : s ∈ Icc 0 r) :
      sphereIntegral n (fun y ↦ w (dist y x) * u y) x s =
        u x * sphereIntegral n (fun y ↦ w (dist y x)) x s := by
    by_cases hs0 : s = 0
    · subst s
      simp [sphereIntegral, mul_assoc, mul_comm, mul_left_comm]
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hu_sphere : sphereIntegral n u x s = u x * sphereArea n s := by
      have hm : u x = sphereIntegral n u x s / sphereArea n s := by
        simpa only [sphereAverage, ite_eq_left hspos] using hmean s hspos hs.2
      exact ((eq_div_iff (sphereArea_ne_zero s hspos)).mp hm).symm
    have hw_sphere :
        sphereIntegral n (fun y ↦ w (dist y x)) x s =
          w s * sphereArea n s := by
      simpa only [mul_one, one_mul, abs_of_pos hspos, sphereIntegral_const] using
        sphereIntegral_radial_mul w (fun _ : ℝ^n ↦ 1) x s
    rw [sphereIntegral_radial_mul, abs_of_pos hspos, hu_sphere, hw_sphere]
    ring
  change ballIntegral n (fun y ↦ w (dist y x) * u y) x r =
    u x * ballIntegral n (fun y ↦ w (dist y x)) x r
  rw [coarea_formula_ball _ _ _ hwu, coarea_formula_ball _ _ _ hw,
    ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Icc hsphere

/-- A normalized radial kernel fixes a function at a point with the spherical mean-value
property. Integrability of the weighted function is needed only inside the kernel's ball. -/
theorem convolution_radial_eq_of_sphereAverage_eq {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {w : ℝ → ℝ} {x : ℝ^n} {r : ℝ}
    (hmean : ∀ s, 0 < s → s ≤ r → u x = sphereAverage n u x s)
    (hzero : ∀ s, r ≤ s → w s = 0)
    (hw : Integrable (fun y : ℝ^n ↦ w ‖y‖))
    (hwu : IntegrableOn (fun y ↦ w (dist y x) * u y) (Metric.ball x r))
    (hmass : (∫ y : ℝ^n, w ‖y‖) = 1) :
    ((fun y : ℝ^n ↦ w ‖y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] u) x = u x := by
  have hwcenter : Integrable (fun y : ℝ^n ↦ w (dist y x)) := by
    simpa only [dist_eq_norm] using hw.comp_sub_right x
  have hout (y : ℝ^n) (hy : y ∉ Metric.ball x r) : w (dist y x) = 0 :=
    hzero _ (not_lt.mp hy)
  have hmasscenter : (∫ y : ℝ^n, w (dist y x)) = 1 := by
    simpa only [dist_eq_norm] using
      (integral_sub_right_eq_self (fun y : ℝ^n ↦ w ‖y‖) x).trans hmass
  calc
    ((fun y : ℝ^n ↦ w ‖y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] u) x =
        ∫ y, w (dist y x) * u y := by
      rw [convolution_mul_swap]
      simp only [dist_eq_norm, norm_sub_rev]
    _ = ∫ y in Metric.ball x r, w (dist y x) * u y := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
        rw [hout y hy, zero_mul]
    _ = u x * ∫ y in Metric.ball x r, w (dist y x) :=
      integral_radial_mul_eq_of_sphereAverage_eq hmean hwcenter.integrableOn hwu
    _ = u x * ∫ y, w (dist y x) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    _ = u x := by rw [hmasscenter, mul_one]

end PDE.Analysis
