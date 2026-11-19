/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.MeasureTheory.Measure.Haar.Unique
public import PDE.Parabolic.Heat.InitialValue
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import PDE.Parabolic.Heat.Kernel.Integrability
import PDE.Parabolic.Heat.Kernel.SpatialDerivatives
import PDE.Parabolic.Heat.Kernel.TimeDerivative
import CAS.ExactTactic

/-!
# Time differentiation of heat-kernel convolutions

For bounded continuous data `g` and `t > 0`, the heat-kernel convolution
`∫ Γ(x - y, s) g(y) dy` is differentiable in `s` at `t`, with derivative obtained by
differentiating the kernel under the integral. A Gaussian majorant, uniform for
`t/2 < s < 3t/2`, justifies the dominated differentiation. The main results are
`hasDerivAt_heatKernel_convolution_time` and `hasDerivAt_initialValueSolution_time`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(b), Theorem 1 (Solution of initial-value problem) and
  step 1 of its proof, p. 47.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

private theorem abs_heat_time_derivative_coefficient_le
    (r t s : ℝ) (ht : 0 < t) (hs_lower : t / 2 < s) :
    |r ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)| ≤
      r ^ 2 / t ^ 2 + (n : ℝ) / t := by
  have hs_pos : 0 < s := by linarith
  exact (abs_sub _ _).trans (add_le_add
    ((abs_of_nonneg (by positivity)).trans_le
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)))
    ((abs_of_nonneg (by positivity)).trans_le
      (div_le_div_of_nonneg_left (Nat.cast_nonneg n) ht (by linarith))))

private theorem fundamentalSolutionHeat_le_time_gaussian
    (z : ℝ^n) (t s : ℝ) (ht : 0 < t)
    (hs_lower : t / 2 < s) (hs_upper : s < 3 * t / 2) :
    fundamentalSolutionHeat (n := n) z s ≤
      (4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2) *
        Real.exp (-(‖z‖ ^ 2 / (6 * t))) := by
  have hs_pos : 0 < s := by linarith
  rw [fundamentalSolutionHeat, ite_eq_right (not_le.mpr hs_pos)]
  gcongr ?_ * Real.exp ?_
  · exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_left hs_lower.le (by positivity))
      (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
  · exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith))

private theorem heat_time_polynomial_mul_gaussian_le
    (r t : ℝ) (ht : 0 < t) :
    (r ^ 2 / t ^ 2 + (n : ℝ) / t) * Real.exp (-(r ^ 2 / (6 * t))) ≤
      ((12 + (n : ℝ)) / t) * Real.exp (-(r ^ 2 / (12 * t))) := by
  set u : ℝ := r ^ 2 / (12 * t) with hu_def
  have hu : 0 ≤ u := by rw [hu_def]; positivity
  have hfast : Real.exp (-(r ^ 2 / (6 * t))) = Real.exp (-(2 * u)) := by
    rw [hu_def]
    cas
  have hr : r ^ 2 / t ^ 2 = 12 / t * u := by
    rw [hu_def]
    field_simp
  have hu_exp : u * Real.exp (-(2 * u)) ≤ Real.exp (-u) :=
    calc u * Real.exp (-(2 * u)) ≤ Real.exp u * Real.exp (-(2 * u)) := by
          gcongr
          linarith [Real.add_one_le_exp u]
      _ = Real.exp (-u) := by rw [← Real.exp_add]; ring_nf
  have hexp_mono : Real.exp (-(2 * u)) ≤ Real.exp (-u) := by gcongr; linarith
  rw [hr, hfast]
  calc _ = 12 / t * (u * Real.exp (-(2 * u))) + (n : ℝ) / t * Real.exp (-(2 * u)) := by ring
    _ ≤ 12 / t * Real.exp (-u) + (n : ℝ) / t * Real.exp (-u) := by gcongr
    _ = _ := by ring

private theorem norm_heatKernel_time_derivative_integrand_le
    (z : ℝ^n) (a B t s : ℝ) (ht : 0 < t)
    (hs_lower : t / 2 < s) (hs_upper : s < 3 * t / 2) (ha : |a| ≤ B) :
    ‖((‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) *
          fundamentalSolutionHeat (n := n) z s) * a‖ ≤
      (B * (4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2) *
          ((12 + (n : ℝ)) / t)) *
        Real.exp (-(‖z‖ ^ 2 / (12 * t))) := by
  have hK := (fundamentalSolutionHeat_pos (n := n) z s (by linarith)).le
  have hB : 0 ≤ B := (abs_nonneg a).trans ha
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hK]
  calc _ ≤ (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) *
        ((4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (6 * t)))) * B := by
        gcongr
        exacts [abs_heat_time_derivative_coefficient_le ‖z‖ t s ht hs_lower,
          fundamentalSolutionHeat_le_time_gaussian z t s ht hs_lower hs_upper]
    _ = B * (4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2) *
        ((‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) * Real.exp (-(‖z‖ ^ 2 / (6 * t)))) := by ring
    _ ≤ B * (4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2) *
        ((12 + (n : ℝ)) / t * Real.exp (-(‖z‖ ^ 2 / (12 * t)))) :=
      mul_le_mul_of_nonneg_left (heat_time_polynomial_mul_gaussian_le ‖z‖ t ht) (by positivity)
    _ = _ := by ring

/-- For bounded continuous data, the time derivative of the heat-kernel convolution at `t > 0`
is the convolution of `g` with `∂ₜΓ`. Step 1 of Evans's proof of §2.3.1(b), Theorem 1 takes
this derivative under the integral, using the bounded derivatives of the kernel on
`ℝⁿ × [δ, ∞)`. -/
theorem hasDerivAt_heatKernel_convolution_time
    (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ) (ht : 0 < t)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    HasDerivAt
        (fun s ↦
          ∫ y : ℝ^n, fundamentalSolutionHeat (n := n) (x - y) s * g y)
        (∫ y : ℝ^n,
          ((‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) *
              fundamentalSolutionHeat (n := n) (x - y) t) *
            g y)
        t := by
  obtain ⟨M, hM⟩ := hg_bdd
  have hΓc (s : ℝ) (hs : 0 < s) :
      Continuous fun y : ℝ^n ↦ fundamentalSolutionHeat (n := n) (x - y) s :=
    continuous_iff_continuousAt.2 fun y ↦
      (differentiableAt_fundamentalSolutionHeat s hs (x - y)).continuousAt.comp
        (continuous_const.sub continuous_id).continuousAt
  have hball {s : ℝ} (hs : s ∈ Metric.ball t (t / 2)) : t / 2 < s ∧ s < 3 * t / 2 := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    constructor <;> linarith [hs.1, hs.2]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y ↦ fundamentalSolutionHeat (n := n) (x - y) s * g y)
    (F' := fun s y ↦ ((‖x - y‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) *
      fundamentalSolutionHeat (n := n) (x - y) s) * g y)
    (bound := fun y ↦ |M| * (4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2) * ((12 + (n : ℝ)) / t) *
      Real.exp (-(‖x - y‖ ^ 2 / (12 * t))))
    (Metric.ball_mem_nhds t (half_pos ht)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [eventually_gt_nhds ht] with s hs
    exact ((hΓc s hs).mul hg_cont).aestronglyMeasurable
  · exact ((MeasureTheory.Measure.measurePreserving_sub_left _ x).integrable_comp_of_integrable
      (fundamentalSolutionHeat_integrable t ht)).mul_bdd hg_cont.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ fun y ↦ (Real.norm_eq_abs _).trans_le (hM y))
  · exact (((by fun_prop : Continuous fun y : ℝ^n ↦
      ‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)).mul (hΓc t ht)).mul
        hg_cont).aestronglyMeasurable
  · exact MeasureTheory.ae_of_all _ fun y s hs ↦ norm_heatKernel_time_derivative_integrand_le
      (x - y) (g y) |M| t s ht (hball hs).1 (hball hs).2 ((hM y).trans (le_abs_self M))
  · exact ((integrable_exp_neg_mul_sq_norm_sub_left x (1 / (12 * t)) (by positivity)).const_mul
      (|M| * (4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2) * ((12 + (n : ℝ)) / t))).congr
      (MeasureTheory.ae_of_all _ fun y ↦ by ring_nf)
  · refine MeasureTheory.ae_of_all _ fun y s hs ↦ ?_
    have hs0 : 0 < s := by linarith [(hball hs).1]
    have := (differentiableAt_fundamentalSolutionHeat_time (x - y) s hs0).hasDerivAt.mul_const
      (g y)
    rwa [fundamentalSolutionHeat_deriv_t _ s hs0] at this

/-- The time derivative of `initialValueSolution g x` at `t > 0`.

`initialValueSolution` returns the datum for `t ≤ 0`, but near any `t > 0` it equals the
heat-kernel convolution, so `hasDerivAt_heatKernel_convolution_time` applies. -/
theorem hasDerivAt_initialValueSolution_time
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (ht : 0 < t)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    HasDerivAt (fun s ↦ initialValueSolution (n := n) g x s)
      (∫ y : ℝ^n,
        ((‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) *
            fundamentalSolutionHeat (n := n) (x - y) t) * g y) t := by
  let conv : ℝ → ℝ := fun s ↦
    ∫ y : ℝ^n,
      fundamentalSolutionHeat (n := n) (x - y) s * g y
  have hconv := hasDerivAt_heatKernel_convolution_time
    (n := n) g x t ht hg_cont hg_bdd
  have heq : (fun s ↦ initialValueSolution (n := n) g x s) =ᶠ[nhds t] conv := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    simp [initialValueSolution, conv, not_le_of_gt hs]
  exact hconv.congr_of_eventuallyEq heq

end HeatEquation
