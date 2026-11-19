/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.MeasureTheory.Measure.Haar.Unique

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Parabolic.Heat.Kernel.Basic
import PDE.Parabolic.Heat.Kernel.Integrability

/-!
# Heat-kernel evolution of initial data

`initialValueSolution g x t` is the convolution `∫ Γ(x - y, t) g(y) dy` for `t > 0`, Evans's formula
(9) in §2.3.1(b). For `t ≤ 0` it is defined to be `g x`, so the function is total. We prove that
constants are preserved, by the unit mass of the kernel (the Lemma of Evans's §2.3.1(a)), and that
`|g| ≤ M` implies `|initialValueSolution g x t| ≤ M`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(a), Lemma (Integral of fundamental solution), p. 46;
  §2.3.1(b), (9), p. 47; §2.3.3(a), Theorem 6 (Maximum principle for the Cauchy problem), pp. 57-58.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-- Heat-kernel convolution formula for initial data `g`.

For `t ≤ 0` the value is `g x`. Derivatives at positive time are computed in
`ConvolutionSpace/SpatialDerivatives.lean` and `ConvolutionTime.lean`, and convergence to the
datum as `t ↓ 0` is `initialValueSolution_locally_uniform_initial_trace`. -/
noncomputable def initialValueSolution (g : ℝ^n → ℝ)
    (x : ℝ^n) (t : ℝ) : ℝ :=
  if t ≤ 0 then g x else
  ∫ y : ℝ^n, fundamentalSolutionHeat (x - y) t * g y

/-- For `t ≤ 0`, `initialValueSolution g x t = g x` by definition. -/
theorem initialValueSolution_of_t_le_zero (g : ℝ^n → ℝ)
    (x : ℝ^n) {t : ℝ} (ht : t ≤ 0) :
    initialValueSolution (n := n) g x t = g x := by
  simp [initialValueSolution, ht]

/-- At `t = 0`, `initialValueSolution g x 0 = g x` by definition. -/
theorem initialValueSolution_of_t_eq_zero (g : ℝ^n → ℝ)
    (x : ℝ^n) :
    initialValueSolution (n := n) g x 0 = g x :=
  initialValueSolution_of_t_le_zero (n := n) g x (le_rfl : (0 : ℝ) ≤ 0)

/-- On the spacetime slice `{t = 0}`, the heat-kernel formula takes the value of the datum.
This comes from the `t ≤ 0` branch of the definition; the limit from positive time is
`initialValueSolution_locally_uniform_initial_trace`. -/
theorem initialValueSolution_timeZero_value (g : ℝ^n → ℝ)
    (xt : ℝ^(n + 1)) (ht : xt 0 = 0) :
    (fun xt ↦ initialValueSolution (n := n) g (spatialPartCLM n xt) (xt 0)) xt =
      g (spatialPartCLM n xt) := by
  simp [initialValueSolution, ht]

/-- Constant initial data is preserved by the heat-kernel convolution. -/
theorem initialValueSolution_const (c : ℝ) (x : ℝ^n) (t : ℝ) :
    initialValueSolution (n := n) (fun _ : ℝ^n ↦ c) x t = c := by
  classical
  by_cases ht : t ≤ 0
  · simp [initialValueSolution, ht]
  · have ht_pos : 0 < t := lt_of_not_ge ht
    let μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ^n))
    let Γ : (ℝ^n) → ℝ := fun z ↦ fundamentalSolutionHeat (n := n) z t
    let Γx : (ℝ^n) → ℝ := fun y ↦ Γ (x - y)
    have hΓ_integral : (∫ z : (ℝ^n), Γ z ∂μ) = 1 := by
      simpa [Γ, μ] using fundamentalSolutionHeat_integral (n := n) t ht_pos
    have hΓx_integral : (∫ y : (ℝ^n), Γx y ∂μ) = 1 := by
      calc
        (∫ y : (ℝ^n), Γx y ∂μ) = ∫ z : (ℝ^n), Γ z ∂μ := by
          simpa [Γx, μ] using
            (MeasureTheory.integral_sub_left_eq_self (μ := μ) (fun z : (ℝ^n) ↦ Γ z) x)
        _ = 1 := hΓ_integral
    have hinit :
        initialValueSolution (n := n) (fun _ : ℝ^n ↦ c) x t =
          ∫ y : (ℝ^n), Γx y * c ∂μ := by
      simp [initialValueSolution, ht, Γx, Γ, μ]
    calc
      initialValueSolution (n := n) (fun _ : ℝ^n ↦ c) x t =
          ∫ y : (ℝ^n), Γx y * c ∂μ := hinit
      _ = c := by
        simpa [μ, hΓx_integral] using
          (MeasureTheory.integral_mul_const (μ := μ) (r := c) (f := fun y : (ℝ^n) ↦ Γx y))

/-- The heat-kernel evolution preserves uniform bounds.

If the continuous initial datum satisfies `|g| ≤ M`, then its heat evolution
satisfies the same pointwise bound at every time; taking the optimal `M`, this
is the `L∞` contraction property of the heat semigroup. For `t ≤ 0` this is the bound
on `g` itself. For `t > 0`, positivity of the Gaussian
kernel, its unit mass, and the Bochner integral triangle inequality give

`|Γ_t * g| ≤ Γ_t * |g| ≤ M Γ_t * 1 = M`.

Evans obtains the same bound for solutions with the growth bound (24) from his §2.3.3(a),
Theorem 6 (Maximum principle for the Cauchy problem), applied to `u` and `-u`. Continuity of
`g` is used only for measurability. -/
theorem abs_initialValueSolution_le
    (g : ℝ^n → ℝ)
    {M : ℝ} (hg_cont : Continuous g)
    (hg_bound : ∀ y, |g y| ≤ M)
    (x : ℝ^n) (t : ℝ) :
    |initialValueSolution (n := n) g x t| ≤ M := by
  classical
  by_cases ht : t ≤ 0
  · simpa [initialValueSolution, ht] using hg_bound x
  · have ht_pos : 0 < t := lt_of_not_ge ht
    let μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ^n))
    let Γ : (ℝ^n) → ℝ := fun z ↦ fundamentalSolutionHeat (n := n) z t
    let Γx : (ℝ^n) → ℝ := fun y ↦ Γ (x - y)
    let f : (ℝ^n) → ℝ := fun y ↦ Γx y * g y
    have hΓ_integrable : MeasureTheory.Integrable Γ (μ := μ) := by
      simpa [Γ, μ] using
        fundamentalSolutionHeat_integrable (n := n) t ht_pos
    have hΓx_integrable : MeasureTheory.Integrable Γx (μ := μ) := by
      simpa [Γx, μ] using hΓ_integrable.comp_sub_left x
    have hΓx_integral : (∫ y : (ℝ^n), Γx y ∂μ) = 1 := by
      calc
        (∫ y : (ℝ^n), Γx y ∂μ) = ∫ z : (ℝ^n), Γ z ∂μ := by
          simpa [Γx, μ] using
            (MeasureTheory.integral_sub_left_eq_self
              (μ := μ) (fun z : (ℝ^n) ↦ Γ z) x)
        _ = 1 := by
          simpa [Γ, μ] using
            fundamentalSolutionHeat_integral (n := n) t ht_pos
    have hf_meas : MeasureTheory.AEStronglyMeasurable f (μ := μ) := by
      exact hΓx_integrable.aestronglyMeasurable.mul
        hg_cont.aestronglyMeasurable
    have hmajorant : MeasureTheory.Integrable
        (fun y : (ℝ^n) ↦ M * Γx y) (μ := μ) :=
      hΓx_integrable.const_mul M
    have hf_bound : ∀ᵐ y ∂μ, ‖f y‖ ≤ M * Γx y := by
      refine Filter.Eventually.of_forall fun y ↦ ?_
      have hΓ_nonneg : 0 ≤ Γx y :=
        le_of_lt (fundamentalSolutionHeat_pos (n := n) (x - y) t ht_pos)
      calc
        ‖f y‖ = Γx y * |g y| := by
          simp [f, Real.norm_eq_abs, abs_of_nonneg hΓ_nonneg]
        _ ≤ Γx y * M :=
          mul_le_mul_of_nonneg_left (hg_bound y) hΓ_nonneg
        _ = M * Γx y := mul_comm _ _
    have hf_integrable : MeasureTheory.Integrable f (μ := μ) :=
      MeasureTheory.Integrable.mono' hmajorant hf_meas hf_bound
    have hintegral_bound :
        (∫ y : (ℝ^n), ‖f y‖ ∂μ) ≤ ∫ y : (ℝ^n), M * Γx y ∂μ :=
      MeasureTheory.integral_mono_ae hf_integrable.norm hmajorant hf_bound
    calc
      |initialValueSolution (n := n) g x t| =
          ‖∫ y : (ℝ^n), f y ∂μ‖ := by
        simp [initialValueSolution, ht, f, Γx, Γ, μ, Real.norm_eq_abs]
      _ ≤ ∫ y : (ℝ^n), ‖f y‖ ∂μ :=
        MeasureTheory.norm_integral_le_integral_norm f
      _ ≤ ∫ y : (ℝ^n), M * Γx y ∂μ := hintegral_bound
      _ = M := by
        rw [MeasureTheory.integral_const_mul, hΓx_integral, mul_one]

end HeatEquation
