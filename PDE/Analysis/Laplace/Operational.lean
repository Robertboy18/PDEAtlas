/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Laplace.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The initial term in Laplace operational calculus

Integration of the derivative of `exp(-s*t) * f(t)` gives the one-sided
transform rule, including the initial value. The endpoint and convergence
hypotheses are stated explicitly; no decay is inferred from differentiability alone.
The rule is the integration by parts `∫₀^∞ e^{-st} v_t dt = s v^# - f` in Evans, §4.3.3,
Example 8, which turns the heat equation (44) into the resolvent equation (45).

## Main results

* `transform_derivative`: `L[f'](s) = s L[f](s) - f(0)` for complex `s`, when `f` is
  continuous from the right at `0` with derivative `f'` on `(0, ∞)`, `e^{-st} f` and
  `e^{-st} f'` are integrable on `(0, ∞)`, and `e^{-st} f(t) → 0` as `t → ∞`.
* `transform_deriv_of_hasCompactSupport`: the same rule for compactly supported `C¹`
  functions, without further hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.3, Example 8 (Resolvents and Laplace transform),
  (44) and (45), p. 203. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex Filter
open scoped Topology

namespace PDE.Analysis.Laplace

/-- The Laplace transform of a derivative, with the initial value and the weighted
boundary condition at infinity. This applies to complex frequencies. -/
theorem transform_derivative {f f' : ℝ → ℂ} (s : ℂ)
    (hf : ContinuousWithinAt f (Ici 0) 0)
    (hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hi : IntegrableOn (fun t : ℝ ↦ exp (-s * t) * f t) (Ioi 0))
    (hi' : IntegrableOn (fun t : ℝ ↦ exp (-s * t) * f' t) (Ioi 0))
    (hlim : Tendsto (fun t : ℝ ↦ exp (-s * t) * f t) atTop (𝓝 0)) :
    transform f' s = s * transform f s - f 0 := by
  have hweight (t : ℝ) : HasDerivAt (fun y : ℝ ↦ exp (-s * y))
      (exp (-s * t) * (-s)) t := by
    simpa using (((hasDerivAt_id t).ofReal_comp).const_mul (-s)).cexp
  have hproduct (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun y : ℝ ↦ exp (-s * y) * f y)
        (exp (-s * t) * f' t - s * (exp (-s * t) * f t)) t := by
    convert (hweight t).mul (hd t ht) using 1
    ring
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hweight 0).continuousAt.continuousWithinAt.mul hf) hproduct
    (hi'.sub (hi.const_mul s)) hlim
  rw [integral_sub hi' (hi.const_mul s), integral_const_mul] at hFTC
  simp only [Pi.mul_apply, ofReal_zero, mul_zero, exp_zero, one_mul, zero_sub] at hFTC
  simp only [transform, smul_eq_mul]
  linear_combination hFTC

/-- Compactly supported continuously differentiable functions satisfy the transform
rule on every vertical line, without separate integrability assumptions. -/
theorem transform_deriv_of_hasCompactSupport {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (s : ℂ) :
    transform (deriv f) s = s * transform f s - f 0 := by
  have hw : Continuous (fun t : ℝ ↦ exp (-s * t)) := by fun_prop
  apply transform_derivative s hf.continuous.continuousWithinAt
    (fun t _ ↦ (hf.differentiable one_ne_zero t).hasDerivAt)
  · exact (hw.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
      |>.integrableOn
  · exact (hw.mul (hf.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hc.deriv.mul_left |>.integrableOn
  · have he : (fun t : ℝ ↦ exp (-s * t) * f t) =ᶠ[cocompact ℝ] 0 :=
      (hasCompactSupport_iff_eventuallyEq.mp hc.mul_left).filter_mono
        (by rw [coclosedCompact_eq_cocompact])
    exact (he.filter_mono atTop_le_cocompact).tendsto

end PDE.Analysis.Laplace
