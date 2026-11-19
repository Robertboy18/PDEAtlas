/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Localization.Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Integrability of scalar asymptotic errors

Measurability is obtained at each fixed positive time from the
derivative formula; a joint almost-everywhere statement alone would not
suffice. The derived propagation cone and pointwise decay then imply
slice integrability for an essentially bounded datum with bounded support.

These results make the integrand `|u - N|` of the estimate (67) of Evans, §3.4.5(b), Theorem 6,
integrable at every `t > 0`; the bound on `u` is the decay (57) of Theorem 5.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.5(a), Theorem 5, equation (57); §3.4.5(b),
  equation (63) and Theorem 6, equation (67).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- Every fixed positive-time slice of the selected-footpoint solution is
strongly measurable almost everywhere. The selection need not be measurable. -/
theorem aestronglyMeasurable_solution_slice {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) {t : ℝ} (ht : 0 < t) :
    AEStronglyMeasurable (fun x : ℝ ↦ solution F g !₂[t, x]) volume :=
  (aestronglyMeasurable_deriv _ volume).congr (Filter.EventuallyEq.symm
      (solution_ae_eq_deriv_value_of_deriv2_lower_bound hF hθ hlower hg ht))

/-- The solution slice is integrable at every positive time, under
essential boundedness and almost-everywhere bounded support of the datum.
Neither initial `L¹` membership nor slice integrability is an input. -/
theorem integrable_solution_slice_of_ae_support_Icc {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    {R : ℝ} (hsupport : ∀ᵐ y ∂volume, y ∉ Icc (-R) R → g y = 0) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ ↦ solution F g !₂[t, x]) volume := by
  have hg1 : Integrable g volume := by
    have hgi : IntegrableOn g (Icc (-R) R) volume :=
      (hg.locallyIntegrable le_top).integrableOn_isCompact isCompact_Icc
    exact hgi.integrable_of_ae_notMem_eq_zero hsupport
  obtain ⟨c, _, hcone⟩ := exists_solution_eq_zero_of_abs_gt hF hθ hlower hzero hg hg1 hsupport
  let A := √(2 * (∫ y, |g y|) / θ) / √t
  have hbound (x : ℝ) : |solution F g !₂[t, x]| ≤ A :=
    abs_solution_le_sqrt_div_sqrt hF hθ hlower hzero hg hg1 ht x
  have hdom : Integrable ((Icc (-(R + c * t)) (R + c * t)).indicator (fun _ : ℝ ↦ A)) volume :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  apply hdom.mono' (aestronglyMeasurable_solution_slice hF hθ hlower hg ht)
  refine Filter.Eventually.of_forall fun x ↦ ?_
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ Icc (-(R + c * t)) (R + c * t)
  · rw [indicator_of_mem hx]
    exact hbound x
  · rw [indicator_of_notMem hx]
    have hxabs : R + c * t < |x| := by
      by_contra h
      exact hx (abs_le.mp (le_of_not_gt h))
    rw [hcone t ht x hxabs, abs_zero]

/-- The error relative to the N-wave is an integrable function at
each positive time; its real integral is therefore nonvacuous. -/
theorem integrable_abs_solution_sub_nWave_of_ae_support_Icc {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {θ : ℝ} (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0)
    (hg : MemLp g ∞ volume) {R : ℝ} (hsupport : ∀ᵐ y ∂volume, y ∉ Icc (-R) R → g y = 0) {t : ℝ}
    (ht : 0 < t) :
    Integrable (fun x : ℝ ↦ |solution F g !₂[t, x] - nWave F g t x|) volume :=
  ((integrable_solution_slice_of_ae_support_Icc hF hθ hlower hzero hg hsupport ht).sub
    (integrable_nWave F g t)).abs

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
