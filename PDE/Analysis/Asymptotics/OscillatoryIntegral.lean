/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Oscillatory integrals (`1/ω` cancellation)

Integrals against a fast linear phase `exp(i ω t)` gain a factor `1/|ω|`: the
antiderivative of the phase is `exp(i ω t) / (i ω)`, so a pure oscillation
integrates to something of size at most `2/|ω|`, and one integration by parts
transfers the gain to `∫ exp(i ω t) • f(t) dt` at the cost of a derivative of
`f`.  This is the model case (linear phase, `k = 1`) of van der Corput's
lemma, here with explicit constants and for vector-valued `f`. It is also the case `n = 1`,
`m = 1` of Lemma 1 of Evans, §4.5.3(b), on an interval and with the boundary terms kept;
Evans integrates by parts `m` times against a compactly supported amplitude.

## Main results

* `osc`: the phase `t ↦ exp(i ω t)`, with `osc_mul`, `conj_osc`,
  `norm_osc_eq_one` and `hasDerivAt_osc`.
* `norm_intervalIntegral_osc_le`: `‖∫_a^b exp(i ω t) dt‖ ≤ 2 / |ω|` for
  `ω ≠ 0`.
* `norm_intervalIntegral_osc_smul_le_of_hasDerivAt`: if `‖f‖ ≤ M` and
  `‖f'‖ ≤ M'` on `[a, b]`, then
  `‖∫_a^b exp(i ω t) • f(t) dt‖ ≤ (2 M + |b - a| M') / |ω|`.

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Princeton Mathematical Series 43, Princeton University Press, 1993, Chapter VIII,
  Oscillatory Integrals of the First Kind, pp. 329-374. <https://doi.org/10.1515/9781400883929>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemma 1, p. 221.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE
namespace Analysis

open scoped ComplexConjugate Interval
open MeasureTheory intervalIntegral
open Complex

noncomputable section

/-- The basic oscillatory scalar `t ↦ exp(i ω t)` (as a complex number). -/
def osc (ω t : ℝ) : ℂ :=
  Complex.exp ((ω * t) * Complex.I)

/-- The zero-frequency oscillatory phase is the constant function `1`. -/
@[simp]
theorem osc_zero (t : ℝ) : osc 0 t = 1 := by
  simp [osc]

/-!
## Basic algebraic identities
-/

/-- Multiplying two oscillatory phases at the same time adds their frequencies. -/
theorem osc_mul (ω₁ ω₂ t : ℝ) : osc ω₁ t * osc ω₂ t = osc (ω₁ + ω₂) t := by
  rw [osc, osc, osc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Complex conjugation reverses the frequency of an oscillatory phase. -/
@[simp]
theorem conj_osc (ω t : ℝ) : conj (osc ω t) = osc (-ω) t := by
  -- `conj (exp z) = exp (conj z)` and `conj I = -I`.
  have h := (Complex.exp_conj (x := ((ω * t) * Complex.I : ℂ))).symm
  simpa [osc, Complex.conj_I, mul_assoc, mul_comm, mul_left_comm] using h

/-- Every real-frequency oscillatory phase has complex norm one. -/
theorem norm_osc_eq_one (ω t : ℝ) : ‖osc ω t‖ = 1 := by
  -- `‖exp(i x)‖ = 1`.
  simpa [osc, mul_assoc, mul_left_comm, mul_comm] using (Complex.norm_exp_ofReal_mul_I (ω * t))

/-!
## Differentiation of the basic oscillation
-/

/-- Differentiating `t ↦ exp(i ω t)` produces the expected factor `i ω exp(i ω t)`. -/
theorem hasDerivAt_osc (ω t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ osc ω s) ((ω : ℂ) * Complex.I * osc ω t) t := by
  simpa [osc, mul_assoc, mul_left_comm, mul_comm] using
    (((ofRealCLM.hasDerivAt (x := t)).const_mul (ω : ℂ)).mul_const I).cexp

/-- The oscillatory phase at a fixed frequency is continuous in time. -/
theorem continuous_osc (ω : ℝ) : Continuous (fun t : ℝ ↦ osc ω t) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_osc ω t).continuousAt

/-!
## Oscillatory integral bound

For `ω ≠ 0`, the interval integral of `exp(i ω t)` has size bounded by `2 / |ω|`.
-/

/-- A pure oscillation averages out with size `O(1/|ω|)` on any interval. -/
theorem norm_intervalIntegral_osc_le (ω a b : ℝ) (hω : ω ≠ 0) :
    ‖∫ t in a..b, osc ω t‖ ≤ 2 / |ω| := by
  have hωc : (ω : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hω) I_ne_zero
  have hint : (∫ t in a..b, osc ω t) =
      (Complex.exp ((ω : ℂ) * I * b) - Complex.exp ((ω : ℂ) * I * a)) / ((ω : ℂ) * I) := by
    simpa [osc, mul_assoc, mul_left_comm, mul_comm] using
      integral_exp_mul_complex (a := a) (b := b) hωc
  have hn (s : ℝ) : ‖Complex.exp ((ω : ℂ) * I * s)‖ = 1 := by
    rw [show (ω : ℂ) * I * s = ((ω * s : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  rw [hint, norm_div, show ‖(ω : ℂ) * I‖ = |ω| by simp]
  gcongr
  exact (norm_sub_le _ _).trans (by rw [hn, hn]; norm_num)

/-!
## Oscillatory integration-by-parts estimate (`1/ω` cancellation)

If `f` varies slowly (bounded derivative), then `∫ exp(i ω t) • f(t) dt` is still `O(1/|ω|)`.
-/

/-- If `f` is bounded and slowly varying, then the oscillatory integral
`∫ exp(i ω t) • f(t) dt` gains a `1/|ω|` factor with explicit constants. -/
theorem norm_intervalIntegral_osc_smul_le_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {f f' : ℝ → E} (ω a b : ℝ) (hω : ω ≠ 0)
    (hderiv : ∀ t ∈ [[a, b]], HasDerivAt f (f' t) t)
    (hf' : IntervalIntegrable f' MeasureTheory.volume a b)
    (M M' : ℝ)
    (hM : ∀ t ∈ [[a, b]], ‖f t‖ ≤ M)
    (hM' : ∀ t ∈ [[a, b]], ‖f' t‖ ≤ M') :
    ‖∫ t in a..b, (osc ω t) • f t‖ ≤ (2 * M + |b - a| * M') / |ω| := by
  -- The antiderivative `u = (ωI)⁻¹ osc ω` of the phase moves the derivative onto `f`.
  have hωc : (ω : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hω) I_ne_zero
  let u : ℝ → ℂ := fun t ↦ ((ω : ℂ) * I)⁻¹ * osc ω t
  have hu_deriv (t : ℝ) (_ : t ∈ [[a, b]]) : HasDerivAt u (osc ω t) t := by
    convert (hasDerivAt_osc ω t).const_mul ((ω : ℂ) * I)⁻¹ using 1
    rw [← mul_assoc, inv_mul_cancel₀ hωc, one_mul]
  have hu (t : ℝ) : ‖u t‖ ≤ 1 / |ω| := by
    simp [u, norm_osc_eq_one]
  have hrew : (∫ t in a..b, osc ω t • f t) =
      (u b • f b - u a • f a) - ∫ t in a..b, u t • f' t := by
    rw [integral_smul_deriv_eq_deriv_smul hu_deriv hderiv
      ((continuous_osc ω).intervalIntegrable a b) hf', sub_sub_cancel]
  have hsmul {g : ℝ → E} {C t : ℝ} (hg : ‖g t‖ ≤ C) : ‖u t • g t‖ ≤ 1 / |ω| * C := by
    rw [norm_smul]
    exact mul_le_mul (hu t) hg (norm_nonneg _) (by positivity)
  have hint : ‖∫ t in a..b, u t • f' t‖ ≤ 1 / |ω| * M' * |b - a| :=
    norm_integral_le_of_norm_le_const fun t ht ↦ hsmul (hM' t (Set.uIoc_subset_uIcc ht))
  rw [hrew]
  calc _ ≤ ‖u b • f b‖ + ‖u a • f a‖ + ‖∫ t in a..b, u t • f' t‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ 1 / |ω| * M + 1 / |ω| * M + 1 / |ω| * M' * |b - a| := by
        gcongr
        exacts [hsmul (hM b Set.right_mem_uIcc), hsmul (hM a Set.left_mem_uIcc)]
    _ = (2 * M + |b - a| * M') / |ω| := by ring

end

end Analysis
end PDE
