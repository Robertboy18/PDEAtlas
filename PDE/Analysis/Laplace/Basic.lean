/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The one-sided complex Laplace transform

The transform integrates over positive times. On a vertical line it is the Fourier
transform of the exponentially damped causal extension. Frequencies use Mathlib's
`2 * π` normalization: the vertical line is parametrized by `a + 2 * π * ξ * I`.
For real `s ≥ 0` and `f ∈ L¹(0, ∞)`, `transform f s` is the Laplace transform `f^#(s)` of
Evans, §4.3.3, (43); here `s` is complex and `f` takes values in a complex normed space.

## Main definitions

* `transform f s`: the integral of `exp (-s t) • f t` over `t > 0`.
* `dampedExtension f a`: `exp (-a t) • f t` for `t > 0`, extended by zero.

## Main results

* `transform_vertical_eq_fourier`: `transform f (a + 2πξ i)` is the Fourier transform of
  `dampedExtension f a` at `ξ`.
* `transform_eq_integral`: for causal `f` the half-line integral is a whole-line integral.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.3, the definition (43), p. 203.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex
open scoped FourierTransform

namespace PDE.Analysis.Laplace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The one-sided Laplace transform, interpreted as a Bochner integral. Convergence
hypotheses are supplied by theorems using the transform. -/
def transform (f : ℝ → E) (s : ℂ) : E :=
  ∫ t in Ioi (0 : ℝ), exp (-s * t) • f t

/-- Exponential damping followed by extension by zero to nonpositive times. -/
def dampedExtension (f : ℝ → E) (a : ℝ) : ℝ → E :=
  (Ioi 0).indicator (fun t ↦ exp (-(a : ℂ) * t) • f t)

/-- A vertical Laplace trace is the Fourier transform of the damped causal extension. -/
theorem transform_vertical_eq_fourier (f : ℝ → E) (a ξ : ℝ) :
    transform f ((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I) =
      𝓕 (dampedExtension f a) ξ := by
  rw [Real.fourier_eq', transform, dampedExtension]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : 0 < t
  · simp only [indicator, mem_Ioi, ht, ↓reduceIte, smul_smul]
    rw [← exp_add]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial, ofReal_mul, ofReal_neg, ofReal_ofNat]
    ring
  · simp only [indicator, mem_Ioi, ht, ↓reduceIte, smul_zero]

/-- For causal data the extension does not change the damped function. -/
theorem dampedExtension_eq {f : ℝ → E} (hf : ∀ t ≤ 0, f t = 0) (a : ℝ) :
    dampedExtension f a = fun t : ℝ ↦ exp (-(a : ℂ) * t) • f t := by
  funext t
  by_cases ht : 0 < t
  · simp [dampedExtension, ht]
  · simp [dampedExtension, ht, hf t (le_of_not_gt ht)]

/-- Causal data permit replacing the half-line integral by the whole-line integral. -/
theorem transform_eq_integral {f : ℝ → E} (hf : ∀ t ≤ 0, f t = 0) (s : ℂ) :
    transform f s = ∫ t : ℝ, exp (-s * t) • f t := by
  rw [transform, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    by_cases ht : 0 < t
    · simp [ht]
    · simp [ht, hf t (le_of_not_gt ht)]

end PDE.Analysis.Laplace
