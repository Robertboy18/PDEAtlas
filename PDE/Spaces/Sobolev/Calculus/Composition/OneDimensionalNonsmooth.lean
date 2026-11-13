/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Truncation
public import PDE.Spaces.Sobolev.Calculus.Slicing.AbsolutelyContinuousRepresentative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import PDE.Analysis.Calculus.AbsoluteValue

/-!
# Nonsmooth calculus for one-dimensional Sobolev representatives

We apply the scalar almost-everywhere chain rules for absolute value,
positive and negative parts, and interval truncation to the selected
absolutely continuous representative of a global `W^{1,1}(ℝ)` class.

Each transformed representative remains absolutely continuous on compact
intervals, has the expected almost-everywhere derivative, and satisfies the
literal fundamental theorem of calculus.

The inputs are the selected representative `representative U` of a `W^{1,1}(ℝ)` class, which is
absolutely continuous on every compact interval and differentiable a.e. with derivative
`weakDerivativeRepresentative U`, and the scalar a.e. chain rules of `PDE.Analysis.Calculus` for
`|·|`, `(·)⁺`, `(·)⁻` and the clamp `T_[a,b]`. Composition with a Lipschitz map preserves absolute
continuity (Mathlib's `LipschitzWith.comp_absolutelyContinuousOnInterval`), so the fundamental
theorem of calculus for Lebesgue integrals, `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`,
applies to each transformed representative.

The a.e. derivative formulas are stated with sign coefficients: `sign(u) u'`
for `|u|`, `((1 + sign u)/2) u'` for `u⁺`, and
`((sign(u - a) - sign(u - b))/2) u'` for `T_[a,b](u)`. On the level sets
`{u = 0}`, `{u = a}`, `{u = b}` the coefficient is zero, matching the fact
that `u' = 0` a.e. there.

## Main results

* `absRepresentative`, `positivePartRepresentative`, `negativePartRepresentative`,
  `truncationRepresentative`: the transformed representatives.
* `absolutelyContinuousOnInterval_*`: each is absolutely continuous on every compact interval.
* `ae_hasDerivAt_*`: each is differentiable a.e. with the derivative named
  `*WeakDerivativeRepresentative`.
* `intervalIntegral_*WeakDerivativeRepresentative_eq_sub`: the fundamental theorem of
  calculus `∫_c^d f' = f d - f c` for each transformed representative.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  for absolutely continuous functions and the fundamental theorem of calculus for Lebesgue
  integrals.
  <https://www.wiley.com/en-us/Real+Analysis%3A+Modern+Techniques+and+Their+Applications%2C+2nd+Edition-p-9780471317166>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 7, Sobolev Spaces, pp. 144-176, for the
  higher-dimensional form of these chain rules.
  <https://doi.org/10.1007/978-3-642-61798-0>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

namespace OneDimensionalNonsmooth

open AbsolutelyContinuousRepresentative

/-- Absolute value of the selected one-dimensional Sobolev representative. -/
def absRepresentative (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦ |representative U t|

/-- The almost-everywhere derivative of `absRepresentative`. -/
def absWeakDerivativeRepresentative
    (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦
    (SignType.sign (representative U t) : ℝ) *
      weakDerivativeRepresentative U t

/-- Absolute value preserves interval absolute continuity of the selected
representative. -/
theorem absolutelyContinuousOnInterval_absRepresentative
    (U : W^{1,1}(ℝ^1)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (absRepresentative U) a b := by
  have h :=
    (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).comp_absolutelyContinuousOnInterval
      (absolutelyContinuousOnInterval_representative U a b)
  apply h.congr
  intro x _hx
  simp [absRepresentative, Real.norm_eq_abs]

/-- The derivative of the absolute-value representative agrees almost
everywhere with `sign(u) u'`. -/
theorem ae_hasDerivAt_absRepresentative
    (U : W^{1,1}(ℝ^1)) :
    ∀ᵐ x ∂volume,
      HasDerivAt (absRepresentative U)
        (absWeakDerivativeRepresentative U x) x := by
  change ∀ᵐ x ∂volume,
    HasDerivAt (fun y ↦ |representative U y|)
      ((SignType.sign (representative U x) : ℝ) *
        weakDerivativeRepresentative U x) x
  exact PDE.Analysis.Calculus.ae_hasDerivAt_abs
    (ae_hasDerivAt_representative U)

/-- Fundamental theorem of calculus for the absolute-value representative. -/
theorem intervalIntegral_absWeakDerivativeRepresentative_eq_sub
    (U : W^{1,1}(ℝ^1)) (a b : ℝ) :
    (∫ t in a..b, absWeakDerivativeRepresentative U t) =
      absRepresentative U b - absRepresentative U a := by
  rw [←
    (absolutelyContinuousOnInterval_absRepresentative U a b).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_hasDerivAt_absRepresentative U] with x hx _hx
  exact hx.deriv.symm

/-- Positive part of the selected one-dimensional Sobolev representative. -/
def positivePartRepresentative
    (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦ posPart (representative U t)

/-- The almost-everywhere derivative of `positivePartRepresentative`. -/
def positivePartWeakDerivativeRepresentative
    (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦
    ((1 + (SignType.sign (representative U t) : ℝ)) / 2) *
      weakDerivativeRepresentative U t

/-- Positive part preserves interval absolute continuity. -/
theorem absolutelyContinuousOnInterval_positivePartRepresentative
    (U : W^{1,1}(ℝ^1)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (positivePartRepresentative U) a b := by
  have h :=
    lipschitzWith_posPart.comp_absolutelyContinuousOnInterval
      (absolutelyContinuousOnInterval_representative U a b)
  apply h.congr
  intro x _hx
  rfl

/-- The derivative of the positive-part representative has the expected
sign coefficient almost everywhere. -/
theorem ae_hasDerivAt_positivePartRepresentative
    (U : W^{1,1}(ℝ^1)) :
    ∀ᵐ x ∂volume,
      HasDerivAt (positivePartRepresentative U)
        (positivePartWeakDerivativeRepresentative U x) x := by
  change ∀ᵐ x ∂volume,
    HasDerivAt
      (fun y ↦
        posPart (representative U y))
      (((1 + (SignType.sign (representative U x) : ℝ)) / 2) *
        weakDerivativeRepresentative U x) x
  exact PDE.Analysis.Calculus.ae_hasDerivAt_posPart
    (ae_hasDerivAt_representative U)

/-- Fundamental theorem of calculus for the positive-part representative. -/
theorem intervalIntegral_positivePartWeakDerivativeRepresentative_eq_sub
    (U : W^{1,1}(ℝ^1)) (a b : ℝ) :
    (∫ t in a..b, positivePartWeakDerivativeRepresentative U t) =
      positivePartRepresentative U b -
        positivePartRepresentative U a := by
  rw [←
    (absolutelyContinuousOnInterval_positivePartRepresentative U a b
      ).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_hasDerivAt_positivePartRepresentative U] with x hx _hx
  exact hx.deriv.symm

/-- Negative part of the selected one-dimensional Sobolev representative. -/
def negativePartRepresentative
    (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦ negPart (representative U t)

/-- The almost-everywhere derivative of `negativePartRepresentative`. -/
def negativePartWeakDerivativeRepresentative
    (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦
    (((SignType.sign (representative U t) : ℝ) - 1) / 2) *
      weakDerivativeRepresentative U t

/-- Negative part preserves interval absolute continuity. -/
theorem absolutelyContinuousOnInterval_negativePartRepresentative
    (U : W^{1,1}(ℝ^1)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (negativePartRepresentative U) a b := by
  have h :=
    lipschitzWith_negPart.comp_absolutelyContinuousOnInterval
      (absolutelyContinuousOnInterval_representative U a b)
  apply h.congr
  intro x _hx
  rfl

/-- The derivative of the negative-part representative has the expected
sign coefficient almost everywhere. -/
theorem ae_hasDerivAt_negativePartRepresentative
    (U : W^{1,1}(ℝ^1)) :
    ∀ᵐ x ∂volume,
      HasDerivAt (negativePartRepresentative U)
        (negativePartWeakDerivativeRepresentative U x) x := by
  change ∀ᵐ x ∂volume,
    HasDerivAt
      (fun y ↦
        negPart (representative U y))
      ((((SignType.sign (representative U x) : ℝ) - 1) / 2) *
        weakDerivativeRepresentative U x) x
  exact PDE.Analysis.Calculus.ae_hasDerivAt_negPart
    (ae_hasDerivAt_representative U)

/-- Fundamental theorem of calculus for the negative-part representative. -/
theorem intervalIntegral_negativePartWeakDerivativeRepresentative_eq_sub
    (U : W^{1,1}(ℝ^1)) (a b : ℝ) :
    (∫ t in a..b, negativePartWeakDerivativeRepresentative U t) =
      negativePartRepresentative U b -
        negativePartRepresentative U a := by
  rw [←
    (absolutelyContinuousOnInterval_negativePartRepresentative U a b
      ).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_hasDerivAt_negativePartRepresentative U] with x hx _hx
  exact hx.deriv.symm

/-- Interval truncation of the selected one-dimensional Sobolev
representative. -/
def truncationRepresentative
    (a b : ℝ) (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦
    PDE.Analysis.Calculus.intervalTruncation a b (representative U t)

/-- The almost-everywhere derivative of `truncationRepresentative`. -/
def truncationWeakDerivativeRepresentative
    (a b : ℝ) (U : W^{1,1}(ℝ^1)) : ℝ → ℝ :=
  fun t ↦
    (((SignType.sign (representative U t - a) : ℝ) -
      (SignType.sign (representative U t - b) : ℝ)) / 2) *
        weakDerivativeRepresentative U t

/-- Truncation to a nonempty interval preserves interval absolute
continuity. -/
theorem absolutelyContinuousOnInterval_truncationRepresentative
    {a b : ℝ} (hab : a ≤ b) (U : W^{1,1}(ℝ^1))
    (c d : ℝ) :
    AbsolutelyContinuousOnInterval (truncationRepresentative a b U)
      c d := by
  have h :=
    (PDE.Analysis.Calculus.lipschitzWith_intervalTruncation hab).comp_absolutelyContinuousOnInterval
      (absolutelyContinuousOnInterval_representative U c d)
  apply h.congr
  intro x _hx
  rfl

/-- The derivative of an interval truncation has the expected coefficient
almost everywhere. -/
theorem ae_hasDerivAt_truncationRepresentative
    (a b : ℝ) (U : W^{1,1}(ℝ^1)) :
    ∀ᵐ x ∂volume,
      HasDerivAt (truncationRepresentative a b U)
        (truncationWeakDerivativeRepresentative a b U x) x := by
  change ∀ᵐ x ∂volume,
    HasDerivAt
      (fun y ↦
        PDE.Analysis.Calculus.intervalTruncation a b
          (representative U y))
      ((((SignType.sign (representative U x - a) : ℝ) -
        (SignType.sign (representative U x - b) : ℝ)) / 2) *
          weakDerivativeRepresentative U x) x
  exact PDE.Analysis.Calculus.ae_hasDerivAt_intervalTruncation a b
    (ae_hasDerivAt_representative U)

/-- Fundamental theorem of calculus for an interval truncation. -/
theorem intervalIntegral_truncationWeakDerivativeRepresentative_eq_sub
    {a b : ℝ} (hab : a ≤ b) (U : W^{1,1}(ℝ^1))
    (c d : ℝ) :
    (∫ t in c..d, truncationWeakDerivativeRepresentative a b U t) =
      truncationRepresentative a b U d -
        truncationRepresentative a b U c := by
  rw [←
    (absolutelyContinuousOnInterval_truncationRepresentative hab U c d
      ).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards
    [ae_hasDerivAt_truncationRepresentative a b U] with x hx _hx
  exact hx.deriv.symm

end OneDimensionalNonsmooth

end SobolevSpace
