/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.AutoDiff.Jet.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# First-order algebra of multivariate formal jets

The first normalized coefficient of a jet is the constant coefficient of its formal partial
derivative. This observation lets the jet API inherit product, power, and inverse rules from
Mathlib's `MvPowerSeries.pderiv` rather than maintaining a second differentiation calculus.

The `value_*` lemmas say that the constant coefficient is a ring homomorphism (and respects
inversion over a field, with the `MvPowerSeries` convention that a series with zero constant
term has inverse `0`). The `firstCoefficient_*` lemmas are the usual first-order derivative
rules: linearity, the Leibniz rule, the power rule and the inverse rule, all stated for the
coefficient of `X i`.

## Main results

* `firstCoefficient_eq_value_pderiv`: `firstCoefficient i f = value (pderiv i f)`.
* `value_add`, `value_mul`, `value_neg`, `value_sub`, `value_pow`, `value_inv`.
* `firstCoefficient_add`, `firstCoefficient_mul`, `firstCoefficient_pow`,
  `firstCoefficient_inv`, `firstCoefficient_mul_inv`.
-/

@[expose] public section

namespace PDE.AutoDiff.Jet

/-- A first-order coefficient is the value of the corresponding formal partial derivative. -/
theorem firstCoefficient_eq_value_pderiv
    {ι R : Type*} {order : ℕ} [CommSemiring R]
    (i : ι) (f : Jet ι R order) :
    firstCoefficient i f =
      value (order := order) (MvPowerSeries.pderiv i f) := by
  unfold firstCoefficient coefficient value
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [MvPowerSeries.coeff_pderiv]
  simp

/-- The value (constant coefficient) of a sum is the sum of the values. -/
@[simp]
theorem value_add
    {ι R : Type*} {order : ℕ} [CommSemiring R]
    (f g : Jet ι R order) :
    value (f + g) = value f + value g := by
  simp [value]

/-- The value of a product is the product of the values. -/
@[simp]
theorem value_mul
    {ι R : Type*} {order : ℕ} [CommSemiring R]
    (f g : Jet ι R order) :
    value (f * g) = value f * value g := by
  simp [value]

/-- The value of a negated jet is the negated value. -/
@[simp]
theorem value_neg
    {ι R : Type*} {order : ℕ} [CommRing R]
    (f : Jet ι R order) :
    value (-f) = -value f := by
  simp [value]

/-- The value of a difference is the difference of the values. -/
@[simp]
theorem value_sub
    {ι R : Type*} {order : ℕ} [CommRing R]
    (f g : Jet ι R order) :
    value (f - g) = value f - value g := by
  simp [sub_eq_add_neg]

/-- The value of a natural power is the power of the value. -/
@[simp]
theorem value_pow
    {ι R : Type*} {order : ℕ} [CommSemiring R]
    (f : Jet ι R order) (n : ℕ) :
    value (f ^ n) = value f ^ n := by
  simp [value]

/-- The value of the formal inverse is the inverse of the value. When the value is zero both
sides are `0`, by the `MvPowerSeries` convention for inverting a series with no constant term. -/
@[simp]
theorem value_inv
    {ι R : Type*} {order : ℕ} [Field R]
    (f : Jet ι R order) :
    value f⁻¹ = (value f)⁻¹ := by
  simp [value]

/-- A constant jet has no first-order part. -/
@[simp]
theorem firstCoefficient_constant
    {ι R : Type*} {order : ℕ} [CommSemiring R] (i : ι) (c : R) :
    firstCoefficient i (constant c : Jet ι R order) = 0 := by
  rw [firstCoefficient_eq_value_pderiv]
  simp [value, constant]

/-- First-order coefficients are additive. -/
@[simp]
theorem firstCoefficient_add
    {ι R : Type*} {order : ℕ} [CommSemiring R]
    (i : ι) (f g : Jet ι R order) :
    firstCoefficient i (f + g) =
      firstCoefficient i f + firstCoefficient i g := by
  simp [firstCoefficient_eq_value_pderiv, value]

/-- Negating a jet negates its first-order coefficients. -/
@[simp]
theorem firstCoefficient_neg
    {ι R : Type*} {order : ℕ} [CommRing R]
    (i : ι) (f : Jet ι R order) :
    firstCoefficient i (-f) = -firstCoefficient i f := by
  simp [firstCoefficient_eq_value_pderiv, value]

/-- First-order coefficients of a difference are the difference of the coefficients. -/
@[simp]
theorem firstCoefficient_sub
    {ι R : Type*} {order : ℕ} [CommRing R]
    (i : ι) (f g : Jet ι R order) :
    firstCoefficient i (f - g) =
      firstCoefficient i f - firstCoefficient i g := by
  simp [sub_eq_add_neg]

/-- The first-order product rule for normalized jet coefficients. -/
theorem firstCoefficient_mul
    {ι R : Type*} {order : ℕ} [CommSemiring R]
    (i : ι) (f g : Jet ι R order) :
    firstCoefficient i (f * g) =
      value f * firstCoefficient i g + value g * firstCoefficient i f := by
  rw [firstCoefficient_eq_value_pderiv]
  simp [Derivation.leibniz, value, smul_eq_mul, firstCoefficient_eq_value_pderiv]

/-- The first-order natural-power rule for normalized jet coefficients. -/
theorem firstCoefficient_pow
    {ι R : Type*} {order : ℕ} [CommSemiring R]
    (i : ι) (f : Jet ι R order) (n : ℕ) :
    firstCoefficient i (f ^ n) =
      n * value f ^ (n - 1) * firstCoefficient i f := by
  rw [firstCoefficient_eq_value_pderiv]
  simp [value, firstCoefficient_eq_value_pderiv, mul_assoc]

/-- The first-order inverse rule for jets over a field. -/
theorem firstCoefficient_inv
    {ι R : Type*} {order : ℕ} [Field R]
    (i : ι) (f : Jet ι R order) :
    firstCoefficient i f⁻¹ =
      -(value f)⁻¹ ^ 2 * firstCoefficient i f := by
  rw [firstCoefficient_eq_value_pderiv]
  simp [value, firstCoefficient_eq_value_pderiv]

/-- The first-order quotient rule, expressed as multiplication by the formal inverse. -/
theorem firstCoefficient_mul_inv
    {ι R : Type*} {order : ℕ} [Field R]
    (i : ι) (f g : Jet ι R order) :
    firstCoefficient i (f * g⁻¹) =
      value f * (-(value g)⁻¹ ^ 2 * firstCoefficient i g) +
        value g⁻¹ * firstCoefficient i f := by
  rw [firstCoefficient_mul, firstCoefficient_inv]

end PDE.AutoDiff.Jet
