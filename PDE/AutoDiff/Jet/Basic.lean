/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Multivariate formal jets

Formal coefficient algebra for forward automatic differentiation.
A `Jet ι R order` is a multivariate formal power series in increments indexed by `ι`, together
with an order index recording the degree through which it is meant to be inspected or
certified. The coefficients are formal data. When a separate semantic theorem identifies them
with normalized derivatives, multiplication is ordinary power-series convolution and no
multinomial coefficients need to be inserted by the AD implementation.

Mathlib's `MvPowerSeries` supplies that algebra and its finite antidiagonal sums. The carrier is
not a truncated quotient: coefficients above `order` can be nonzero. `Jet.polynomial` is the
operation that actually discards them and extracts the finite collection of coefficients of
total degree at most `order`.

For example, squaring the seeded coordinate `x + X` produces
`x^2 + (2*x)*X + X^2`. Convolution computes the coefficient `2*x` of `X`.
Interpreting that coefficient as the derivative of `x ↦ x^2` is a separate
calculus statement. `Jet/Expression.lean` supplies that connection for compiled
expressions at first order under their validity hypotheses; the presence of
higher coefficients alone supplies no higher-derivative or convergence theorem.

This is a proof-only model. Numerical coefficient bounds use FloatLib interval enclosures;
CEGA supplies the connection to analytic derivative and remainder estimates.
The variable type is arbitrary; finite polynomial extraction assumes `Finite ι`.

## Main definitions

* `Jet ι R order`: reducibly `MvPowerSeries ι R`, tagged with an inspection order.
* `coefficient α f`, `value f`, `firstCoefficient i f`, `gradient f`: the formal coefficient
  at a multi-index, the constant coefficient, the coefficient of `X i`, and all of the latter.
* `constant c`, `coordinate x i`, `coordinates x`: the constant jet and the seeded input
  variables `x i + X i`.
* `polynomial f`: the truncation to total degree at most `order`, with `coefficient_polynomial`
  and `coefficient_polynomial_eq_zero` describing which coefficients survive.
* `values F`, `jacobian F`: for a family `F : κ → Jet ι R order` of output jets, the values and
  the output-first Jacobian `jacobian F k i = firstCoefficient i (F k)`.
-/

@[expose] public section

namespace PDE.AutoDiff

noncomputable section

/--
An order-indexed multivariate formal jet with coefficients in `R`.

The implementation is reducible to Mathlib's `MvPowerSeries`, so all algebraic laws and
coefficient convolution theorems are inherited rather than reproved. The order index is erased:
`Jet ι R 3` and `Jet ι R 5` are definitionally equal, and mixing inspection orders is permitted.
Extraction and composition take that index as an explicit policy, not as a typing invariant.
Only the value and first coefficients of compiled expressions have analytic certification;
higher coefficients are formal data.
-/
@[reducible]
def Jet (ι : Type*) (R : Type*) (_order : ℕ) :=
  MvPowerSeries ι R

namespace Jet

/-- A multi-index recording one derivative order for each variable. -/
abbrev MultiIndex (ι : Type*) :=
  ι →₀ ℕ

/-- The total derivative order represented by a multi-index. -/
def totalDegree {ι : Type*} (α : MultiIndex ι) : ℕ :=
  α.degree

/--
The formal coefficient at `α`.

A normalized Taylor interpretation requires a separate theorem relating the jet to derivatives
of a function.
-/
def coefficient {ι R : Type*} {order : ℕ} [Semiring R]
    (α : MultiIndex ι) (f : Jet ι R order) : R :=
  MvPowerSeries.coeff α f

/-- The value represented by a jet, namely its constant coefficient. -/
def value {ι R : Type*} {order : ℕ} [Semiring R]
    (f : Jet ι R order) : R :=
  MvPowerSeries.constantCoeff f

/-- The constant jet with value `c`. -/
def constant {ι R : Type*} {order : ℕ} [Semiring R] (c : R) :
    Jet ι R order :=
  MvPowerSeries.C c

/--
The `i`th input variable based at `x`.

The resulting formal series is `x i + X i`, so its value is `x i`, its normalized first
coefficient in direction `i` is one, and all other positive-degree coefficients vanish.
-/
def coordinate {ι R : Type*} {order : ℕ} [Semiring R]
    (x : ι → R) (i : ι) : Jet ι R order :=
  MvPowerSeries.C (x i) + MvPowerSeries.X i

/-- Seed every coordinate of a point as an independent jet variable. -/
def coordinates {ι R : Type*} {order : ℕ} [Semiring R]
    (x : ι → R) : ι → Jet ι R order :=
  fun i ↦ coordinate x i

/-- The normalized first-order coefficient in coordinate `i`. -/
def firstCoefficient {ι R : Type*} {order : ℕ} [Semiring R]
    (i : ι) (f : Jet ι R order) : R :=
  coefficient (Finsupp.single i 1) f

/-- Collect every first-order coordinate coefficient. -/
def gradient {ι R : Type*} {order : ℕ} [Semiring R]
    (f : Jet ι R order) : ι → R :=
  fun i ↦ firstCoefficient i f

/-- Extract the finite polynomial containing all coefficients of total degree at most `order`. -/
noncomputable def polynomial {ι R : Type*} {order : ℕ}
    [Finite ι] [CommSemiring R] (f : Jet ι R order) : MvPolynomial ι R :=
  MvPowerSeries.truncTotal (order + 1) f

/-! ## Coefficient equations -/

/-- The zero multi-index has total degree `0`. -/
@[simp]
theorem totalDegree_zero {ι : Type*} :
    totalDegree (0 : MultiIndex ι) = 0 := by
  simp [totalDegree]

/-- A multi-index with the single entry `n` in position `i` has total degree `n`. -/
@[simp]
theorem totalDegree_single {ι : Type*} (i : ι) (n : ℕ) :
    totalDegree (Finsupp.single i n) = n := by
  simp [totalDegree]

/-- Every coefficient of the zero jet vanishes. -/
@[simp]
theorem coefficient_zero {ι R : Type*} {order : ℕ} [Semiring R]
    (α : MultiIndex ι) :
    coefficient α (0 : Jet ι R order) = 0 :=
  MvPowerSeries.coeff_zero α

/-- Taking the coefficient at `α` is additive. -/
@[simp]
theorem coefficient_add {ι R : Type*} {order : ℕ} [Semiring R]
    (α : MultiIndex ι) (f g : Jet ι R order) :
    coefficient α (f + g) = coefficient α f + coefficient α g :=
  rfl

/-- The product coefficient is the finite convolution over decompositions `β + γ = α`. -/
theorem coefficient_mul {ι R : Type*} {order : ℕ}
    [DecidableEq ι] [Semiring R] (α : MultiIndex ι)
    (f g : Jet ι R order) :
    coefficient α (f * g) =
      ∑ p ∈ Finset.antidiagonal α,
        coefficient p.1 f * coefficient p.2 g :=
  MvPowerSeries.coeff_mul α f g

/-- The value of the constant jet `c` is `c`. -/
@[simp]
theorem value_constant {ι R : Type*} {order : ℕ} [Semiring R] (c : R) :
    value (constant c : Jet ι R order) = c :=
  MvPowerSeries.constantCoeff_C c

/-- The coordinate jet `x i + X i` has value `x i`, the base point's `i`th coordinate. -/
@[simp]
theorem value_coordinate {ι R : Type*} {order : ℕ} [Semiring R]
    (x : ι → R) (i : ι) :
    value (coordinate x i : Jet ι R order) = x i := by
  simp [value, coordinate]

/-- The coordinate jet in direction `i` has first-order coefficient `1` in that direction:
seeded inputs carry the identity as their Jacobian. -/
@[simp]
theorem firstCoefficient_coordinate_same {ι R : Type*} {order : ℕ}
    [Semiring R] (x : ι → R) (i : ι) :
    firstCoefficient i (coordinate x i : Jet ι R order) = 1 := by
  classical
  simp [firstCoefficient, coefficient, coordinate, MvPowerSeries.coeff_C,
    MvPowerSeries.coeff_X]

/-- The coordinate jet in direction `j` has zero first-order coefficient in any other
direction `i`. -/
@[simp]
theorem firstCoefficient_coordinate_of_ne {ι R : Type*} {order : ℕ}
    [Semiring R] (x : ι → R) {i j : ι} (h : i ≠ j) :
    firstCoefficient i (coordinate x j : Jet ι R order) = 0 := by
  classical
  simp [firstCoefficient, coefficient, coordinate, MvPowerSeries.coeff_C,
    MvPowerSeries.coeff_X, (Finsupp.single_left_injective one_ne_zero).ne h]

/-- Finite extraction preserves every coefficient through the declared jet order. -/
theorem coefficient_polynomial {ι R : Type*} {order : ℕ}
    [Finite ι] [CommSemiring R] (f : Jet ι R order)
    {α : MultiIndex ι} (hα : totalDegree α ≤ order) :
    (polynomial f).coeff α = coefficient α f := by
  exact MvPowerSeries.coeff_truncTotal f (by simpa [totalDegree] using hα)

/-- Finite extraction discards every coefficient above the declared jet order. -/
theorem coefficient_polynomial_eq_zero {ι R : Type*} {order : ℕ}
    [Finite ι] [CommSemiring R] (f : Jet ι R order)
    {α : MultiIndex ι} (hα : order < totalDegree α) :
    (polynomial f).coeff α = 0 := by
  exact MvPowerSeries.coeff_truncTotal_eq_zero f (by simpa [totalDegree] using hα)


/-- Extract the values of a family of output jets. -/
noncomputable def values {ι κ R : Type*} {order : ℕ} [Semiring R]
    (f : κ → Jet ι R order) : κ → R :=
  fun k ↦ value (f k)

/-- Extract the output-first Jacobian of a family of jets. -/
noncomputable def jacobian {ι κ R : Type*} {order : ℕ} [Semiring R]
    (f : κ → Jet ι R order) : κ → ι → R :=
  fun k ↦ gradient (f k)

/-- The `k`th output value is the value of the `k`th output jet. -/
@[simp]
theorem values_apply {ι κ R : Type*} {order : ℕ} [Semiring R]
    (f : κ → Jet ι R order) (k : κ) :
    values f k = value (f k) :=
  rfl

/-- The Jacobian entry `(k, i)` is the first-order coefficient of output `k` in input
direction `i`. -/
@[simp]
theorem jacobian_apply {ι κ R : Type*} {order : ℕ} [Semiring R]
    (f : κ → Jet ι R order) (k : κ) (i : ι) :
    jacobian f k i = firstCoefficient i (f k) :=
  rfl

/-- Reading the values of the seeded coordinates of `x` gives back `x`. -/
@[simp]
theorem values_coordinates {ι R : Type*} {order : ℕ} [Semiring R]
    (x : ι → R) :
    values (coordinates x : ι → Jet ι R order) = x := by
  funext i
  simp [values, coordinates]

end Jet

end

end PDE.AutoDiff
