/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.AutoDiff.Jet.Analytic
public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.FiniteSum

/-!
# Rational enclosures of multivariate formal jets

An `IntervalJet` assigns a rational interval to each formal multivariate coefficient. It
has no ring instances: interval multiplication is sound but not
distributive, so presenting rational intervals as a semiring would make false algebraic
identities available to simplification.

The operations below are therefore explicit. Their soundness theorems state that coefficient
enclosures are preserved by constants, coordinate seeding, addition, negation, and power-series
convolution. Value, gradient, and Jacobian projections provide the data used by validated
Newton and Krawczyk checkers.

The enclosure relation `Encloses F f` asks that `F α` contain the exact coefficient of `f` at
every multi-index `α` of total degree at most `order`; coefficients above the order are
unconstrained, matching the fact that `Jet.polynomial` discards them. The convolution theorem
`mul_encloses` is where the order bound matters: a coefficient of degree `≤ order` in `f * g`
only involves coefficients of `f` and `g` of degree `≤ order`, since degrees add along the
antidiagonal.

## Main results

* `IntervalJet ι order`, `Encloses`: interval coefficient data and the soundness relation.
* `constant_encloses`, `coordinate_encloses`, `add_encloses`, `neg_encloses`, `sub_encloses`,
  `mul_encloses`: soundness of each operation.
* `value_mem`, `gradient_mem`, `values_jacobian_mem`: the projections used by validated
  root-finding contain the exact value, gradient and Jacobian entries.
* `valueAndGradient_mem_of_representsFirstOrderAt`: when the exact jet has first-order
  calculus semantics at `x`, the interval value and gradient enclose `f x` and its partial
  derivatives.
-/

@[expose] public section

namespace PDE.AutoDiff

open CAS.Continuum

/--
Rational interval bounds for the normalized coefficients of an order-indexed jet.

The function is total on multi-indices. Soundness predicates only inspect coefficients through
the declared order.
-/
def IntervalJet (ι : Type*) (_order : ℕ) :=
  Jet.MultiIndex ι → RationalInterval

namespace IntervalJet

/-- Every relevant interval coefficient contains the corresponding exact jet coefficient. -/
def Encloses {ι : Type*} {order : ℕ}
    (bounds : IntervalJet ι order) (f : Jet ι ℝ order) : Prop :=
  ∀ α, Jet.totalDegree α ≤ order →
    (bounds α).MemReal (Jet.coefficient α f)

/-- Exact rational constant coefficients, with zero bounds at every positive multi-index. -/
noncomputable def constant {ι : Type*} {order : ℕ} (q : ℚ) :
    IntervalJet ι order := by
  classical
  exact fun α ↦ if α = 0 then RationalInterval.const q else RationalInterval.const 0

/--
Interval coordinate seeding.

The constant coefficient is the supplied interval for the base point, the selected linear
coefficient is exactly one, and every other coefficient is exactly zero.
-/
noncomputable def coordinate {ι : Type*} [DecidableEq ι] {order : ℕ}
    (x : ι → RationalInterval) (i : ι) : IntervalJet ι order := by
  classical
  exact fun α ↦
    if α = 0 then x i
    else if α = Finsupp.single i 1 then RationalInterval.const 1
    else RationalInterval.const 0

/-- Seed every input coordinate with its interval base point. -/
noncomputable def coordinates {ι : Type*} [DecidableEq ι] {order : ℕ}
    (x : ι → RationalInterval) : ι → IntervalJet ι order :=
  fun i ↦ coordinate x i

/-- Coefficient-wise interval addition. -/
def add {ι : Type*} {order : ℕ}
    (f g : IntervalJet ι order) : IntervalJet ι order :=
  fun α ↦ (f α).add (g α)

/-- Coefficient-wise interval negation. -/
def neg {ι : Type*} {order : ℕ}
    (f : IntervalJet ι order) : IntervalJet ι order :=
  fun α ↦ (f α).neg

/-- Coefficient-wise interval subtraction. -/
def sub {ι : Type*} {order : ℕ}
    (f g : IntervalJet ι order) : IntervalJet ι order :=
  add f (neg g)

/--
Power-series convolution of interval coefficients.

Each antidiagonal is finite even when the variable index type is infinite.
-/
noncomputable def mul {ι : Type*} [DecidableEq ι] {order : ℕ}
    (f g : IntervalJet ι order) : IntervalJet ι order :=
  fun α ↦
    RationalInterval.sum (Finset.antidiagonal α) fun p ↦
      (f p.1).mul (g p.2)

/-- The interval containing the constant coefficient. -/
def value {ι : Type*} {order : ℕ}
    (f : IntervalJet ι order) : RationalInterval :=
  f 0

/-- The intervals containing all normalized first-order coefficients. -/
noncomputable def gradient {ι : Type*} {order : ℕ}
    (f : IntervalJet ι order) : ι → RationalInterval :=
  fun i ↦ f (Finsupp.single i 1)

/-- The value intervals of a family of interval jets. -/
def values {ι κ : Type*} {order : ℕ}
    (f : κ → IntervalJet ι order) : κ → RationalInterval :=
  fun k ↦ value (f k)

/-- The output-first interval Jacobian of a family of interval jets. -/
noncomputable def jacobian {ι κ : Type*} {order : ℕ}
    (f : κ → IntervalJet ι order) : κ → ι → RationalInterval :=
  fun k ↦ gradient (f k)

/-! ## Soundness -/

/-- Rational singleton coefficients enclose the corresponding exact constant jet. -/
theorem constant_encloses {ι : Type*} {order : ℕ} (q : ℚ) :
    Encloses (constant q) (Jet.constant (q : ℝ) : Jet ι ℝ order) := by
  intro α hα
  by_cases hzero : α = 0
  · subst α
    simp [constant, Jet.coefficient, Jet.constant]
  · rw [show constant q α = RationalInterval.const 0 by
      simp [constant, hzero]]
    rw [show
      Jet.coefficient α (Jet.constant (q : ℝ) : Jet ι ℝ order) = 0 by
      exact MvPowerSeries.coeff_C_of_ne_zero hzero (q : ℝ)]
    simpa using RationalInterval.memReal_const (0 : ℚ)

/-- Interval coordinate seeding encloses every coordinate jet based at a contained point. -/
theorem coordinate_encloses {ι : Type*} [DecidableEq ι] {order : ℕ}
    {x : ι → RationalInterval} {y : ι → ℝ}
    (hxy : ∀ i, (x i).MemReal (y i)) (i : ι) :
    Encloses (coordinate x i) (Jet.coordinate y i : Jet ι ℝ order) := by
  intro α hα
  by_cases hzero : α = 0
  · subst α
    simpa [coordinate, Jet.coefficient, Jet.coordinate,
      MvPowerSeries.coeff_C, MvPowerSeries.coeff_X] using hxy i
  · by_cases hlinear : α = Finsupp.single i 1
    · subst α
      simpa [coordinate, Jet.coefficient, Jet.coordinate,
        MvPowerSeries.coeff_C, MvPowerSeries.coeff_X] using
        RationalInterval.memReal_const 1
    · simpa [coordinate, Jet.coefficient, Jet.coordinate,
        MvPowerSeries.coeff_C, MvPowerSeries.coeff_X, hzero, hlinear] using
        RationalInterval.memReal_const 0

/-- Interval addition preserves coefficient enclosures. -/
theorem add_encloses {ι : Type*} {order : ℕ}
    {f g : Jet ι ℝ order} {F G : IntervalJet ι order}
    (hF : Encloses F f) (hG : Encloses G g) :
    Encloses (add F G) (f + g) := by
  intro α hα
  simpa [add] using RationalInterval.add_sound (hF α hα) (hG α hα)

/-- Interval negation preserves coefficient enclosures. -/
theorem neg_encloses {ι : Type*} {order : ℕ}
    {f : Jet ι ℝ order} {F : IntervalJet ι order}
    (hF : Encloses F f) :
    Encloses (neg F) (-f) := by
  intro α hα
  simpa [neg, Jet.coefficient] using RationalInterval.neg_sound (hF α hα)

/-- Interval subtraction preserves coefficient enclosures. -/
theorem sub_encloses {ι : Type*} {order : ℕ}
    {f g : Jet ι ℝ order} {F G : IntervalJet ι order}
    (hF : Encloses F f) (hG : Encloses G g) :
    Encloses (sub F G) (f - g) := by
  simpa [sub, sub_eq_add_neg] using add_encloses hF (neg_encloses hG)

/-- Interval convolution preserves every coefficient enclosure through the declared order. -/
theorem mul_encloses {ι : Type*} [DecidableEq ι] {order : ℕ}
    {f g : Jet ι ℝ order} {F G : IntervalJet ι order}
    (hF : Encloses F f) (hG : Encloses G g) :
    Encloses (mul F G) (f * g) := by
  intro α hα
  rw [Jet.coefficient_mul]
  apply RationalInterval.sum_sound
  intro p hp
  have hsum : Jet.totalDegree p.1 + Jet.totalDegree p.2 = Jet.totalDegree α := by
    have hpadd : p.1 + p.2 = α := Finset.mem_antidiagonal.mp hp
    simpa [Jet.totalDegree] using congrArg Jet.totalDegree hpadd
  apply RationalInterval.mul_sound
  · apply hF
    omega
  · apply hG
    omega

/-- The value interval of an enclosing interval jet contains the exact jet value. -/
theorem value_mem {ι : Type*} {order : ℕ}
    {f : Jet ι ℝ order} {F : IntervalJet ι order}
    (hF : Encloses F f) :
    (value F).MemReal (Jet.value f) := by
  exact hF 0 (by simp [Jet.totalDegree])

/-- At positive order, every interval gradient entry contains the exact first coefficient. -/
theorem gradient_mem {ι : Type*} {order : ℕ}
    {f : Jet ι ℝ order} {F : IntervalJet ι order}
    (hF : Encloses F f) (horder : 1 ≤ order) (i : ι) :
    (gradient F i).MemReal (Jet.firstCoefficient i f) := by
  exact hF (Finsupp.single i 1) (by simpa [Jet.totalDegree] using horder)

/--
If the exact formal jet has first-order calculus semantics, its interval value and gradient
enclose the function value and its coordinate derivatives.

This theorem transfers a pointwise semantic certificate. It does not turn coefficientwise
enclosures into uniform bounds over a box.
-/
theorem valueAndGradient_mem_of_representsFirstOrderAt
    {n order : ℕ} {jet : Jet (Fin n) ℝ order}
    {f : ℝ^n → ℝ} {x : ℝ^n} {F : IntervalJet (Fin n) order}
    (hF : Encloses F jet) (horder : 1 ≤ order)
    (hjet : Jet.RepresentsFirstOrderAt jet f x) :
    (value F).MemReal (f x) ∧
      ∀ i, (gradient F i).MemReal ((∂[i] f) x) := by
  constructor
  · rw [← hjet.value_eq]
    exact value_mem hF
  · intro i
    rw [← hjet.firstCoefficient_eq_partialDeriv i]
    exact gradient_mem hF horder i

/--
At positive order, interval residual values and Jacobian entries contain the corresponding exact
data. Validated Newton-style algorithms start from this theorem.
-/
theorem values_jacobian_mem {ι κ : Type*} {order : ℕ}
    {f : κ → Jet ι ℝ order} {F : κ → IntervalJet ι order}
    (hF : ∀ k, Encloses (F k) (f k)) (horder : 1 ≤ order) :
    (∀ k, (values F k).MemReal
      (Jet.values f k)) ∧
      (∀ k i, (jacobian F k i).MemReal
        (Jet.jacobian f k i)) := by
  constructor
  · intro k
    exact value_mem (hF k)
  · intro k i
    exact gradient_mem (hF k) horder i

end IntervalJet

end PDE.AutoDiff
