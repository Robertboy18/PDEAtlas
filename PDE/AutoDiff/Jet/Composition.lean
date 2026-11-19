/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.AutoDiff.Jet.Algebra

/-!
# Finite formal composition of multivariate jets

Given a jet `f` and a coefficient sequence `a`, `compose` forms the finite substitution using
outer coefficients through the declared order:

```text
∑ k ≤ order, a k * (f - value f)^k
```

The construction is purely formal and is independent of the source of the outer coefficients.
Interpreting it as function composition requires a separate theorem identifying `a k` with
normalized derivatives and justifying the relevant Taylor expansion.

The point of centering at `value f` is that `centered f` has zero constant term, so
`(centered f)^k` has no coefficients below total degree `k`. Consequently each coefficient of
total degree `≤ order` of the composition is a finite expression in `a 0, …, a order`, which is
what `compose_congr` records, and the first-order coefficient sees only `a 1` (the chain rule).

## Main results

* `centered`, `compose`: the centred jet and the finite substitution above.
* `value_compose`: the value of the composition is `outer 0`.
* `firstCoefficient_compose`: the chain rule `∂ᵢ(g ∘ f) = g'(f) · ∂ᵢ f` for first-order
  coefficients.
* `coefficient_compose_coordinate`: composing with a seeded coordinate returns each supplied
  coefficient `outer n`, `n ≤ order`, so no outer coefficient is lost.
* `compose_congr`, `compose_order_zero`: dependence on the outer coefficients through the
  declared order only.
-/

@[expose] public section

namespace PDE.AutoDiff.Jet

noncomputable section

/-- Remove the constant coefficient from a jet. -/
def centered {ι R : Type*} {order : ℕ} [CommRing R]
    (f : Jet ι R order) : Jet ι R order :=
  f - constant (value f)

/--
Formally compose a jet with a univariate coefficient polynomial using outer coefficients through
the jet's declared order.

`outer k` is expected to be the normalized coefficient `g^(k)(value f) / k!`. The definition
is algebraic and does not itself assert analytic correctness of the supplied coefficients.
Because `Jet` retains a full power series, the returned series can have nonzero coefficients
above `order`; only coefficients through `order` are the intended certified observations.
-/
def compose {ι R : Type*} {order : ℕ} [CommRing R]
    (outer : ℕ → R) (f : Jet ι R order) : Jet ι R order :=
  ∑ k ∈ Finset.range (order + 1),
    constant (outer k) * centered f ^ k

/-- Centering the coordinate jet `x i + X i` leaves exactly the increment `X i`. -/
@[simp]
theorem centered_coordinate {ι R : Type*} {order : ℕ}
    [CommRing R] (x : ι → R) (i : ι) :
    centered (coordinate x i : Jet ι R order) = MvPowerSeries.X i := by
  unfold centered coordinate value constant
  simp

/-- A centred jet has zero constant term. -/
@[simp]
theorem value_centered {ι R : Type*} {order : ℕ} [CommRing R]
    (f : Jet ι R order) :
    value (centered f) = 0 := by
  simp [value, centered, constant]

/-- The value of a composition is the zeroth outer coefficient: every term with `k ≥ 1`
contains a factor with zero constant term. -/
@[simp]
theorem value_compose {ι R : Type*} {order : ℕ} [CommRing R]
    (outer : ℕ → R) (f : Jet ι R order) :
    value (compose outer f) = outer 0 := by
  have hcenter : MvPowerSeries.constantCoeff (centered f) = 0 := by
    simpa only [value] using value_centered f
  simp only [value, compose, map_sum, map_mul, map_pow]
  rw [Finset.sum_eq_single 0]
  · simp [constant]
  · intro k hk hk_ne
    simp [hcenter, hk_ne]
  · simp

/-- Composition depends only on the outer coefficients through the declared order. -/
theorem compose_congr {ι R : Type*} {order : ℕ} [CommRing R]
    {outer₁ outer₂ : ℕ → R}
    (h : ∀ k ≤ order, outer₁ k = outer₂ k)
    (f : Jet ι R order) :
    compose outer₁ f = compose outer₂ f := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [h k (Nat.le_of_lt_succ hk)]

/-- Order-zero composition retains exactly the outer function's value. -/
theorem compose_order_zero {ι R : Type*} [CommRing R]
    (outer : ℕ → R) (f : Jet ι R 0) :
    compose outer f = constant (outer 0) := by
  simp [compose]

/--
Composition with a seeded coordinate recovers every supplied univariate coefficient through the
declared jet order.
-/
theorem coefficient_compose_coordinate
    {ι R : Type*} {order : ℕ} [CommRing R]
    (outer : ℕ → R) (x : ι → R) (i : ι) {n : ℕ} (hn : n ≤ order) :
    coefficient (Finsupp.single i n)
        (compose outer (coordinate x i : Jet ι R order)) = outer n := by
  classical
  simp only [compose, map_sum, coefficient, centered_coordinate]
  rw [Finset.sum_eq_single n]
  · simp [constant, MvPowerSeries.coeff_X_pow]
  · intro k hk hkn
    have hsingle : Finsupp.single i n ≠ Finsupp.single i k := by
      intro h
      apply hkn
      have hnk : n = k := by
        simpa using DFunLike.congr_fun h i
      exact hnk.symm
    simp [constant, MvPowerSeries.coeff_X_pow, hsingle]
  · simp only [Finset.mem_range]
    omega

/--
The first coefficient of a composition satisfies the chain rule.

Only the linear outer coefficient contributes because `centered f` has zero constant term.
-/
theorem firstCoefficient_compose
    {ι R : Type*} {order : ℕ} [Field R]
    (outer : ℕ → R) (f : Jet ι R order) (i : ι)
    (horder : 1 ≤ order) :
    firstCoefficient i (compose outer f) =
      outer 1 * firstCoefficient i f := by
  rw [firstCoefficient_eq_value_pderiv]
  simp only [compose, map_sum, Derivation.leibniz,
    MvPowerSeries.pderiv_pow, value]
  simp only [map_add]
  rw [Finset.sum_eq_single 1]
  · simp [constant, centered, value, firstCoefficient_eq_value_pderiv]
  · intro k hk hk_ne
    rw [Finset.mem_range] at hk
    by_cases hk0 : k = 0
    · subst k
      simp [constant]
    · have hkpred : k - 1 ≠ 0 := by omega
      simp [constant, centered, value, hkpred]
  · intro hnot
    simp only [Finset.mem_range, not_lt] at hnot
    omega

end

end PDE.AutoDiff.Jet
