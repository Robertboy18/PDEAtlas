/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Mixed derivatives of formal power series

Formal partial derivatives commute. They can therefore be iterated along a
multiset of coordinate directions, without choosing an ordering. Differentiating
in a multiset consumes precisely its multiplicity in a distinguished coordinate
when comparing coefficients through a fixed degree.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ R : Type*} [CommSemiring R]

/-- Mixed formal partial derivatives commute. -/
theorem pderiv_comm (i j : σ) (f : MvPowerSeries σ R) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  apply ext
  intro a
  simp only [coeff_pderiv]
  simp [hij, Ne.symm hij, add_comm, add_left_comm, mul_comm, mul_left_comm]

local instance : LeftCommutative (fun (i : σ) (f : MvPowerSeries σ R) ↦ pderiv i f) :=
  ⟨pderiv_comm⟩

/-- Iterate the native formal partial derivative in a multiset of directions. -/
noncomputable def iteratedPDeriv (s : Multiset σ) (f : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  s.foldr (fun i g ↦ pderiv i g) f

/-- Differentiating in no directions leaves the series unchanged. -/
@[simp]
theorem iteratedPDeriv_zero_multiset (f : MvPowerSeries σ R) :
    iteratedPDeriv 0 f = f := rfl

/-- Inserting a direction applies its partial derivative to the mixed derivative. -/
@[simp]
theorem iteratedPDeriv_cons (i : σ) (s : Multiset σ) (f : MvPowerSeries σ R) :
    iteratedPDeriv (i ::ₘ s) f = pderiv i (iteratedPDeriv s f) := by
  simp only [iteratedPDeriv, Multiset.foldr_cons]

/-- Joining multisets composes their mixed derivatives. -/
theorem iteratedPDeriv_add (s t : Multiset σ) (f : MvPowerSeries σ R) :
    iteratedPDeriv (s + t) f = iteratedPDeriv s (iteratedPDeriv t f) := by
  simp only [iteratedPDeriv, Multiset.foldr_add]

/-- A partial derivative commutes with every mixed derivative. -/
theorem pderiv_iteratedPDeriv (i : σ) (s : Multiset σ) (f : MvPowerSeries σ R) :
    pderiv i (iteratedPDeriv s f) = iteratedPDeriv s (pderiv i f) := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons j s ih =>
    rw [iteratedPDeriv_cons, pderiv_comm, ih, iteratedPDeriv_cons]

/-- Repeated occurrences of one direction give its iterated partial derivative. -/
theorem iteratedPDeriv_replicate (n : ℕ) (i : σ) (f : MvPowerSeries σ R) :
    iteratedPDeriv (Multiset.replicate n i) f = (pderiv i)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Multiset.replicate_succ, iteratedPDeriv_cons, ih, Function.iterate_succ_apply']

/-- Every mixed derivative of the zero series is zero. -/
@[simp]
theorem iteratedPDeriv_zero (s : Multiset σ) :
    iteratedPDeriv s (0 : MvPowerSeries σ R) = 0 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons i s ih => simp only [iteratedPDeriv_cons, ih, map_zero]

/-- Mixed differentiation uses only the indicated number of coefficients in
the distinguished variable; all spatial coefficients are compared at once. -/
theorem coeff_iteratedPDeriv_eq_of_coordinate_le [DecidableEq σ]
    (i : σ) (s : Multiset σ) {n : ℕ} {f g : MvPowerSeries σ R}
    (h : ∀ a : σ →₀ ℕ, a i ≤ n → coeff a f = coeff a g) :
    ∀ a : σ →₀ ℕ, a i + s.count i ≤ n →
      coeff a (iteratedPDeriv s f) = coeff a (iteratedPDeriv s g) := by
  induction s using Multiset.induction_on with
  | empty =>
    intro a ha
    exact h a (by simpa only [Multiset.count_zero, add_zero] using ha)
  | @cons j s ih =>
    intro a ha
    have hb : (a + Finsupp.single j 1 : σ →₀ ℕ) i + s.count i ≤ n := by
      by_cases hji : j = i
      · subst j
        simpa [Multiset.count_cons, add_assoc, add_comm, add_left_comm] using ha
      · simpa [Multiset.count_cons, Finsupp.single_apply, hji, Ne.symm hji] using ha
    rw [iteratedPDeriv_cons, iteratedPDeriv_cons, coeff_pderiv, coeff_pderiv, ih _ hb]

end MvPowerSeries
