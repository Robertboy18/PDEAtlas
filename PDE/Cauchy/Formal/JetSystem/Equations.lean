/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.Formal.Equation

/-!
# The first-order system of mixed jets

Every non-pure-time highest derivative is a spatial derivative of a lower jet.
This gives a finite first-order system with one state for each lower multiindex.
We fix one spatial direction for each such derivative and check the equations
on the tuple of mixed formal derivatives. This is the first-order system of Evans,
§4.6.3(a), whose unknowns are the partial derivatives of order below the order of the
equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3(a), (15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MvPowerSeries
open scoped BigOperators

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

local notation "J" => (Σ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ))
local notation "T" => {α : Sym (Fin (d + 1)) (k + 1) // α ≠ Sym.replicate (k + 1) 0}

/-- A principal multiindex other than pure time contains a spatial direction. -/
theorem exists_spatial_mem (α : T) :
    ∃ j : Fin d, j.succ ∈ α.1 := by
  by_contra! h
  apply α.2
  apply Sym.eq_replicate.mpr
  intro i hi
  revert hi
  exact Fin.cases (fun _ ↦ rfl) (fun j hj ↦ False.elim (h j hj)) i

/-- A spatial direction occurring in a non-pure-time highest multiindex. -/
def spatialDirection (α : T) : Fin d :=
  (exists_spatial_mem α).choose

/-- The chosen spatial direction occurs in the highest multiindex. -/
theorem spatialDirection_mem (α : T) :
    (spatialDirection α).succ ∈ α.1 :=
  (exists_spatial_mem α).choose_spec

/-- Remove the chosen spatial direction to obtain a highest lower-jet component. -/
def spatialJetIndex (α : T) : J :=
  ⟨Fin.last k, α.1.erase (spatialDirection α).succ (spatialDirection_mem α)⟩

/-- For a lower-order state, adjoining time stays within the lower jet. -/
def timeJetSuccessor (α : J) (h : (α.1 : ℕ) < k) : J :=
  ⟨⟨(α.1 : ℕ) + 1, by omega⟩, Sym.cons 0 α.2⟩

/-- At the highest lower order, adjoining time gives a principal multiindex. -/
def timeTopIndex (α : J) (h : ¬ (α.1 : ℕ) < k) : Sym (Fin (d + 1)) (k + 1) :=
  Sym.cast (by have := α.1.isLt; omega) (Sym.cons 0 α.2)

/-- The highest derivative is precisely a spatial derivative of its selected jet. -/
theorem iteratedPDeriv_eq_spatial_jet {R : Type*} [CommRing R]
    (α : T) (u : MvPowerSeries (Fin (d + 1)) R) :
    iteratedPDeriv (α.1 : Multiset (Fin (d + 1))) u =
      pderiv (spatialDirection α).succ (formalDerivativeTuple (k + 1) u (spatialJetIndex α)) := by
  have h := congrArg (fun β : Sym (Fin (d + 1)) (k + 1) ↦
    iteratedPDeriv (β : Multiset (Fin (d + 1))) u)
      (Sym.cons_erase (spatialDirection_mem α))
  simpa only [Sym.coe_cons, iteratedPDeriv_cons, formalDerivativeTuple,
    spatialJetIndex] using h.symm

/-- The time derivative of a lower-order state is its next time jet. -/
theorem pderiv_formalDerivativeTuple_of_lt {R : Type*} [CommRing R]
    (u : MvPowerSeries (Fin (d + 1)) R) (α : J) (h : (α.1 : ℕ) < k) :
    pderiv 0 (formalDerivativeTuple (k + 1) u α) =
      formalDerivativeTuple (k + 1) u (timeJetSuccessor α h) := by
  simp only [formalDerivativeTuple, timeJetSuccessor, Sym.coe_cons, iteratedPDeriv_cons]

/-- The time derivative of a highest lower-order state is its principal derivative. -/
theorem pderiv_formalDerivativeTuple_of_not_lt {R : Type*} [CommRing R]
    (u : MvPowerSeries (Fin (d + 1)) R) (α : J) (h : ¬ (α.1 : ℕ) < k) :
    pderiv 0 (formalDerivativeTuple (k + 1) u α) =
      iteratedPDeriv (timeTopIndex α h : Multiset (Fin (d + 1))) u := by
  simp only [formalDerivativeTuple, timeTopIndex, Sym.coe_cast, Sym.coe_cons,
    iteratedPDeriv_cons]

variable {R : Type*} [CommRing R]

/-- Principal matrices of the jet system. Each nontrivial row is either a
single spatial derivative or the normalized scalar principal expression. -/
def jetCoefficients (a : T → R) (j : Fin d) (α β : J) : R :=
  if h : (α.1 : ℕ) < k then 0
  else if ht : timeTopIndex α h = Sym.replicate (k + 1) 0 then
    ∑ γ : T, if spatialDirection γ = j ∧ spatialJetIndex γ = β then a γ else 0
  else
    if spatialDirection ⟨timeTopIndex α h, ht⟩ = j ∧
      spatialJetIndex ⟨timeTopIndex α h, ht⟩ = β then 1 else 0

/-- Lower-order rows are the next jet value; only the scalar principal row has forcing. -/
def jetForcing (b : R) (v : J → R) (α : J) : R :=
  if h : (α.1 : ℕ) < k then v (timeJetSuccessor α h)
  else if timeTopIndex α h = Sym.replicate (k + 1) 0 then b else 0

/-- The jet matrices commute with ring homomorphisms, in particular admissible
formal substitution and evaluation of coefficient functions. -/
theorem map_jetCoefficients {S : Type*} [CommRing S] (f : R →+* S)
    (a : T → R) (j : Fin d) (α β : J) :
    f (jetCoefficients a j α β) = jetCoefficients (fun γ ↦ f (a γ)) j α β := by
  classical
  unfold jetCoefficients
  split_ifs
  · exact map_zero f
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    split_ifs <;> simp
  · exact map_one f
  · exact map_zero f

/-- The forcing construction commutes with ring homomorphisms on coefficients
and state components. -/
theorem map_jetForcing {S : Type*} [CommRing S] (f : R →+* S)
    (b : R) (v : J → R) (α : J) :
    f (jetForcing b v α) = jetForcing (f b) (fun β ↦ f (v β)) α := by
  unfold jetForcing
  split_ifs <;> simp

/-- Contracting a selected row evaluates exactly its chosen spatial derivative. -/
private theorem sum_spatial_row (γ : T) (D : Fin d → J → R) :
    (∑ j, ∑ β, (if spatialDirection γ = j ∧ spatialJetIndex γ = β then 1 else 0) *
      D j β) = D (spatialDirection γ) (spatialJetIndex γ) := by
  classical
  simp only [ite_and, ite_mul, one_mul, zero_mul]
  simp

/-- The principal row contracts to the sum of the selected highest derivatives. -/
private theorem sum_principal_row (a : T → R) (D : Fin d → J → R) :
    (∑ j, ∑ β, (∑ γ : T,
      if spatialDirection γ = j ∧ spatialJetIndex γ = β then a γ else 0) * D j β) =
      ∑ γ, a γ * D (spatialDirection γ) (spatialJetIndex γ) := by
  classical
  simp only [Finset.sum_mul]
  calc
    _ = ∑ j, ∑ γ : T, ∑ β : J,
        (if spatialDirection γ = j ∧ spatialJetIndex γ = β then a γ else 0) * D j β := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = ∑ γ : T, ∑ j, ∑ β : J,
        (if spatialDirection γ = j ∧ spatialJetIndex γ = β then a γ else 0) * D j β :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro γ hγ
      simp only [ite_and, ite_mul, zero_mul]
      simp

/-- The formal derivative tuple solves the finite first-order jet equations.
The scalar highest-time equation is used only in its corresponding principal row. -/
theorem formalDerivativeTuple_equation
    (a : T → MvPowerSeries (J ⊕ Fin (d + 1)) R)
    (b : MvPowerSeries (J ⊕ Fin (d + 1)) R)
    {u : MvPowerSeries (Fin (d + 1)) R}
    (hu : (pderiv 0)^[k + 1] u = formalRightHandSide a b u) (α : J) :
    pderiv 0 (formalDerivativeTuple (k + 1) u α) =
      (∑ j, ∑ β, jetCoefficients
        (fun γ ↦ subst (formalArguments (k + 1) u) (a γ)) j α β *
          pderiv j.succ (formalDerivativeTuple (k + 1) u β)) +
      jetForcing (subst (formalArguments (k + 1) u) b)
        (formalDerivativeTuple (k + 1) u) α := by
  classical
  by_cases h : (α.1 : ℕ) < k
  · simp only [jetCoefficients, jetForcing, dite_eq_left h, zero_mul,
      Finset.sum_const_zero, zero_add]
    exact pderiv_formalDerivativeTuple_of_lt u α h
  · rw [pderiv_formalDerivativeTuple_of_not_lt u α h]
    by_cases ht : timeTopIndex α h = Sym.replicate (k + 1) 0
    · simp only [jetCoefficients, jetForcing, dite_eq_right h, dite_eq_left ht,
        ite_eq_left ht]
      rw [sum_principal_row, ht, Sym.coe_replicate, iteratedPDeriv_replicate, hu]
      unfold formalRightHandSide
      congr 1
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [iteratedPDeriv_eq_spatial_jet γ u]
    · simp only [jetCoefficients, jetForcing, dite_eq_right h, dite_eq_right ht,
        ite_eq_right ht, add_zero]
      rw [sum_spatial_row]
      exact iteratedPDeriv_eq_spatial_jet ⟨timeTopIndex α h, ht⟩ u

/-- Every lower component has zero full spatial trace when the first `k + 1`
time coefficients of the scalar solution vanish. -/
theorem constantCoeff_formalDerivativeTuple
    {u : MvPowerSeries (Fin (d + 1)) R}
    (hu : ∀ j < k + 1, PowerSeries.coeff j (finSuccEquiv R d u) = 0) (α : J) :
    PowerSeries.constantCoeff
      (finSuccEquiv R d (formalDerivativeTuple (k + 1) u α)) = 0 := by
  apply MvPowerSeries.ext
  intro e
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeff_finSuccEquiv]
  have hcoeff (f : Fin (d + 1) →₀ ℕ) (hf : f 0 ≤ k) :
      coeff f u = coeff f (0 : MvPowerSeries (Fin (d + 1)) R) := by
    have h := congrArg (coeff f.tail) (hu (f 0) (by omega))
    simpa only [coeff_coeff_finSuccEquiv, Finsupp.cons_tail, map_zero] using h
  have hc : (α.2 : Multiset (Fin (d + 1))).count 0 ≤ k :=
    (Multiset.count_le_card 0 _).trans (by
      simpa only [Sym.card_coe] using (Nat.le_of_lt_succ α.1.isLt))
  have h := coeff_iteratedPDeriv_eq_of_coordinate_le 0
    (α.2 : Multiset (Fin (d + 1))) hcoeff (e.cons 0) (by simpa using hc)
  simpa only [formalDerivativeTuple, iteratedPDeriv_zero, map_zero] using h

end PDE.Cauchy.Quasilinear.Analytic
