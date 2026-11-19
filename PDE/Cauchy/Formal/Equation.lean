/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Filtration
public import PDE.Analysis.Analytic.PowerSeries.IteratedDerivative

/-!
# Formal scalar Cauchy equations of arbitrary order

The equation is solved for the pure time derivative of highest order. Its other
highest-order terms have at least one spatial direction. Coefficients depend on
position and every lower mixed derivative, each indexed once by its multiset.
The first `k` time coefficients vanish as entire formal spatial series. This is the problem
(14) of Evans, §4.6.3(a), with zero Cauchy data, solved for the pure normal derivative by the
noncharacteristic condition `a_(0,…,0,k) ≠ 0`; Evans then reduces it to a first-order system,
while the formal equation keeps the order `k`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3(a), (14) and the reduction to the first-order
  system (15), pp. 239-240.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MvPowerSeries
open scoped BigOperators

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ} {R : Type*} [CommRing R]

/-- The formal lower jet contains one component for each lower mixed partial. -/
def formalDerivativeTuple (k : ℕ) (u : MvPowerSeries (Fin (d + 1)) R) :
    (Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) → MvPowerSeries (Fin (d + 1)) R :=
  fun α ↦ iteratedPDeriv (α.2 : Multiset (Fin (d + 1))) u

/-- The coefficient arguments consist of the lower jet and all position variables. -/
def formalArguments (k : ℕ) (u : MvPowerSeries (Fin (d + 1)) R) :
    (Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1) →
      MvPowerSeries (Fin (d + 1)) R :=
  Sum.elim (formalDerivativeTuple k u) X

/-- The normalized scalar right-hand side omits only the pure highest time derivative. -/
def formalRightHandSide
    (a : {α : Sym (Fin (d + 1)) k // α ≠ Sym.replicate k 0} →
      MvPowerSeries ((Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) R)
    (b : MvPowerSeries
      ((Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) R)
    (u : MvPowerSeries (Fin (d + 1)) R) : MvPowerSeries (Fin (d + 1)) R :=
  (∑ α, subst (formalArguments k u) (a α) *
    iteratedPDeriv (α.1 : Multiset (Fin (d + 1))) u) +
      subst (formalArguments k u) b

private theorem count_time_lt
    (α : {α : Sym (Fin (d + 1)) k // α ≠ Sym.replicate k 0}) :
    (α.1 : Multiset (Fin (d + 1))).count 0 < k := by
  have hle := Multiset.count_le_card 0 (α.1 : Multiset (Fin (d + 1)))
  rw [Sym.card_coe] at hle
  refine lt_of_le_of_ne hle ?_
  intro he
  apply α.2
  apply Sym.eq_replicate.mpr
  have hc : (α.1 : Multiset (Fin (d + 1))).count 0 =
      (α.1 : Multiset (Fin (d + 1))).card := by
    simpa only [Sym.card_coe] using he
  exact fun i hi ↦ ((Multiset.count_eq_card.mp hc) i hi).symm

/-- Vanishing time coefficients below `k` make every lower jet argument admissible
for substitution, including its full spatial trace at time zero. -/
theorem hasSubst_formalArguments
    {u : MvPowerSeries (Fin (d + 1)) R}
    (hu : ∀ j < k, PowerSeries.coeff j (finSuccEquiv R d u) = 0) :
    HasSubst (formalArguments k u) := by
  apply hasSubst_of_constantCoeff_zero
  intro j
  cases j with
  | inr i => simp [formalArguments]
  | inl α =>
    change constantCoeff (iteratedPDeriv (α.2 : Multiset (Fin (d + 1))) u) = 0
    have hc : (α.2 : Multiset (Fin (d + 1))).count 0 < k :=
      (Multiset.count_le_card 0 _).trans_lt (by simpa only [Sym.card_coe] using α.1.isLt)
    have hcoeff (e : Fin (d + 1) →₀ ℕ) (he : e 0 ≤ k - 1) :
        coeff e u = coeff e (0 : MvPowerSeries (Fin (d + 1)) R) := by
      have hj : e 0 < k := by omega
      have h := congrArg (coeff e.tail) (hu (e 0) hj)
      simpa only [coeff_coeff_finSuccEquiv, Finsupp.cons_tail, map_zero] using h
    have h := coeff_iteratedPDeriv_eq_of_coordinate_le 0
      (α.2 : Multiset (Fin (d + 1))) hcoeff 0 (by simpa using Nat.le_pred_of_lt hc)
    simpa only [iteratedPDeriv_zero, map_zero, coeff_zero_eq_constantCoeff_apply] using h

/-- A coefficient of time degree `n` of the scalar right-hand side uses only
time coefficients strictly below `n + k` of the unknown. -/
theorem coeff_formalRightHandSide_eq
    (hk : 0 < k)
    (a : {α : Sym (Fin (d + 1)) k // α ≠ Sym.replicate k 0} →
      MvPowerSeries ((Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) R)
    (b : MvPowerSeries
      ((Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) R)
    {u v : MvPowerSeries (Fin (d + 1)) R} {n : ℕ}
    (hu : HasSubst (formalArguments k u)) (hv : HasSubst (formalArguments k v))
    (h : ∀ e : Fin (d + 1) →₀ ℕ, e 0 < n + k → coeff e u = coeff e v) :
    ∀ e : Fin (d + 1) →₀ ℕ, e 0 ≤ n →
      coeff e (formalRightHandSide a b u) = coeff e (formalRightHandSide a b v) := by
  let s : Set (Fin (d + 1) →₀ ℕ) := {e | e 0 ≤ n}
  have hs : ∀ ⦃e⦄, e ∈ s → ∀ ⦃f⦄, f ≤ e → f ∈ s :=
    fun _ he _ hf ↦ (hf 0).trans he
  have hderiv (t : Multiset (Fin (d + 1))) (ht : t.count 0 < k) :
      Set.EqOn (fun e ↦ coeff e (iteratedPDeriv t u))
        (fun e ↦ coeff e (iteratedPDeriv t v)) s := by
    intro e he
    apply coeff_iteratedPDeriv_eq_of_coordinate_le 0 t
      (n := n + k - 1) (fun f hf ↦ h f (by omega))
    change e 0 ≤ n at he
    omega
  have hargs (j : (Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) :
      Set.EqOn (fun e ↦ coeff e (formalArguments k u j))
        (fun e ↦ coeff e (formalArguments k v j)) s := by
    cases j with
    | inl α =>
      exact hderiv _ ((Multiset.count_le_card 0 _).trans_lt
        (by simpa only [Sym.card_coe] using α.1.isLt))
    | inr i => intro e he; rfl
  have hsubst (f : MvPowerSeries
      ((Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) R) :=
    eqOn_coeff_subst hs hu hv hargs f
  intro e he
  simp only [formalRightHandSide, map_add, map_sum]
  refine congrArg₂ (· + ·) ?_ (hsubst b he)
  apply Finset.sum_congr rfl
  intro α hα
  exact eqOn_coeff_mul hs (hsubst (a α)) (hderiv _ (count_time_lt α)) he

end PDE.Cauchy.Quasilinear.Analytic
