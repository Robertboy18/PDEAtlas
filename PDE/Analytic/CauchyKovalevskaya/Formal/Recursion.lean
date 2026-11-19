/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Filtration
public import PDE.Analysis.Analytic.PowerSeries.Recursion.Derivatives
public import PDE.Notation.PowerSeries

/-!
# Formal coefficients for a first-order Cauchy system

The first coordinate is time. Coefficients of the equation are formal series in
the state and the spatial coordinates. Substitution is admissible for an unknown
with zero initial trace, and the right-hand side preserves agreement through
each time degree, including all spatial coefficients.

The time recursion `existsUnique_iterate_pderiv_eq_of_coeff_depend_lt` is stated for
any order and any index type. The first-order system uses it with order one, and the
scalar equation of order `k` in `PDE.Cauchy.Formal.Recursion` uses it with one unknown.
For the first-order system this is the computation of the Taylor coefficients in steps 1-3
of the proof of Evans, §4.6.3, Theorem 2, (18)-(25).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, proof of Theorem 2, (18)-(25).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MvPowerSeries
open scoped BigOperators MvPowerSeries

noncomputable section

namespace PDE.Analytic.CauchyKovalevskaya

variable {d m : ℕ} {R : Type*} [CommRing R]

/-- Substitute the state series and retain the original spatial coordinate variables. -/
def formalArguments (u : Fin m → MvPowerSeries (Fin (d + 1)) R) :
    Fin m ⊕ Fin d → MvPowerSeries (Fin (d + 1)) R :=
  Sum.elim u (fun j ↦ X j.succ)

/-- The formal right-hand side of the reduced coupled first-order system. -/
def formalRightHandSide
    (B : Fin d → Fin m → Fin m → MvPowerSeries (Fin m ⊕ Fin d) R)
    (c : Fin m → MvPowerSeries (Fin m ⊕ Fin d) R)
    (u : Fin m → MvPowerSeries (Fin (d + 1)) R) (i : Fin m) :
    MvPowerSeries (Fin (d + 1)) R :=
  (∑ j, ∑ k, subst (formalArguments u) (B j i k) * pderiv j.succ (u k)) +
    subst (formalArguments u) (c i)

/-- A zero spatial trace at time zero makes substitution into the coefficient series admissible. -/
theorem hasSubst_formalArguments
    {u : Fin m → MvPowerSeries (Fin (d + 1)) R}
    (hu : ∀ i, PowerSeries.constantCoeff (finSuccEquiv R d (u i)) = 0) :
    HasSubst (formalArguments u) := by
  apply hasSubst_of_constantCoeff_zero
  intro j
  cases j with
  | inl i =>
    change constantCoeff (u i) = 0
    have h := congrArg (coeff (0 : Fin d →₀ ℕ)) (hu i)
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_coeff_finSuccEquiv, Finsupp.cons_zero_zero] at h
    simpa only [coeff_zero_eq_constantCoeff_apply, map_zero] using h
  | inr j => simp [formalArguments]

/-- The nonlinear right-hand side through time degree `n` uses no later time coefficient. -/
theorem coeff_formalRightHandSide_eq
    (B : Fin d → Fin m → Fin m → MvPowerSeries (Fin m ⊕ Fin d) R)
    (c : Fin m → MvPowerSeries (Fin m ⊕ Fin d) R)
    {u v : Fin m → MvPowerSeries (Fin (d + 1)) R} {n : ℕ}
    (hu : HasSubst (formalArguments u)) (hv : HasSubst (formalArguments v))
    (h : ∀ i a, a 0 ≤ n → [X^a] (u i) = [X^a] (v i)) :
    ∀ i a, a 0 ≤ n →
      [X^a] (formalRightHandSide B c u i) = [X^a] (formalRightHandSide B c v i) := by
  let s : Set (Fin (d + 1) →₀ ℕ) := {a | a 0 ≤ n}
  have hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s :=
    fun _ ha _ hb ↦ (hb 0).trans ha
  have hargs (j : Fin m ⊕ Fin d) :
      Set.EqOn (fun a ↦ coeff a (formalArguments u j))
        (fun a ↦ coeff a (formalArguments v j)) s := by
    cases j with
    | inl i => exact h i
    | inr j => intro a ha; rfl
  have hsubst (f : MvPowerSeries (Fin m ⊕ Fin d) R) :=
    eqOn_coeff_subst hs hu hv hargs f
  intro i a ha
  simp only [formalRightHandSide, map_add, map_sum]
  refine congrArg₂ (· + ·) ?_ (hsubst (c i) ha)
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact eqOn_coeff_mul hs (hsubst (B j i k))
    (coeff_pderiv_eq_of_coordinate_eq (Fin.succ_ne_zero j) (h k)) ha

variable [Algebra ℚ R]

/-- A time-causal formal system of order `k` has a unique solution whose first `k` time
coefficients vanish. The right-hand side only has to respect agreement of time coefficients
between unknowns with this vanishing initial data, which is where substitution into the
coefficient series is admissible. -/
theorem existsUnique_iterate_pderiv_eq_of_coeff_depend_lt {ι : Type*} (k : ℕ)
    (G : (ι → MvPowerSeries (Fin (d + 1)) R) → ι → MvPowerSeries (Fin (d + 1)) R)
    (hG : ∀ n u v,
      (∀ i, ∀ j < k, PowerSeries.coeff j (finSuccEquiv R d (u i)) = 0) →
      (∀ i, ∀ j < k, PowerSeries.coeff j (finSuccEquiv R d (v i)) = 0) →
      (∀ i a, a 0 < n + k → coeff a (u i) = coeff a (v i)) →
        ∀ i a, a 0 ≤ n → coeff a (G u i) = coeff a (G v i)) :
    ∃! u : ι → MvPowerSeries (Fin (d + 1)) R,
      (∀ i, ∀ j < k, PowerSeries.coeff j (finSuccEquiv R d (u i)) = 0) ∧
        ∀ i, (pderiv 0)^[k] (u i) = G u i := by
  classical
  let e := finSuccEquiv R d
  -- Removing the initial coefficients makes the right-hand side well behaved for every
  -- argument of the recursion, before the vanishing initial data has been proved.
  let lift (u : PowerSeries (MvPowerSeries (Fin d) R)) : MvPowerSeries (Fin (d + 1)) R :=
    e.symm (PowerSeries.mk fun n ↦ if n < k then 0 else PowerSeries.coeff n u)
  have hlift (u : PowerSeries (MvPowerSeries (Fin d) R)) :
      ∀ j < k, PowerSeries.coeff j (e (lift u)) = 0 := by
    intro j hj
    simp [lift, hj]
  have hlift_coeff (u : PowerSeries (MvPowerSeries (Fin d) R)) (a : Fin (d + 1) →₀ ℕ) :
      coeff a (lift u) =
        if a 0 < k then 0 else coeff a.tail (PowerSeries.coeff (a 0) u) := by
    have h := coeff_coeff_finSuccEquiv (lift u) (k := a 0) (x := a.tail)
    rw [Finsupp.cons_tail] at h
    rw [← h]
    simp only [lift, e, AlgEquiv.apply_symm_apply, PowerSeries.coeff_mk]
    split <;> simp_all only [map_zero]
  let F (u : ι → PowerSeries (MvPowerSeries (Fin d) R)) (i : ι) :=
    e (G (fun l ↦ lift (u l)) i)
  have hF (n : ℕ) (u v : ι → PowerSeries (MvPowerSeries (Fin d) R))
      (h : ∀ i j, j < n + k → PowerSeries.coeff j (u i) = PowerSeries.coeff j (v i)) :
      ∀ i, PowerSeries.coeff n (F u i) = PowerSeries.coeff n (F v i) := by
    intro i
    apply ext
    intro a
    change coeff a (PowerSeries.coeff n (finSuccEquiv R d _)) = _
    rw [coeff_coeff_finSuccEquiv, coeff_coeff_finSuccEquiv]
    apply hG n _ _ (fun l ↦ hlift (u l)) (fun l ↦ hlift (v l))
    · intro l b hb
      rw [hlift_coeff, hlift_coeff, h l (b 0) hb]
    · simp only [Finsupp.cons_zero, le_refl]
  obtain ⟨u, hu, huniq⟩ :=
    PowerSeries.existsUnique_iterate_derivative_eq_of_coeff_depend_lt k F (fun _ _ ↦ 0) hF
  have hlift_of_zero (v : PowerSeries (MvPowerSeries (Fin d) R))
      (hv : ∀ j < k, PowerSeries.coeff j v = 0) : lift v = e.symm v := by
    apply congrArg e.symm
    apply PowerSeries.ext
    intro j
    simp only [PowerSeries.coeff_mk]
    split
    · exact (hv j ‹j < k›).symm
    · rfl
  have hD : Function.Semiconj e (pderiv 0) PowerSeries.derivative :=
    finSuccEquiv_pderiv_zero
  let z (i : ι) : MvPowerSeries (Fin (d + 1)) R := e.symm (u i)
  have huzero (i : ι) : ∀ j < k, PowerSeries.coeff j (u i) = 0 :=
    fun j hj ↦ hu.1 i ⟨j, hj⟩
  have hz : (fun l ↦ lift (u l)) = z := funext fun l ↦ hlift_of_zero (u l) (huzero l)
  refine ⟨z, ⟨fun i j hj ↦ ?_, fun i ↦ ?_⟩, ?_⟩
  · change PowerSeries.coeff j (e (e.symm (u i))) = 0
    simpa only [e.apply_symm_apply] using huzero i j hj
  · apply e.injective
    rw [hD.iterate_right k]
    change PowerSeries.derivative^[k] (e (e.symm (u i))) = _
    rw [e.apply_symm_apply, hu.2 i]
    change e (G (fun l ↦ lift (u l)) i) = _
    rw [hz]
  · intro w hw
    let v (i : ι) : PowerSeries (MvPowerSeries (Fin d) R) := e (w i)
    have hvlift : (fun l ↦ lift (v l)) = w := by
      funext l
      rw [hlift_of_zero (v l) (hw.1 l)]
      exact e.symm_apply_apply (w l)
    have hvderiv (i : ι) : PowerSeries.derivative^[k] (v i) = F v i := by
      change PowerSeries.derivative^[k] (e (w i)) = _
      rw [← hD.iterate_right k, hw.2 i]
      change e (G w i) = e (G (fun l ↦ lift (v l)) i)
      rw [hvlift]
    have hv := huniq v ⟨fun i j ↦ hw.1 i j j.isLt, hvderiv⟩
    funext i
    apply e.injective
    simpa only [v, z, e.apply_symm_apply] using congrFun hv i

/-- A reduced coupled first-order system has a unique formal solution with zero initial trace.
Recursion takes place in time, so spatial differentiation does not introduce a circular
dependence among the coefficients being defined. -/
theorem existsUnique_formal_solution
    (B : Fin d → Fin m → Fin m → MvPowerSeries (Fin m ⊕ Fin d) R)
    (c : Fin m → MvPowerSeries (Fin m ⊕ Fin d) R) :
    ∃! u : Fin m → MvPowerSeries (Fin (d + 1)) R,
      (∀ i, PowerSeries.constantCoeff (finSuccEquiv R d (u i)) = 0) ∧
        ∀ i, pderiv 0 (u i) = formalRightHandSide B c u i := by
  have hzero (u : Fin m → MvPowerSeries (Fin (d + 1)) R) :
      (∀ i, ∀ j < 1, PowerSeries.coeff j (finSuccEquiv R d (u i)) = 0) ↔
        ∀ i, PowerSeries.constantCoeff (finSuccEquiv R d (u i)) = 0 := by
    simp only [Nat.lt_one_iff, forall_eq, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  obtain ⟨u, hu, huniq⟩ := existsUnique_iterate_pderiv_eq_of_coeff_depend_lt 1
    (formalRightHandSide B c) fun n u v hu hv h ↦
      coeff_formalRightHandSide_eq B c (hasSubst_formalArguments ((hzero u).mp hu))
        (hasSubst_formalArguments ((hzero v).mp hv)) fun i a ha ↦ h i a (Nat.lt_succ_of_le ha)
  exact ⟨u, ⟨(hzero u).mp hu.1, hu.2⟩, fun w hw ↦ huniq w ⟨(hzero w).mpr hw.1, hw.2⟩⟩

end PDE.Analytic.CauchyKovalevskaya
