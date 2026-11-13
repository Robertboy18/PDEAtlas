/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Majorization
public import PDE.Analytic.CauchyKovalevskaya.Formal.Recursion

/-!
# Coefficient comparison for a Cauchy system

Comparison is by time degree, retaining every spatial coefficient at each step.
Spatial differentiation therefore stays inside the induction hypothesis. The
majorizing system needs no separate positivity hypothesis: nonnegativity of the
coefficients of its solution follows from the comparison. This is step 5 of the proof of
Evans, §4.6.3, Theorem 2, which ends with `u* ≫ u` in (32).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, proof of Theorem 2, (26)-(32).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MvPowerSeries
open scoped BigOperators

namespace PDE.Analytic.CauchyKovalevskaya

variable {d m : ℕ}
  {B D : Fin d → Fin m → Fin m → MvPowerSeries (Fin m ⊕ Fin d) ℝ}
  {c e : Fin m → MvPowerSeries (Fin m ⊕ Fin d) ℝ}
  {u v : Fin m → MvPowerSeries (Fin (d + 1)) ℝ}

/-- A majorized state gives a majorized right-hand side through the same time degree. -/
theorem formalRightHandSide_isMajorizedOn {n : ℕ}
    (hu : HasSubst (formalArguments u)) (hv : HasSubst (formalArguments v))
    (hB : ∀ j i k, IsMajorizedOn (B j i k) (D j i k) Set.univ)
    (hc : ∀ i, IsMajorizedOn (c i) (e i) Set.univ)
    (h : ∀ i, IsMajorizedOn (u i) (v i) {a | a 0 ≤ n}) :
    ∀ i, IsMajorizedOn (formalRightHandSide B c u i)
      (formalRightHandSide D e v i) {a | a 0 ≤ n} := by
  let s : Set (Fin (d + 1) →₀ ℕ) := {a | a 0 ≤ n}
  have hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s :=
    fun _ ha _ hb ↦ (hb 0).trans ha
  have hshift (j : Fin d) (a : Fin (d + 1) →₀ ℕ) (ha : a ∈ s) :
      a + Finsupp.single j.succ 1 ∈ s := by
    change (a + Finsupp.single j.succ 1 : Fin (d + 1) →₀ ℕ) 0 ≤ n
    change a 0 ≤ n at ha
    simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne (Fin.succ_ne_zero j).symm,
      add_zero] using ha
  have hargs (j : Fin m ⊕ Fin d) :
      IsMajorizedOn (formalArguments u j) (formalArguments v j) s := by
    cases j with
    | inl i => exact h i
    | inr j =>
      intro a ha
      change ‖coeff a (X j.succ : MvPowerSeries (Fin (d + 1)) ℝ)‖ ≤ coeff a (X j.succ)
      classical
      simp only [coeff_X]
      split_ifs <;> simp
  intro i
  apply IsMajorizedOn.add
  · apply IsMajorizedOn.sum
    intro j hj
    apply IsMajorizedOn.sum
    intro k hk
    apply IsMajorizedOn.mul hs (IsMajorizedOn.subst hs hu hv hargs (hB j i k))
    exact (h k).pderiv j.succ (hshift j)
  · exact IsMajorizedOn.subst hs hu hv hargs (hc i)

/-- Coefficientwise majorants of the data majorize the complete formal Cauchy solution.
Only the equations and zero initial traces are needed for the two formal solutions. -/
theorem formal_solution_isMajorizedOn
    (hu₀ : ∀ i, PowerSeries.constantCoeff (finSuccEquiv ℝ d (u i)) = 0)
    (hv₀ : ∀ i, PowerSeries.constantCoeff (finSuccEquiv ℝ d (v i)) = 0)
    (hu : ∀ i, pderiv 0 (u i) = formalRightHandSide B c u i)
    (hv : ∀ i, pderiv 0 (v i) = formalRightHandSide D e v i)
    (hB : ∀ j i k, IsMajorizedOn (B j i k) (D j i k) Set.univ)
    (hc : ∀ i, IsMajorizedOn (c i) (e i) Set.univ) :
    ∀ i, IsMajorizedOn (u i) (v i) Set.univ := by
  have hzero (w : Fin m → MvPowerSeries (Fin (d + 1)) ℝ)
      (hw : ∀ i, PowerSeries.constantCoeff (finSuccEquiv ℝ d (w i)) = 0)
      (i : Fin m) (a : Fin (d + 1) →₀ ℕ) (ha : a 0 = 0) :
      coeff a (w i) = 0 := by
    have hz := congrArg (coeff a.tail) (hw i)
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeff_finSuccEquiv] at hz
    simpa only [← ha, Finsupp.cons_tail, map_zero] using hz
  have hbound (n : ℕ) : ∀ i, IsMajorizedOn (u i) (v i) {a | a 0 ≤ n} := by
    induction n with
    | zero =>
      intro i a ha
      have ha₀ : a 0 = 0 := Nat.eq_zero_of_le_zero ha
      rw [hzero u hu₀ i a ha₀, hzero v hv₀ i a ha₀, norm_zero]
    | succ n ih =>
      have hR := formalRightHandSide_isMajorizedOn
        (hasSubst_formalArguments hu₀) (hasSubst_formalArguments hv₀) hB hc ih
      intro i a ha
      by_cases han : a 0 ≤ n
      · exact ih i a han
      have haeq : a 0 = n + 1 := Nat.le_antisymm ha (Nat.lt_of_not_ge han)
      let b := a.tail.cons n
      have hb : b 0 = n := by simp [b]
      have hba : b + Finsupp.single 0 1 = a := by
        ext j
        refine Fin.cases ?_ (fun j ↦ ?_) j
        · simp [hb, haeq]
        · simp [b, Finsupp.tail_apply]
      have hRi := hR i b (le_of_eq hb)
      rw [← hu i, ← hv i, coeff_pderiv, coeff_pderiv, hba, hb] at hRi
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [norm_mul, Real.norm_of_nonneg hn.le] at hRi
      exact (mul_le_mul_iff_of_pos_right hn).mp hRi
  intro i a ha
  exact hbound (a 0) i a (show a 0 ≤ a 0 from le_rfl)

end PDE.Analytic.CauchyKovalevskaya
