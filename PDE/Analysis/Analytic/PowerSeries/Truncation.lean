/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Convergence
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Polynomial truncations of native coordinate expansions

The total-degree truncation of a commutative formal series evaluates to the
partial sum of its native multilinear realization. Polynomial extensionality
then recovers formal coefficients from homogeneous diagonal values.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace MvPolynomial

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- Grouping monomials by symmetric powers selects precisely one total degree. -/
theorem coeff_sum_monomial_sym (f : (ι →₀ ℕ) → R) (n : ℕ) (a : ι →₀ ℕ) :
    (∑ s : Sym ι n, monomial (s : Multiset ι).toFinsupp
      (f (s : Multiset ι).toFinsupp)).coeff a =
      if a.sum (fun _ ↦ id) = n then f a else 0 := by
  classical
  rw [coeff_sum]
  by_cases ha : a.sum (fun _ ↦ id) = n
  · let s := (Sym.equivNatSum ι n).symm ⟨a, ha⟩
    have hs : (s : Multiset ι).toFinsupp = a := by simp [s]
    rw [Finset.sum_eq_single s]
    · simp [hs, ha]
    · intro b hb hbs
      have hba : (b : Multiset ι).toFinsupp ≠ a := by
        intro h
        apply hbs
        apply (Sym.equivNatSum ι n).injective
        apply Subtype.ext
        exact h.trans hs.symm
      simp [coeff_monomial, hba]
    · simp
  · rw [ite_eq_right ha]
    apply Finset.sum_eq_zero
    intro s hs
    have hsa : (s : Multiset ι).toFinsupp ≠ a := by
      intro h
      apply ha
      rw [← h]
      simp
    simp [coeff_monomial, hsa]

end MvPolynomial

namespace MvPowerSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Total-degree truncation is the finite sum over coordinate multisets. -/
theorem truncTotal_eq_sum_sym {R : Type*} [CommSemiring R]
    (f : MvPowerSeries ι R) (N : ℕ) :
    f.truncTotal N = ∑ n ∈ Finset.range N, ∑ s : Sym ι n,
      MvPolynomial.monomial (s : Multiset ι).toFinsupp (coeff (s : Multiset ι).toFinsupp f) := by
  ext a
  have hc (n : ℕ) :
      (∑ s : Sym ι n, (MvPolynomial.monomial (s : Multiset ι).toFinsupp
        (coeff (s : Multiset ι).toFinsupp f)).coeff a) =
        if a.sum (fun _ ↦ id) = n then coeff a f else 0 := by
    simpa only [MvPolynomial.coeff_sum] using
      MvPolynomial.coeff_sum_monomial_sym (fun a ↦ coeff a f) n a
  simp only [MvPolynomial.coeff_sum, hc, Finset.sum_ite_eq, Finset.mem_range]
  exact coeff_truncTotal_eq_ite f

/-- Polynomial evaluation of a truncation is the native analytic partial sum. -/
theorem eval_truncTotal (f : MvPowerSeries ι ℝ) (N : ℕ) (x : ι → ℝ) :
    MvPolynomial.eval x (f.truncTotal N) = f.toFormalMultilinearSeries.partialSum N x := by
  rw [truncTotal_eq_sum_sym]
  simp only [map_sum, FormalMultilinearSeries.partialSum, toFormalMultilinearSeries,
    FormalMultilinearSeries.ofMultiindexCoefficients_apply, MvPolynomial.eval_monomial,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro s hs
  have hprod : ((s : Multiset ι).map x).prod =
      (s : Multiset ι).toFinsupp.prod (fun i n ↦ x i ^ n) := by
    conv_lhs => rw [← Multiset.toFinsupp_toMultiset (s : Multiset ι)]
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun i ↦ pow_zero _) (fun i a b ↦ pow_add _ _ _)]
  rw [hprod, mul_comm]

/-- Homogeneous diagonal values determine a real commutative formal series. -/
theorem ext_of_toFormalMultilinearSeries_apply {f g : MvPowerSeries ι ℝ}
    (h : ∀ n x, f.toFormalMultilinearSeries n (fun _ ↦ x) =
      g.toFormalMultilinearSeries n (fun _ ↦ x)) : f = g := by
  ext a
  have ht (N : ℕ) : f.truncTotal N = g.truncTotal N := by
    apply MvPolynomial.funext
    intro x
    simp only [eval_truncTotal, FormalMultilinearSeries.partialSum]
    exact Finset.sum_congr rfl fun n hn ↦ h n x
  have hc := congrArg (fun p : MvPolynomial ι ℝ ↦ p.coeff a) (ht (a.degree + 1))
  simpa only [coeff_truncTotal _ (Nat.lt_succ_self _)] using hc

end MvPowerSeries
