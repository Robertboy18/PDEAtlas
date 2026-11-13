/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Truncation
public import Mathlib.Analysis.Analytic.CPolynomialDef

/-!
# Native expansions of multivariable polynomials

The coefficient inclusion of a polynomial into a formal series gives its native
finite multilinear expansion. Polynomial Taylor approximations therefore have
the expected commutative coefficients.
-/

@[expose] public section

open scoped BigOperators

namespace MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The native homogeneous realization of a polynomial vanishes above its total degree. -/
theorem toFormalMultilinearSeries_eq_zero_of_totalDegree_lt (P : MvPolynomial ι ℝ)
    {n : ℕ} (hn : P.totalDegree < n) :
    P.toMvPowerSeries.toFormalMultilinearSeries n = 0 := by
  classical
  change (∑ s : Sym ι n, ContinuousMultilinearMap.symMonomial s
    (P.coeff (s : Multiset ι).toFinsupp)) = 0
  apply Finset.sum_eq_zero
  intro s hs
  have hc : P.coeff (s : Multiset ι).toFinsupp = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    change P.totalDegree < (s : Multiset ι).toFinsupp.sum (fun _ ↦ id)
    simpa only [Multiset.toFinsupp_sum_eq, Sym.card_coe] using hn
  rw [hc]
  ext v
  simp [ContinuousMultilinearMap.symMonomial, ContinuousMultilinearMap.coordinateMonomial]

/-- Coefficient inclusion realizes a polynomial as a finite native power series
on the whole space. -/
theorem hasFiniteFPowerSeriesOnBall_eval (P : MvPolynomial ι ℝ) :
    HasFiniteFPowerSeriesOnBall (fun x ↦ eval x P)
      P.toMvPowerSeries.toFormalMultilinearSeries 0 (P.totalDegree + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk'
    (fun n hn ↦ P.toFormalMultilinearSeries_eq_zero_of_totalDegree_lt
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hn)) (by simp)
  intro x hx
  change P.toMvPowerSeries.toFormalMultilinearSeries.partialSum (P.totalDegree + 1) x = _
  rw [← MvPowerSeries.eval_truncTotal]
  rw [(MvPowerSeries.truncTotal_coe_eq_self_iff P (Nat.succ_ne_zero _)).mpr
    (Nat.lt_succ_self _), zero_add]

end MvPolynomial
