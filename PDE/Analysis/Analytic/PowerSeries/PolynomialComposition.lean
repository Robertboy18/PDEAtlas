/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Multiplication
public import Mathlib.Analysis.Analytic.Polynomial

/-!
# Polynomial operations on analytic coefficients

Extracting commutative Taylor coefficients commutes with finite polynomial
operations on analytic functions.
-/

@[expose] public section

open scoped Topology
open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant commutative coefficient is the value at the expansion point. -/
theorem HasFPowerSeriesAt.constantCoeff_toMvPowerSeries
    {f : (ι → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    {x : ι → ℝ} (hp : HasFPowerSeriesAt f p x) :
    p.toMvPowerSeries.constantCoeff = f x := by
  have hc := hp.ofMultiindexCoefficients.coeff_zero (fun _ ↦ 1)
  change p.toMvPowerSeries.toFormalMultilinearSeries 0 (fun _ ↦ 1) = f x at hc
  simpa [MvPowerSeries.toFormalMultilinearSeries_apply_one,
    Sym.eq_nil_of_card_zero (default : Sym ι 0)] using hc

/-- Equal commutative coefficients determine the same analytic germ. -/
theorem HasFPowerSeriesAt.eventuallyEq_of_toMvPowerSeries_eq
    {f g : (ι → ℝ) → ℝ} {p q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    {x : ι → ℝ} (hp : HasFPowerSeriesAt f p x) (hq : HasFPowerSeriesAt g q x)
    (hpq : p.toMvPowerSeries = q.toMvPowerSeries) : f =ᶠ[𝓝 x] g := by
  have hp' : HasFPowerSeriesAt f p.toMvPowerSeries.toFormalMultilinearSeries x :=
    hp.ofMultiindexCoefficients
  have hq' : HasFPowerSeriesAt g p.toMvPowerSeries.toFormalMultilinearSeries x := by
    rw [hpq]
    exact hq.ofMultiindexCoefficients
  filter_upwards [hp'.eventually_hasSum_sub, hq'.eventually_hasSum_sub] with y hfy hgy
  exact hfy.unique hgy

/-- Commutative coefficient extraction preserves addition. -/
theorem FormalMultilinearSeries.toMvPowerSeries_add
    (p q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) :
    (p + q).toMvPowerSeries = p.toMvPowerSeries + q.toMvPowerSeries := by
  ext a
  change (p + q).multiindexCoeff a = p.multiindexCoeff a + q.multiindexCoeff a
  simp only [multiindexCoeff, ContinuousMultilinearMap.symCoefficient,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> simp

/-- Coefficients of an analytic sum are the sums of the coefficients. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_add
    {f g : (ι → ℝ) → ℝ} {p q r : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt g q 0)
    (hr : HasFPowerSeriesAt (f + g) r 0) :
    r.toMvPowerSeries = p.toMvPowerSeries + q.toMvPowerSeries :=
  (hr.toMvPowerSeries_eq (hp.add hq) EventuallyEq.rfl).trans
    (FormalMultilinearSeries.toMvPowerSeries_add p q)

/-- Every native expansion of a polynomial has its usual polynomial coefficients. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_eval (P : MvPolynomial ι ℝ)
    {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt (fun x ↦ MvPolynomial.eval x P) p 0) :
    p.toMvPowerSeries = P.toMvPowerSeries := by
  simpa only [MvPowerSeries.toMvPowerSeries_toFormalMultilinearSeries] using
    hp.toMvPowerSeries_eq
      P.hasFiniteFPowerSeriesOnBall_eval.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
      EventuallyEq.rfl

/-- Polynomial substitution in analytic functions agrees with substitution in their
commutative Taylor coefficients. No zero constant-term hypothesis is needed here. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_eval_comp
    {κ : Type*} {g : (ι → ℝ) → κ → ℝ}
    {p : κ → FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : ∀ i, HasFPowerSeriesAt (fun x ↦ g x i) (p i) 0)
    (P : MvPolynomial κ ℝ) {r : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hr : HasFPowerSeriesAt (fun x ↦ MvPolynomial.eval (g x) P) r 0) :
    r.toMvPowerSeries = MvPolynomial.aeval (fun i ↦ (p i).toMvPowerSeries) P := by
  classical
  have hpoly (Q : MvPolynomial κ ℝ) :
      AnalyticAt ℝ (fun x ↦ MvPolynomial.eval (g x) Q) 0 :=
    AnalyticAt.aeval_mvPolynomial (fun i ↦ (hp i).analyticAt) Q
  induction P using MvPolynomial.induction_on generalizing r with
  | C c =>
    have hc : HasFPowerSeriesAt
        (fun x ↦ MvPolynomial.eval x (MvPolynomial.C c : MvPolynomial ι ℝ)) r 0 := by
      simpa only [MvPolynomial.eval_C] using hr
    simpa only [MvPolynomial.aeval_C, MvPolynomial.coe_C,
      ← MvPowerSeries.c_eq_algebraMap] using
      HasFPowerSeriesAt.toMvPowerSeries_eval (MvPolynomial.C c : MvPolynomial ι ℝ) hc
  | add P Q hP hQ =>
    obtain ⟨pP, hpP⟩ := hpoly P
    obtain ⟨pQ, hpQ⟩ := hpoly Q
    have hs := hpP.toMvPowerSeries_add hpQ
      (show HasFPowerSeriesAt
        ((fun x ↦ MvPolynomial.eval (g x) P) + fun x ↦ MvPolynomial.eval (g x) Q) r 0 by
        simpa only [MvPolynomial.eval_add] using! hr)
    rw [hs, hP hpP, hQ hpQ, map_add]
  | mul_X P j hP =>
    obtain ⟨pP, hpP⟩ := hpoly P
    have hm := hpP.toMvPowerSeries_mul (hp j)
      (show HasFPowerSeriesAt
        ((fun x ↦ MvPolynomial.eval (g x) P) * fun x ↦ g x j) r 0 by
        simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using! hr)
    rw [hm, hP hpP, map_mul, MvPolynomial.aeval_X]
