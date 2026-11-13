/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.PolynomialComposition
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Composition of commutative analytic expansions

For an inner map vanishing at the expansion point, analytic composition agrees
with formal substitution. A finite outer Taylor approximation suffices at each
coefficient degree: differentiability makes the inner map of order one, so
composition preserves the Taylor remainder order.
-/

@[expose] public section

open scoped Topology
open Filter Asymptotics

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Analytic composition with a zero-based inner map has the formally substituted
commutative coefficients. The native analytic expansions supply all convergence. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_comp
    {f : (κ → ℝ) → ℝ} {g : (ι → ℝ) → κ → ℝ}
    {p : κ → FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    {q : FormalMultilinearSeries ℝ (κ → ℝ) ℝ}
    {r : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hf : HasFPowerSeriesAt f q 0)
    (hg : ∀ i, HasFPowerSeriesAt (fun x ↦ g x i) (p i) 0) (hg0 : g 0 = 0)
    (hr : HasFPowerSeriesAt (f ∘ g) r 0) :
    r.toMvPowerSeries = q.toMvPowerSeries.subst (fun i ↦ (p i).toMvPowerSeries) := by
  classical
  have hga : AnalyticAt ℝ g 0 := .pi (fun i ↦ (hg i).analyticAt)
  have hgt : Tendsto g (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, hg0] using hga.continuousAt
  have hgO : (fun x ↦ ‖g x‖) =O[𝓝 0] fun x ↦ ‖x‖ := by
    simpa only [hg0, sub_zero] using hga.differentiableAt.isBigO_sub.norm_norm
  have hcc : ∀ i, (p i).toMvPowerSeries.constantCoeff = 0 := by
    intro i
    rw [(hg i).constantCoeff_toMvPowerSeries, hg0, Pi.zero_apply]
  ext a
  let N := a.degree + 1
  let P := q.toMvPowerSeries.truncTotal N
  obtain ⟨s, hs⟩ : AnalyticAt ℝ (fun x ↦ MvPolynomial.eval (g x) P) 0 :=
    AnalyticAt.aeval_mvPolynomial (fun i ↦ (hg i).analyticAt) P
  have he : (fun x ↦ f (g x) - MvPolynomial.eval (g x) P)
      =O[𝓝 0] fun x ↦ ‖x‖ ^ N :=
    ((hf.isBigO_sub_eval_truncTotal_pow N).comp_tendsto hgt).trans (hgO.pow N)
  have hc := congrArg (fun Q : MvPolynomial ι ℝ ↦ Q.coeff a)
    (MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
      (f := q.toMvPowerSeries) (k := N) hcc)
  rw [MvPowerSeries.coeff_truncTotal _ (show a.degree < N from Nat.lt_succ_self _),
    MvPowerSeries.coeff_truncTotal _ (show a.degree < N from Nat.lt_succ_self _),
    MvPowerSeries.subst_coe] at hc
  calc
    MvPowerSeries.coeff a r.toMvPowerSeries = MvPowerSeries.coeff a s.toMvPowerSeries :=
      hr.coeff_eq_of_isBigO_sub hs he a (Nat.lt_succ_self _)
    _ = MvPowerSeries.coeff a
        (MvPolynomial.aeval (fun i ↦ (p i).toMvPowerSeries) P) :=
      congrArg (MvPowerSeries.coeff a) (HasFPowerSeriesAt.toMvPowerSeries_eval_comp hg P hs)
    _ = MvPowerSeries.coeff a
        (q.toMvPowerSeries.subst fun i ↦ (p i).toMvPowerSeries) := hc.symm
