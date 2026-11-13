/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.PolynomialComposition
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Analytic trace on a coordinate hyperplane

Restricting the first coordinate to zero retains exactly the time-constant
coefficient, as a full formal series in the remaining variables. Finite Taylor
approximations identify this restriction without an interchange of infinite sums.
-/

@[expose] public section

open scoped Topology
open Filter Asymptotics

variable {d : ℕ}

namespace PDE

/-- The zero-first-coordinate inclusion is analytic, including in zero spatial dimension. -/
theorem analyticAt_finCons_zero (x : Fin d → ℝ) :
    AnalyticAt ℝ (fun y : Fin d → ℝ ↦ (Fin.cons 0 y : Fin (d + 1) → ℝ)) x := by
  apply AnalyticAt.pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using analyticAt_const (𝕜 := ℝ) (x := x) (v := (0 : ℝ))
  · simpa only [Fin.cons_succ] using!
      (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt x

end PDE

/-- Restricting an analytic expansion to the first coordinate hyperplane extracts
the constant coefficient of its time-series presentation. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_finCons_zero
    {f : (Fin (d + 1) → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
    {q : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0)
    (hq : HasFPowerSeriesAt (fun x ↦ f (Fin.cons 0 x)) q 0) :
    q.toMvPowerSeries =
      PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv ℝ d p.toMvPowerSeries) := by
  have hga := PDE.analyticAt_finCons_zero (0 : Fin d → ℝ)
  have hgt : Tendsto (fun x : Fin d → ℝ ↦ (Fin.cons 0 x : Fin (d + 1) → ℝ))
      (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, ← Matrix.vecCons.eq_1, Matrix.cons_zero_zero] using hga.continuousAt
  have hgO : (fun x : Fin d → ℝ ↦ ‖(Fin.cons 0 x : Fin (d + 1) → ℝ)‖)
      =O[𝓝 0] fun x ↦ ‖x‖ := by
    simpa only [← Matrix.vecCons.eq_1, Matrix.cons_zero_zero, sub_zero]
      using hga.differentiableAt.isBigO_sub.norm_norm
  ext a
  let N := a.degree + 1
  let P := p.toMvPowerSeries.truncTotal N
  let Q := (MvPolynomial.finSuccEquiv ℝ d P).coeff 0
  have heval (x : Fin d → ℝ) : MvPolynomial.eval (Fin.cons 0 x) P =
      MvPolynomial.eval x Q := by
    rw [MvPolynomial.eval_eq_eval_mv_eval', ← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_map]
  have he : (fun x ↦ f (Fin.cons 0 x) - MvPolynomial.eval x Q)
      =O[𝓝 0] fun x ↦ ‖x‖ ^ N := by
    have he := ((hp.isBigO_sub_eval_truncTotal_pow N).comp_tendsto hgt).trans (hgO.pow N)
    change (fun x ↦ f (Fin.cons 0 x) - MvPolynomial.eval (Fin.cons 0 x) P)
      =O[𝓝 0] (fun x ↦ ‖x‖ ^ N) at he
    simpa only [heval] using he
  have ha : (a.cons 0).degree < N := by
    change (a.cons 0).sum (fun _ e ↦ e) < a.degree + 1
    rw [Finsupp.sum_cons, zero_add]
    exact Nat.lt_succ_self _
  calc
    MvPowerSeries.coeff a q.toMvPowerSeries = Q.coeff a :=
      hq.coeff_eq_of_isBigO_sub_eval Q he a (Nat.lt_succ_self _)
    _ = MvPowerSeries.coeff (a.cons 0) p.toMvPowerSeries := by
      rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPowerSeries.coeff_truncTotal _ ha]
    _ = MvPowerSeries.coeff a
        (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv ℝ d p.toMvPowerSeries)) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_coeff_finSuccEquiv]

/-- A zero analytic trace is equivalent to vanishing of every spatial coefficient
at time degree zero. The equality is local on the whole initial hyperplane. -/
theorem HasFPowerSeriesAt.eventuallyEq_zero_finCons_iff
    {f : (Fin (d + 1) → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0) :
    (fun x ↦ f (Fin.cons 0 x)) =ᶠ[𝓝 0] 0 ↔
      PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv ℝ d p.toMvPowerSeries) = 0 := by
  obtain ⟨q, hq⟩ : AnalyticAt ℝ (fun x : Fin d → ℝ ↦ f (Fin.cons 0 x)) 0 :=
    hp.analyticAt.comp_of_eq (PDE.analyticAt_finCons_zero 0) Matrix.cons_zero_zero
  have hqcoeff := hp.toMvPowerSeries_finCons_zero hq
  have hzero := (0 : MvPolynomial (Fin d) ℝ).hasFiniteFPowerSeriesOnBall_eval
    |>.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
  constructor
  · intro h
    rw [← hqcoeff, hq.toMvPowerSeries_eq hzero (by simpa using! h)]
    simp only [MvPowerSeries.toMvPowerSeries_toFormalMultilinearSeries, MvPolynomial.coe_zero]
  · intro h
    have heq := hq.eventuallyEq_of_toMvPowerSeries_eq hzero (by
      rw [hqcoeff, h, MvPowerSeries.toMvPowerSeries_toFormalMultilinearSeries,
        MvPolynomial.coe_zero])
    simpa using! heq
