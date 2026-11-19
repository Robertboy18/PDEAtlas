/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.CoefficientUniqueness
public import PDE.Analysis.Analytic.PowerSeries.PolynomialExpansion
import Mathlib.Analysis.Analytic.Constructions

/-!
# Polynomial approximation and analytic coefficients

A remainder of order `N` identifies the commutative Taylor coefficients below
degree `N`. Native analytic expansions therefore admit polynomial approximations
given by truncation of their commutative coefficients.
-/

@[expose] public section

open scoped Topology
open Filter Asymptotics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An analytic difference of order `N` has equal coefficients below degree `N`. -/
theorem HasFPowerSeriesAt.coeff_eq_of_isBigO_sub
    {f g : (ι → ℝ) → ℝ} {p q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt g q 0) {N : ℕ}
    (hfg : (fun x ↦ f x - g x) =O[𝓝 0] fun x ↦ ‖x‖ ^ N)
    (a : ι →₀ ℕ) (ha : a.sum (fun _ ↦ id) < N) :
    MvPowerSeries.coeff a p.toMvPowerSeries = MvPowerSeries.coeff a q.toMvPowerSeries := by
  have hc := (hp.sub hq).multiindexCoeff_eq_zero_of_isBigO_norm_pow hfg a ha
  change MvPowerSeries.coeff a (p - q).toMvPowerSeries = 0 at hc
  rw [FormalMultilinearSeries.toMvPowerSeries_sub, map_sub] at hc
  exact sub_eq_zero.mp hc

/-- A polynomial approximation determines all Taylor coefficients below the error order. -/
theorem HasFPowerSeriesAt.coeff_eq_of_isBigO_sub_eval
    {f : (ι → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0) (P : MvPolynomial ι ℝ) {N : ℕ}
    (hf : (fun x ↦ f x - MvPolynomial.eval x P) =O[𝓝 0] fun x ↦ ‖x‖ ^ N)
    (a : ι →₀ ℕ) (ha : a.sum (fun _ ↦ id) < N) :
    MvPowerSeries.coeff a p.toMvPowerSeries = P.coeff a := by
  have hP := P.hasFiniteFPowerSeriesOnBall_eval.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
  simpa only [MvPowerSeries.toMvPowerSeries_toFormalMultilinearSeries,
    MvPolynomial.coeff_coe] using hp.coeff_eq_of_isBigO_sub hP hf a ha

/-- Truncating commutative coefficients gives a polynomial Taylor approximation
with the native analytic remainder estimate. -/
theorem HasFPowerSeriesAt.isBigO_sub_eval_truncTotal_pow
    {f : (ι → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0) (N : ℕ) :
    (fun x ↦ f x - MvPolynomial.eval x (p.toMvPowerSeries.truncTotal N))
      =O[𝓝 0] fun x ↦ ‖x‖ ^ N := by
  simp_rw [MvPowerSeries.eval_truncTotal]
  have heq : p.toMvPowerSeries.toFormalMultilinearSeries =
      FormalMultilinearSeries.ofMultiindexCoefficients p.multiindexCoeff := rfl
  rw [heq]
  simpa only [zero_add] using hp.ofMultiindexCoefficients.isBigO_sub_partialSum_pow N
