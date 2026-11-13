/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Trace
public import PDE.Analytic.CauchyKovalevskaya.Majorant.Convergence
public import PDE.Analytic.CauchyKovalevskaya.Solution.Equation

/-!
# Analytic existence for the reduced Cauchy system

The convergent formal solution sums to an analytic function. Taking power series
commutes with products, substitution, and differentiation, so the formal equation
gives the PDE on a ball of positive radius. The initial condition holds on a
spatial ball, not only at its center.

`exists_analytic_solution_zero` is the Cauchy–Kovalevskaya theorem for the reduced
system, Evans, §4.6.3, Theorem 2: analytic coefficients and zero initial data give an
analytic solution near the origin. One radius serves for analyticity, the equation, and
the initial trace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Topology
open Filter

namespace PDE.Analytic.CauchyKovalevskaya

/-- A reduced coupled analytic Cauchy system has an analytic solution with zero
initial data on a ball of positive radius. -/
theorem exists_analytic_solution_zero {d m : ℕ}
    (B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    (c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    (hB : ∀ j i k, AnalyticAt ℝ (B j i k) 0) (hc : ∀ i, AnalyticAt ℝ (c i) 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : (Fin (d + 1) → ℝ) → Fin m → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball (0 : Fin d → ℝ) r, u (Fin.cons 0 x) = 0) ∧
      ∀ x ∈ Metric.ball 0 r, ∀ i,
        fderiv ℝ (fun y ↦ u y i) x (Pi.single 0 1) = rightHandSide B c u i x := by
  choose pB hpB using hB
  choose pc hpc using hc
  obtain ⟨v, hvzero, hveq, hvr⟩ := exists_convergent_formal_solution pB pc
    (fun j i k ↦ (hpB j i k).radius_pos) (fun i ↦ (hpc i).radius_pos)
  let u (x : Fin (d + 1) → ℝ) (i : Fin m) := (v i).toFormalMultilinearSeries.sum x
  have hu (i : Fin m) : HasFPowerSeriesAt (fun x ↦ u x i)
      (v i).toFormalMultilinearSeries 0 :=
    ((v i).toFormalMultilinearSeries.hasFPowerSeriesOnBall (hvr i)).hasFPowerSeriesAt
  have htrace (i : Fin m) : (fun x : Fin d → ℝ ↦ u (Fin.cons 0 x) i) =ᶠ[𝓝 0] 0 :=
    (hu i).eventuallyEq_zero_finCons_iff.mpr (by
      rw [MvPowerSeries.toMvPowerSeries_toFormalMultilinearSeries]
      exact hvzero i)
  have hu0 : u 0 = 0 := by
    funext i
    simpa only [← Matrix.vecCons.eq_1, Matrix.cons_zero_zero, Pi.zero_apply]
      using (htrace i).eq_of_nhds
  have hEq (i : Fin m) :
      (fun x ↦ fderiv ℝ (fun y ↦ u y i) x (Pi.single 0 1))
        =ᶠ[𝓝 0] rightHandSide B c u i := by
    obtain ⟨q, hq⟩ := analyticAt_rightHandSide
      (fun j i k ↦ (hpB j i k).analyticAt) (fun i ↦ (hpc i).analyticAt)
      (fun i ↦ (hu i).analyticAt) hu0 i
    have hd := (hu i).fderiv_apply (Pi.single 0 1)
    apply hd.eventuallyEq_of_toMvPowerSeries_eq hq
    rw [(hu i).toMvPowerSeries_fderiv_apply 0 hd,
      toMvPowerSeries_rightHandSide hpB hpc hu hu0 i hq]
    simp only [MvPowerSeries.toMvPowerSeries_toFormalMultilinearSeries]
    exact hveq i
  have hua : AnalyticAt ℝ u 0 := AnalyticAt.pi fun i ↦ (hu i).analyticAt
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.mem_nhds_iff.mp
    (hua.eventually_analyticAt.and (eventually_all.mpr hEq))
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.mem_nhds_iff.mp (eventually_all.mpr htrace)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, u, ?_, ?_, ?_⟩
  · intro x hx
    exact (h₁ (Metric.ball_subset_ball (min_le_left _ _) hx)).1
  · intro x hx
    funext i
    exact h₂ (Metric.ball_subset_ball (min_le_right _ _) hx) i
  · intro x hx i
    exact (h₁ (Metric.ball_subset_ball (min_le_left _ _) hx)).2 i

end PDE.Analytic.CauchyKovalevskaya
