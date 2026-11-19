/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Trace
public import PDE.Analytic.CauchyKovalevskaya.Solution.Equation

/-!
# Analytic germ uniqueness for the reduced Cauchy system

The PDE and the initial trace determine the formal time recursion. Uniqueness
of that recursion, followed by uniqueness of power-series expansions, gives
local uniqueness of analytic solutions. The first step is the observation in
step 4 of the proof of Evans, §4.6.3, Theorem 2, that the equation and the data
determine every derivative of a solution at the origin.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, proof of Theorem 2, steps 3-4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Topology
open Filter

namespace PDE.Analytic.CauchyKovalevskaya

/-- Two analytic solutions of the reduced Cauchy system with zero initial trace
agree on a neighborhood of the origin. The equations and traces are assumed
to hold on neighborhoods of the origin. -/
theorem eventuallyEq_of_analytic_solutions_zero {d m : ℕ}
    {B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    {c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    (hB : ∀ j i k, AnalyticAt ℝ (B j i k) 0) (hc : ∀ i, AnalyticAt ℝ (c i) 0)
    {u v : (Fin (d + 1) → ℝ) → Fin m → ℝ}
    (hu : ∀ i, AnalyticAt ℝ (fun x ↦ u x i) 0)
    (hv : ∀ i, AnalyticAt ℝ (fun x ↦ v x i) 0)
    (hutrace : ∀ i, (fun x : Fin d → ℝ ↦ u (Fin.cons 0 x) i) =ᶠ[𝓝 0] 0)
    (hvtrace : ∀ i, (fun x : Fin d → ℝ ↦ v (Fin.cons 0 x) i) =ᶠ[𝓝 0] 0)
    (hueq : ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ u y i) x (Pi.single 0 1))
      =ᶠ[𝓝 0] rightHandSide B c u i)
    (hveq : ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ v y i) x (Pi.single 0 1))
      =ᶠ[𝓝 0] rightHandSide B c v i) :
    u =ᶠ[𝓝 0] v := by
  choose pB hpB using hB
  choose pc hpc using hc
  choose pu hpu using hu
  choose pv hpv using hv
  have hformal (z : (Fin (d + 1) → ℝ) → Fin m → ℝ)
      (pz : Fin m → FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ)
      (hz : ∀ i, HasFPowerSeriesAt (fun x ↦ z x i) (pz i) 0)
      (hztrace : ∀ i, (fun x : Fin d → ℝ ↦ z (Fin.cons 0 x) i) =ᶠ[𝓝 0] 0)
      (hzeq : ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ z y i) x (Pi.single 0 1))
        =ᶠ[𝓝 0] rightHandSide B c z i) :
      (∀ i, PowerSeries.constantCoeff
        (MvPowerSeries.finSuccEquiv ℝ d (pz i).toMvPowerSeries) = 0) ∧
      ∀ i, MvPowerSeries.pderiv 0 (pz i).toMvPowerSeries = formalRightHandSide
        (fun j i k ↦ (pB j i k).toMvPowerSeries) (fun i ↦ (pc i).toMvPowerSeries)
        (fun i ↦ (pz i).toMvPowerSeries) i := by
    have hz0 : z 0 = 0 := by
      funext i
      simpa only [← Matrix.vecCons.eq_1, Matrix.cons_zero_zero, Pi.zero_apply]
        using (hztrace i).eq_of_nhds
    refine ⟨fun i ↦ (hz i).eventuallyEq_zero_finCons_iff.mp (hztrace i), fun i ↦ ?_⟩
    obtain ⟨q, hq⟩ := analyticAt_rightHandSide
      (fun j i k ↦ (hpB j i k).analyticAt) (fun i ↦ (hpc i).analyticAt)
      (fun i ↦ (hz i).analyticAt) hz0 i
    have hd := (hz i).fderiv_apply (Pi.single 0 1)
    rw [← (hz i).toMvPowerSeries_fderiv_apply 0 hd,
      hd.toMvPowerSeries_eq hq (hzeq i)]
    exact toMvPowerSeries_rightHandSide hpB hpc hz hz0 i hq
  obtain ⟨w, hw, huniq⟩ := existsUnique_formal_solution
    (fun j i k ↦ (pB j i k).toMvPowerSeries) (fun i ↦ (pc i).toMvPowerSeries)
  have hpuw := huniq (fun i ↦ (pu i).toMvPowerSeries) (hformal u pu hpu hutrace hueq)
  have hpvw := huniq (fun i ↦ (pv i).toMvPowerSeries) (hformal v pv hpv hvtrace hveq)
  have hcoeff := hpuw.trans hpvw.symm
  have heq (i : Fin m) : (fun x ↦ u x i) =ᶠ[𝓝 0] fun x ↦ v x i :=
    (hpu i).eventuallyEq_of_toMvPowerSeries_eq (hpv i) (congrFun hcoeff i)
  filter_upwards [eventually_all.mpr heq] with x hx
  exact funext hx

end PDE.Analytic.CauchyKovalevskaya
