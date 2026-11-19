/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.PolynomialComposition

/-!
# Finite operations on commutative analytic expansions

Coordinate projections and finite sums have their expected formal
coefficients, independently of the chosen native multilinear representatives.
-/

@[expose] public section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The commutative expansion of a coordinate projection is its formal variable. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_proj
    {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} (i : ι)
    (hp : HasFPowerSeriesAt (fun x ↦ x i) p 0) :
    p.toMvPowerSeries = MvPowerSeries.X i := by
  simpa only [MvPolynomial.coe_X] using
    HasFPowerSeriesAt.toMvPowerSeries_eval (MvPolynomial.X i)
      (show HasFPowerSeriesAt (fun x ↦ MvPolynomial.eval x (MvPolynomial.X i)) p 0 by
        simpa only [MvPolynomial.eval_X] using hp)

/-- Commutative analytic coefficients commute with any finite sum. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_sum
    {κ : Type*} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ}
    {p : κ → FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    {q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : ∀ j, HasFPowerSeriesAt (f j) (p j) 0)
    (hq : HasFPowerSeriesAt (fun x ↦ ∑ j ∈ s, f j x) q 0) :
    q.toMvPowerSeries = ∑ j ∈ s, (p j).toMvPowerSeries := by
  classical
  let P : MvPolynomial κ ℝ := ∑ j ∈ s, MvPolynomial.X j
  have hP : HasFPowerSeriesAt (fun x ↦ MvPolynomial.eval (fun j ↦ f j x) P) q 0 := by
    simpa only [P, map_sum, MvPolynomial.eval_X] using hq
  simpa only [P, map_sum, MvPolynomial.aeval_X] using
    HasFPowerSeriesAt.toMvPowerSeries_eval_comp hp P hP
