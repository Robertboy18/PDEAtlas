/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Differentiation.Coordinate
public import PDE.Analysis.Analytic.PowerSeries.Filtration
public import PDE.Analysis.Analytic.PowerSeries.Trace

/-!
# Time coefficients and native Cauchy traces

The trace of the `j`th time derivative is `j!` times the `j`th time
coefficient, as an entire spatial series. Over the reals, vanishing of this
native analytic trace is therefore equivalent to vanishing of that coefficient.
-/

@[expose] public section

open scoped Topology
open Filter MvPowerSeries PDE.Analysis.MultiIndex

/-- A zero pure-time Cauchy trace is equivalent to a zero full spatial
coefficient at the corresponding time degree. -/
theorem HasFPowerSeriesAt.eventuallyEq_zero_coordinateDeriv_finCons_iff
    {d j : ℕ} {u : ℝ^(d + 1) → ℝ}
    {p q : FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
    (hp : HasFPowerSeriesAt (fun x ↦ u (WithLp.toLp 2 x)) p 0)
    (hq : HasFPowerSeriesAt
      (fun x ↦ coordinateDeriv (Sym.replicate j 0) u (WithLp.toLp 2 x)) q 0) :
    (fun x : Fin d → ℝ ↦
      coordinateDeriv (Sym.replicate j 0) u (WithLp.toLp 2 (Fin.cons 0 x))) =ᶠ[𝓝 0] 0 ↔
        PowerSeries.coeff j (finSuccEquiv ℝ d p.toMvPowerSeries) = 0 := by
  rw [hq.eventuallyEq_zero_finCons_iff, hp.toMvPowerSeries_coordinateDeriv _ hq,
    Sym.coe_replicate, iteratedPDeriv_replicate]
  have hD : Function.Semiconj (finSuccEquiv ℝ d) (pderiv 0) PowerSeries.derivative :=
    finSuccEquiv_pderiv_zero
  rw [hD.iterate_right j p.toMvPowerSeries, PowerSeries.constantCoeff_iterate_derivative]
  have hj : (j.factorial : MvPowerSeries (Fin d) ℝ) ≠ 0 := by
    intro h
    have hreal := congrArg (constantCoeff : MvPowerSeries (Fin d) ℝ →+* ℝ) h
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at hreal
    exact Nat.factorial_ne_zero j hreal
  simp only [mul_eq_zero, hj, false_or]
