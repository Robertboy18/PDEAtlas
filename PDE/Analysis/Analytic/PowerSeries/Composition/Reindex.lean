/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Composition
public import PDE.Analysis.Analytic.PowerSeries.FiniteOperations
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Reindexing analytic variables

Pulling an analytic function back by a map of finite coordinate sets renames its
commutative expansion. The coordinate map need not be injective.
-/

@[expose] public section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Reindexing the arguments of an analytic function renames its formal variables,
including when several old variables are identified. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_comp_reindex
    (ρ : κ → ι) {f : (κ → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (κ → ℝ) ℝ}
    {q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0)
    (hq : HasFPowerSeriesAt (fun x ↦ f (fun j ↦ x (ρ j))) q 0) :
    q.toMvPowerSeries = MvPowerSeries.rename ρ p.toMvPowerSeries := by
  have hproj (j : κ) : AnalyticAt ℝ (fun x : ι → ℝ ↦ x (ρ j)) 0 :=
    (ContinuousLinearMap.proj (ρ j) : (ι → ℝ) →L[ℝ] ℝ).analyticAt 0
  choose r hr using hproj
  rw [hp.toMvPowerSeries_comp hr rfl hq, MvPowerSeries.rename_eq_subst]
  congr 1
  funext j
  exact (hr j).toMvPowerSeries_proj (ρ j)
