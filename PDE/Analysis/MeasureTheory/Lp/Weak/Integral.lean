/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakCompactness
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrals of weakly convergent Bochner L² functions

Indicators of finite-measure sets are legitimate Hilbert-space tests. Their pairings
identify vector integrals without a countable dense subset of the target space.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace PDE.Analysis

variable {H α ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace α] {μ : Measure α}
  {l : Filter ι} {v : ι → Lp H 2 μ} {v₀ : Lp H 2 μ}

/-- Every finite-measure set integral converges weakly under weak Bochner `L²`
convergence. The testing vector is arbitrary, with no separability hypothesis. -/
theorem tendsto_inner_setIntegral_of_tendsto_weak_L2
    (hv : Tendsto (fun i ↦ toWeakSpace ℝ (Lp H 2 μ) (v i)) l
      (𝓝 (toWeakSpace ℝ (Lp H 2 μ) v₀)))
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (h : H) :
    Tendsto (fun i ↦ inner ℝ h (∫ t in s, v i t ∂μ)) l
      (𝓝 (inner ℝ h (∫ t in s, v₀ t ∂μ))) := by
  simpa only [innerSL_apply_apply, LinearEquiv.symm_apply_apply,
    L2.inner_indicatorConstLp_eq_inner_setIntegral]
    using WeakCompactness.tendsto_evaluation hv
      (innerSL ℝ (indicatorConstLp 2 hs hμs h))

end PDE.Analysis
