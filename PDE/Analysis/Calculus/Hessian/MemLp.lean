/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Addition of almost-everywhere classical Hessians in Lp

The Hessian sum rule only needs twice differentiability almost everywhere.
This permits finite sums of fields whose classical formulas omit a null set.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open MeasureTheory
open scoped BigOperators ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The operator norm on `E →L[ℝ] F`. -/
local instance normedAddCommGroupCLM : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
/-- The real scalar action on `E →L[ℝ] F`, for the operator norm. -/
local instance normedSpaceCLM : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- The operator norm on the bilinear maps `E →L[ℝ] E →L[ℝ] F`, where Hessians live. -/
local instance normedAddCommGroupBilinearCLM : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
/-- The real scalar action on the bilinear maps `E →L[ℝ] E →L[ℝ] F`. -/
local instance normedSpaceBilinearCLM : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- The twice-differentiable finite sum has the sum of the classical Hessians. -/
theorem fderiv_fderiv_fun_sum {ι : Type*} {s : Finset ι} {U : ι → E → F}
    {x : E} (hU : ∀ i ∈ s, ContDiffAt ℝ 2 (U i) x) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ∑ i ∈ s, U i y)) x =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (U i)) x := by
  ext v w : 2
  have h := congrArg (fun A ↦ A ![v, w])
    (iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) hU)
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    sum_apply] using h

/-- Twice-differentiable addition preserves the sum of the classical Hessians. -/
theorem fderiv_fderiv_fun_add {U V : E → F} {x : E}
    (hU : ContDiffAt ℝ 2 U x) (hV : ContDiffAt ℝ 2 V x) :
    fderiv ℝ (fderiv ℝ (fun y ↦ U y + V y)) x =
      fderiv ℝ (fderiv ℝ U) x + fderiv ℝ (fderiv ℝ V) x := by
  ext v w : 2
  have h := congrArg (fun A ↦ A ![v, w]) (iteratedFDeriv_add_apply hU hV)
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_apply, Pi.add_def] using h

variable [MeasurableSpace E] {μ : Measure E} {p : ℝ≥0∞}

/-- Two Lp Hessians add when their fields are twice differentiable almost everywhere. -/
theorem memLp_fderiv_fderiv_add {U V : E → F}
    (hU : ∀ᵐ x ∂μ, ContDiffAt ℝ 2 U x) (hV : ∀ᵐ x ∂μ, ContDiffAt ℝ 2 V x)
    (hUm : MemLp (fderiv ℝ (fderiv ℝ U)) p μ)
    (hVm : MemLp (fderiv ℝ (fderiv ℝ V)) p μ) :
    MemLp (fderiv ℝ (fderiv ℝ (fun y ↦ U y + V y))) p μ := by
  have hsum := hUm.add hVm
  apply MemLp.ae_eq ?_ hsum
  filter_upwards [hU, hV] with x hxU hxV
  exact (fderiv_fderiv_fun_add hxU hxV).symm

/-- A finite sum of almost-everywhere twice-differentiable fields retains its Lp Hessian. -/
theorem memLp_fderiv_fderiv_sum {ι : Type*} {s : Finset ι} {U : ι → E → F}
    (hU : ∀ᵐ x ∂μ, ∀ i ∈ s, ContDiffAt ℝ 2 (U i) x)
    (hUm : ∀ i ∈ s, MemLp (fderiv ℝ (fderiv ℝ (U i))) p μ) :
    MemLp (fderiv ℝ (fderiv ℝ (fun y ↦ ∑ i ∈ s, U i y))) p μ := by
  have hsum := memLp_finsetSum s hUm
  apply MemLp.ae_eq ?_ hsum
  filter_upwards [hU] with x hx
  exact (fderiv_fderiv_fun_sum hx).symm

end PDE.Analysis
