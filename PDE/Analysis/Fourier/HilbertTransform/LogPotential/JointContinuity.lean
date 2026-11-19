/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.LogPotential.Lipschitz

/-!
# Joint continuity of compact logarithmic potentials

The logarithmic kernel is locally integrable. Mathlib's parametric convolution
theorem therefore gives joint continuity for continuous families with a common
compact support, without spatial differentiability of the density.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis

namespace DeGregorio

/-- A jointly continuous family with fixed compact support has jointly
continuous logarithmic potentials. -/
theorem continuous_logPotential_of_uniform_support
    {ι : Type*} [TopologicalSpace ι] {q : ι → ℝ → ℝ} {R : ℝ}
    (hs : ∀ t x, x ∉ Icc (-R) R → q t x = 0)
    (hq : Continuous (fun z : ℝ × ι ↦ q z.2 z.1)) :
    Continuous (fun z : ℝ × ι ↦ Real.pi⁻¹ * ∫ y, Real.log (z.1 - y) * q z.2 y) := by
  have hc := continuousOn_convolution_right_with_param
    (ContinuousLinearMap.lsmul ℝ ℝ) (f := Real.log) (μ := volume)
    (s := (univ : Set ι)) isCompact_Icc (fun t x _ hx ↦ hs t x hx)
    locallyIntegrable_real_log (hq.comp continuous_swap).continuousOn
  rw [univ_prod_univ] at hc
  have hh := (continuousOn_univ.mp hc).comp continuous_swap
  apply (hh.const_mul Real.pi⁻¹).congr
  intro z
  congr 1
  change (∫ y, Real.log y * q z.2 (z.1 - y)) =
    ∫ y, Real.log (z.1 - y) * q z.2 y
  simpa only [sub_sub_cancel] using
    integral_sub_left_eq_self (fun y ↦ Real.log (z.1 - y) * q z.2 y) volume z.1

end DeGregorio
