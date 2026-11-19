/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integrals of compactly supported directional derivatives

Integration by parts against the constant function gives zero integral in each
direction. The finite-dimensional statement also covers a zero-dimensional
space, where every directional derivative vanishes.
-/

@[expose] public section

open MeasureTheory Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

namespace PDE

/-- A compactly supported C¹ scalar function has zero integral of every
directional derivative. -/
theorem integral_fderiv_eq_zero_of_hasCompactSupport {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) (v : E) :
    ∫ x, fderiv ℝ f x v ∂μ = 0 := by
  have hint : Integrable (fun x ↦ fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcompact.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : E ↦ (1 : ℝ)) (g := f) (v := v)
    (by simp) (by simpa using hint)
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hcompact)
    (fun _ _ ↦ differentiableAt_const _) (fun x _ ↦ hf.differentiable one_ne_zero x)
  simpa using h

end PDE
