/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Integration.Retarded.Derivative
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Continuous first derivatives of retarded integrals

Joint continuity of the kernel and its spatial-age derivative gives a continuously
differentiable retarded integral. No derivative in the forcing index is required.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

/-- A continuous first-derivative family suffices for first regularity of a retarded integral. -/
theorem contDiff_one_retardedIntegral
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : ℝ → E × ℝ → V}
    (hF : ∀ s, Differentiable ℝ (F s))
    (hc : Continuous (fun p : ℝ × (E × ℝ) ↦ F p.1 p.2))
    (hD : Continuous (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (F p.1) p.2)) :
    ContDiff ℝ 1 (retardedIntegral F) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun p ↦ (ContinuousLinearMap.snd ℝ E ℝ).smulRight (F p.2 (p.1, 0)) +
    retardedIntegral (fun s ↦ fderiv ℝ (F s)) p, ?_, hasFDerivAt_retardedIntegral hF hc hD⟩
  exact (((ContinuousLinearMap.smulRightL ℝ (E × ℝ) V)
    (ContinuousLinearMap.snd ℝ E ℝ)).continuous.comp
      (hc.comp (continuous_snd.prodMk (continuous_fst.prodMk continuous_const)))).add
    (continuous_retardedIntegral hD)

end PDE.Analysis
