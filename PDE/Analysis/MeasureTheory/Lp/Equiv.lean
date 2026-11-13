/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Continuous linear equivalences on Bochner `Lᵖ` spaces

A continuous real-linear equivalence between normed spaces acts pointwise on
Bochner `Lᵖ` classes. The action is a continuous linear
equivalence, with an explicit almost-everywhere representative.
-/

@[expose] public section

noncomputable section


open MeasureTheory

namespace ContinuousLinearEquiv

variable {E F α : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace α]

/-- Pointwise application of a continuous real-linear equivalence, lifted to
Bochner `Lᵖ`. -/
def compLpLEquiv
    (e : E ≃L[ℝ] F) (p : ENNReal) (μ : Measure α) [Fact (1 ≤ p)] :
    Lp E p μ ≃L[ℝ] Lp F p μ where
  toLinearEquiv :=
    { (e.toContinuousLinearMap.compLpL p μ).toLinearMap with
      invFun := e.symm.toContinuousLinearMap.compLpL p μ
      left_inv := by
        intro f
        change e.symm.toContinuousLinearMap.compLpL p μ
          (e.toContinuousLinearMap.compLpL p μ f) = f
        apply Lp.ext
        filter_upwards [
          e.symm.toContinuousLinearMap.coeFn_compLpL
            (e.toContinuousLinearMap.compLpL p μ f),
          e.toContinuousLinearMap.coeFn_compLpL f] with x hsymm he
        rw [hsymm, he]
        exact e.symm_apply_apply (f x)
      right_inv := by
        intro f
        change e.toContinuousLinearMap.compLpL p μ
          (e.symm.toContinuousLinearMap.compLpL p μ f) = f
        apply Lp.ext
        filter_upwards [
          e.toContinuousLinearMap.coeFn_compLpL
            (e.symm.toContinuousLinearMap.compLpL p μ f),
          e.symm.toContinuousLinearMap.coeFn_compLpL f] with x he hsymm
        rw [he, hsymm]
        exact e.apply_symm_apply (f x) }
  continuous_toFun := (e.toContinuousLinearMap.compLpL p μ).continuous
  continuous_invFun := (e.symm.toContinuousLinearMap.compLpL p μ).continuous

/-- The lifted equivalence acts by pointwise application almost everywhere. -/
theorem compLpLEquiv_apply_ae
    (e : E ≃L[ℝ] F) (p : ENNReal) (μ : Measure α) [Fact (1 ≤ p)]
    (f : Lp E p μ) :
    (e.compLpLEquiv p μ f : α → F) =ᵐ[μ] fun x ↦ e (f x) :=
  e.toContinuousLinearMap.coeFn_compLpL f

end ContinuousLinearEquiv
