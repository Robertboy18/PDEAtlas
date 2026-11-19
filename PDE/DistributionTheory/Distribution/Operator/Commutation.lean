/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import PDE.DistributionTheory.TestFunction.Derivative.Commutation

/-!
# Commuting constant derivatives of ordinary distributions

Transposing the identity on smooth test functions gives commuting directional
derivatives without assuming that the distribution is tempered or is represented
by a smooth function. Constant linear maps of the values commute with these
derivatives as well.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] {Ω : Opens E}

/-- Constant directional derivatives commute on ordinary distributions on
an arbitrary open set. -/
theorem lineDerivCLM_commute (v w : E) :
    Commute (lineDerivCLM v : 𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, F))
      (lineDerivCLM w) := by
  ext T φ
  simp only [mul_apply_eq_comp, lineDerivCLM_apply, neg_neg]
  have h := congrArg (fun A : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) ↦ A φ)
    (TestFunction.lineDerivCLM_commute (Ω := Ω) (F := ℝ) w v)
  exact congrArg T h

/-- A constant map of the values commutes with a distributional derivative. -/
theorem mapCLM_lineDerivCLM (A : F →L[ℝ] G) (v : E) (T : 𝓓'(Ω, F)) :
    mapCLM A (lineDerivCLM v T) = (lineDerivCLM v (mapCLM A T) : 𝓓'(Ω, G)) := by
  ext φ
  simp only [mapCLM_apply, lineDerivCLM_apply, map_neg]

end Distribution
