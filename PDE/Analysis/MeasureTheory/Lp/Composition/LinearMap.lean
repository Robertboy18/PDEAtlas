/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Composition of bounded maps on Lp

The Lp lift respects composition of continuous linear maps. This lets
identities between spatial operators pass to Bochner classes directly.
-/

@[expose] public section

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal

variable {𝕜 X E F G : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure X}

/-- Lifting to Lp respects composition of continuous linear maps. -/
theorem comp_compLpL (L : F →L[𝕜] G) (K : E →L[𝕜] F) :
    (L.comp K).compLpL p μ = (L.compLpL p μ).comp (K.compLpL p μ) := by
  ext1 u
  apply Lp.ext
  filter_upwards [(L.comp K).coeFn_compLpL u, L.coeFn_compLpL (K.compLpL p μ u),
    K.coeFn_compLpL u] with x hLK hL hK
  simp only [comp_apply, hLK, hL, hK]

end ContinuousLinearMap
