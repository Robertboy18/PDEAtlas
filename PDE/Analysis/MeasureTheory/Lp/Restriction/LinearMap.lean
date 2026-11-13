/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Restriction

/-!
# Bounded linear maps commute with restriction in Lp

Restricting the underlying measure and applying a bounded linear map to
the values give the same Lp class in either order.
-/

@[expose] public section

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ ν : Measure X}

/-- Valuewise bounded linear maps commute with the contractive restriction
associated with a measure inequality. -/
theorem compLpL_restrictionCLMOfLE (L : E →L[ℝ] F) (hμν : μ ≤ ν) :
    (L.compLpL p μ).comp (Lp.restrictionCLMOfLE hμν) =
      (Lp.restrictionCLMOfLE hμν).comp (L.compLpL p ν) := by
  ext1 u
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (Lp.restrictionCLMOfLE hμν u),
    Lp.restrictionCLMOfLE_apply_ae hμν u,
    Lp.restrictionCLMOfLE_apply_ae hμν (L.compLpL p ν u),
    (L.coeFn_compLpL u).filter_mono (ae_mono hμν)] with x hL hU hR hV
  simp only [comp_apply, hL, hU, hR, hV]

end ContinuousLinearMap
