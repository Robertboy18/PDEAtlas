/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Gelfand embeddings on Bochner spaces

The energy-to-dual map factors through the pivot space, also after passage
from pointwise maps to maps on Bochner equivalence classes.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PDE.Analysis.Evolution

/-- The energy-to-dual map on `Lᵖ` is the composition of the two Gelfand
embeddings on `Lᵖ`. -/
theorem GelfandTriple.pivotToDual_compLpL_inclusion
    {V H X : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure X} (v : Lp V p μ) :
    T.pivotToDual.compLpL p μ (T.inclusion.compLpL p μ v) =
      T.energyToDual.compLpL p μ v := by
  apply Lp.ext
  filter_upwards [T.pivotToDual.coeFn_compLpL (T.inclusion.compLpL p μ v),
    T.inclusion.coeFn_compLpL v, T.energyToDual.coeFn_compLpL v] with t h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  rfl

end PDE.Analysis.Evolution
