/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import PDE.Common.Euclidean.SpaceTime

/-!
# Lebesgue measure in canonical spacetime coordinates

The splitting of `SpaceTime n` into its time coordinate and its spatial part
`ℝ × ℝ^n` preserves Lebesgue measure.
-/

@[expose] public noncomputable section

namespace PDE.Common

open MeasureTheory

/-- Splitting spacetime into its time coordinate and spatial part preserves Lebesgue measure. -/
theorem measurePreserving_timeSpaceContinuousLinearEquiv {n : ℕ} :
    MeasurePreserving
      (timeSpaceContinuousLinearEquiv n : SpaceTime n → ℝ × ℝ^n) volume volume := by
  have hprod := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))
  rw [← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at hprod
  have h := hprod.comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin (n + 1))))
  convert h using 1
  funext p
  apply Prod.ext
  · rfl
  · ext i
    simp [Function.comp_def, MeasurableEquiv.piFinSuccAbove, Fin.tail]

end PDE.Common
