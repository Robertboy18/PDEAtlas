/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Sobolev
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceVector

/-!
# Vector Sobolev heat smoothing

Coordinatewise physical heat evolution gains one weak derivative on vector
Sobolev graphs, and each base component is the physical Fourier heat evolution
of the corresponding base component.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal NNReal Sobolev

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- Actual coordinatewise heat evolution gaining one weak derivative of vector fields. -/
def vectorHeatGain (n k : ℕ) (t : ℝ) (ht : 0 < t) :
    VectorH n k →L[ℝ] VectorH n (k + 1) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦ heatGainSobolev n k t ht)

@[simp]
theorem vectorHeatGain_apply {t : ℝ} (ht : 0 < t) (u : VectorH n k) (j : Fin n) :
    vectorHeatGain n k t ht u j = heatGainSobolev n k t ht (u j) := by
  simp only [vectorHeatGain, ContinuousLinearMap.piLpMap_apply]

/-- Each output base function is exactly the physical Fourier heat evolution. -/
theorem baseL2_vectorHeatGain (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (u : VectorH n k) (j : Fin n) :
    baseL2 (vectorHeatGain n k (t : ℝ) ht u j) = heatL2 n t (baseL2 (u j)) := by
  rw [vectorHeatGain_apply, baseL2_heatGainSobolev]

end HeatEquation.WholeSpace
