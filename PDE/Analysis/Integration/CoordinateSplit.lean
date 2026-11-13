/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Polar
public import PDE.Analysis.InnerProductSpace.Euclidean.CoordinateProjection

/-!
# Lebesgue measure under the last-coordinate splitting

The orthogonal splitting of Euclidean space preserves Lebesgue measure. Its last
one-dimensional Euclidean factor is identified with `ℝ`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Analysis

variable {n : ℕ}

/-- Split off the last Cartesian coordinate. -/
def lastCoordinateSplit : ℝ^(n + 1) ≃ᵐ (ℝ^n × ℝ) :=
  (euclideanSumMeasurableEquiv n 1).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ℝ^n))
      ((MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
        (MeasurableEquiv.funUnique (Fin 1) ℝ)))

/-- The Cartesian split agrees with the continuous coordinate projection. -/
theorem lastCoordinateSplit_apply (x : ℝ^(n + 1)) :
    lastCoordinateSplit x = (coordinateProjection x, x (Fin.last n)) := by
  rfl

/-- The first component is the retained-coordinate projection. -/
@[simp]
theorem lastCoordinateSplit_fst (x : ℝ^(n + 1)) :
    (lastCoordinateSplit x).1 = coordinateProjection x := rfl

/-- The second component is the last coordinate. -/
@[simp]
theorem lastCoordinateSplit_snd (x : ℝ^(n + 1)) :
    (lastCoordinateSplit x).2 = x (Fin.last n) := rfl

/-- Reassembly recovers the retained coordinates. -/
@[simp]
theorem coordinateProjection_lastCoordinateSplit_symm (p : ℝ^n × ℝ) :
    coordinateProjection (lastCoordinateSplit.symm p) = p.1 := by
  rw [← lastCoordinateSplit_fst, MeasurableEquiv.apply_symm_apply]

/-- Reassembly recovers the last coordinate. -/
@[simp]
theorem lastCoordinateSplit_symm_last (p : ℝ^n × ℝ) :
    lastCoordinateSplit.symm p (Fin.last n) = p.2 := by
  rw [← lastCoordinateSplit_snd, MeasurableEquiv.apply_symm_apply]

/-- Reassembly recovers each retained coordinate. -/
@[simp]
theorem lastCoordinateSplit_symm_castSucc (p : ℝ^n × ℝ) (i : Fin n) :
    lastCoordinateSplit.symm p i.castSucc = p.1 i := by
  rw [← coordinateProjection_apply, coordinateProjection_lastCoordinateSplit_symm]

/-- The last-coordinate split preserves the product of the Lebesgue measures. -/
theorem lastCoordinateSplit_measurePreserving :
    MeasurePreserving (lastCoordinateSplit (n := n)) volume volume := by
  apply MeasurePreserving.trans
  · exact euclideanSumMeasurableEquiv_measurePreserving n 1
  · exact (MeasurePreserving.id volume).prod
      ((PiLp.volume_preserving_ofLp (Fin 1)).trans
        (volume_preserving_funUnique (Fin 1) ℝ))

end PDE.Analysis
