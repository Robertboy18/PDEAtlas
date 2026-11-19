/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Operator
public import PDE.Common.Euclidean.SpaceTime

/-!
# The wave operator on a product Hessian

The canonical coordinate operator contracts the second Fréchet
derivative in space-time product coordinates. This uses only two derivatives
and applies in every spatial dimension, including zero.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE (time)
open PDE.Common

/-- The wave operator in product coordinates is the time direction of the
Hessian minus its spatial trace. -/
theorem waveOperator_comp_splitSpaceTime {n : ℕ} {F : ℝ^n × ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (p : ℝ^(n + 1)) :
    waveOperator (fun q ↦ F (splitSpaceTime q)) p =
      fderiv ℝ (fderiv ℝ F) (splitSpaceTime p) (0, 1) (0, 1) -
        ∑ i : Fin n, fderiv ℝ (fderiv ℝ F) (splitSpaceTime p)
          (EuclideanSpace.single i (1 : ℝ), 0) (EuclideanSpace.single i (1 : ℝ), 0) := by
  let L := (spaceTimeContinuousLinearEquiv n).toContinuousLinearMap
  have hsecond (i : Fin (n + 1)) : (∂[i] (∂[i] (F ∘ L))) p = fderiv ℝ (fderiv ℝ F) (L p)
          (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single i 1)) := by
    rw [PDE.secondPartialDeriv_eq_iteratedFDeriv_apply i i (hF.comp L.contDiff).contDiffAt,
      L.iteratedFDeriv_comp_right hF p le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have htime : L (EuclideanSpace.single (0 : Fin (n + 1)) 1) = (0, 1) := by
    change splitSpaceTime (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = (0, 1)
    rw [splitSpaceTime, ← spatialPartCLM_eq_spatialPart, spatialPartCLM_single_zero]
    simp [time]
  have hspace (i : Fin n) :
      L (EuclideanSpace.single i.succ 1) = (EuclideanSpace.single i 1, 0) := by
    change splitSpaceTime (EuclideanSpace.single i.succ (1 : ℝ)) =
      (EuclideanSpace.single i (1 : ℝ), 0)
    rw [splitSpaceTime, ← spatialPartCLM_eq_spatialPart, spatialPartCLM_single_succ]
    simp [time]
  change waveOperator (F ∘ L) p = _
  simp only [waveOperator, hsecond, htime, hspace]
  rfl

end WaveEquation
