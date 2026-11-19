/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.FirstDerivative
public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightCoherence

/-!
# First variation of the constructed Perron path

The fixed path is Lipschitz in its homogeneous term at the original weight.
The quadratic composition remainder therefore gives differentiability
at twice that weight. Invertibility of the linearized equation follows from
the second contraction bound, using Mathlib's geometric-series inverse.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L : ℝ≥0} {N : E → E} {η : ℝ}

/-- The fixed path has a Fréchet derivative in the doubled weight.
The derivative solves the linearized integral equation; both Green operators
and their intertwining identity are explicit, as are both contraction bounds. -/
theorem exists_hasFDerivAt_increaseExponentialWeight_perronPath
    (hη : 0 ≤ η) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ v, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G v) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) v))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN2 : ContDiff ℝ 2 N)
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ N) x‖ ≤ M)
    (z : ℝ →ᵇ E) :
    let u := perronPath η G hN hN0 hsmallG z
    ∃ d : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E),
      HasFDerivAt
        (fun w ↦ increaseExponentialWeight (by linarith : η ≤ 2 * η)
          (perronPath η G hN hN0 hsmallG w)) d z ∧
      (1 - H.comp (linearizedExponentialComposition hN (hN2.of_le (by norm_num)) η u)).comp d =
        increaseExponentialWeight (by linarith : η ≤ 2 * η) := by
  let J : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
    increaseExponentialWeight (by linarith : η ≤ 2 * η)
  let P := perronPath η G hN hN0 hsmallG
  let Q := composeExponentialWeight hN hN0 η
  let D := linearizedExponentialComposition hN (hN2.of_le (by norm_num)) η (P z)
  let A := H.comp D
  have hA : ‖A‖ < 1 :=
    ((H.opNorm_comp_le D).trans
      (mul_le_mul_of_nonneg_left
        (norm_linearizedExponentialComposition_le hN (hN2.of_le (by norm_num)) η (P z))
        (norm_nonneg H))).trans_lt hsmallH
  let C := ‖H‖ * M * (1 - ‖G‖ * L)⁻¹ ^ 2
  have hr (w : ℝ →ᵇ E) :
      ‖J (P w) - J (P z) - A (J (P w) - J (P z)) - J (w - z)‖ ≤ C * ‖w - z‖ ^ 2 := by
    have hp : P w - P z = w - z + G (Q (P w) - Q (P z)) := by
      calc
        P w - P z = (w + G (Q (P w))) - (z + G (Q (P z))) :=
          congrArg₂ (· - ·) (perronPath_eq η G hN hN0 hsmallG w)
            (perronPath_eq η G hN hN0 hsmallG z)
        _ = w - z + G (Q (P w) - Q (P z)) := by rw [map_sub]; abel
    have hj : J (P w) - J (P z) = J (w - z) + H (J (Q (P w) - Q (P z))) := by
      rw [← map_sub, hp, map_add]
      exact congrArg (J (w - z) + ·) (hcomm _)
    have hd : J (D (P w - P z)) = D (J (P w) - J (P z)) := by
      simpa only [map_sub] using
        increaseExponentialWeight_linearizedExponentialComposition
          hN (hN2.of_le (by norm_num)) η (by linarith : η ≤ 2 * η) (P z) (P w - P z)
    have heq :
        J (P w) - J (P z) - A (J (P w) - J (P z)) - J (w - z) =
          H (J (Q (P w) - Q (P z) - D (P w - P z))) := by
      change J (P w) - J (P z) - H (D (J (P w) - J (P z))) - J (w - z) = _
      rw [J.map_sub (Q (P w) - Q (P z)) (D (P w - P z)), H.map_sub, hd]
      rw [hj]
      abel
    rw [heq]
    have hdist : ‖P w - P z‖ ≤ ‖w - z‖ / (1 - ‖G‖ * L) := by
      simpa only [dist_eq_norm] using dist_perronPath_le η G hN hN0 hsmallG w z
    calc
      ‖H (J (Q (P w) - Q (P z) - D (P w - P z)))‖ ≤
          ‖H‖ * ‖J (Q (P w) - Q (P z) - D (P w - P z))‖ := H.le_opNorm _
      _ ≤ ‖H‖ * (M * ‖P w - P z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (norm_weighted_composition_remainder_le hη hN hN0 hN2 hM hbound (P z) (P w))
          (norm_nonneg H)
      _ ≤ ‖H‖ * (M * (‖w - z‖ / (1 - ‖G‖ * L)) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist 2) hM)
          (norm_nonneg H)
      _ = C * ‖w - z‖ ^ 2 := by dsimp only [C]; rw [div_eq_mul_inv, mul_pow]; ring
  have hd := hasFDerivAt_of_quadratic_contraction_residual
    (fun w ↦ J (P w)) z A hA J C hr
  refine ⟨_, hd, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  change (ContinuousLinearEquiv.ofUnit (Units.oneSub A hA))
    ((ContinuousLinearEquiv.ofUnit (Units.oneSub A hA)).symm (J v)) = J v
  exact (ContinuousLinearEquiv.ofUnit (Units.oneSub A hA)).apply_symm_apply (J v)

end PDE.Analysis.Evolution
