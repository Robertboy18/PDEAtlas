/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.LinearResponse

/-!
# The quadratic remainder of the constructed path

Subtracting the nonlinear fixed-point equation and its linear response
expresses the path remainder through the inverse at the doubled weight. The
Hessian estimate then gives a uniform quadratic bound.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L M : ℝ≥0} {N : E → E}

/-- The path remainder is the inverse linear response applied to the
nonlinear Taylor remainder, with the weight change made explicit. -/
theorem increaseExponentialWeight_perronPath_remainder
    {η θ : ℝ} (hηθ : η ≤ θ) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ x, increaseExponentialWeight hηθ (G x) = H (increaseExponentialWeight hηθ x))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN1 : ContDiff ℝ 1 N)
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1)
    (z w : ℝ →ᵇ E) :
    let P := perronPath η G hN hN0 hsmallG
    let D := linearizedExponentialComposition hN hN1 η (P z)
    increaseExponentialWeight hηθ
      (P w - P z - perronLinearResponse G hN hN1 hsmallG η (P z) (w - z)) =
      perronLinearResponse H hN hN1 hsmallH η (P z)
        (H (increaseExponentialWeight hηθ
          (composeExponentialWeight hN hN0 η (P w) -
            composeExponentialWeight hN hN0 η (P z) - D (P w - P z)))) := by
  let J := increaseExponentialWeight (E := E) hηθ
  let P := perronPath η G hN hN0 hsmallG
  let Q := composeExponentialWeight hN hN0 η
  let D := linearizedExponentialComposition hN hN1 η (P z)
  let R := perronLinearResponse G hN hN1 hsmallG η (P z)
  have hp : P w - P z = w - z + G (Q (P w) - Q (P z)) := by
    calc
      P w - P z = (w + G (Q (P w))) - (z + G (Q (P z))) :=
        congrArg₂ (· - ·) (perronPath_eq η G hN hN0 hsmallG w)
          (perronPath_eq η G hN hN0 hsmallG z)
      _ = _ := by rw [map_sub]; abel
  have he : P w - P z - R (w - z) =
      G (Q (P w) - Q (P z) - D (P w - P z)) +
        G (D (P w - P z - R (w - z))) := by
    calc
      P w - P z - R (w - z) =
          (w - z + G (Q (P w) - Q (P z))) -
            (w - z + G (D (R (w - z)))) :=
        congrArg₂ (· - ·) hp (perronLinearResponse_eq G hN hN1 hsmallG η (P z) (w - z))
      _ = _ := by simp only [map_sub]; abel
  apply perronLinearResponse_unique H hN hN1 hsmallH η (P z)
  change J (P w - P z - R (w - z)) =
    H (J (Q (P w) - Q (P z) - D (P w - P z))) +
      H (D (J (P w - P z - R (w - z))))
  calc
    J (P w - P z - R (w - z)) =
        H (J (Q (P w) - Q (P z) - D (P w - P z))) +
          H (J (D (P w - P z - R (w - z)))) := by
      conv_lhs => rw [he]
      rw [map_add, hcomm, hcomm]
    _ = _ := by rw [increaseExponentialWeight_linearizedExponentialComposition]

/-- A uniform quadratic remainder estimate for the fixed path and its
constructed first variation. Both contraction margins precede the paths. -/
theorem norm_increaseExponentialWeight_perronPath_remainder_le
    {η : ℝ} (hη : 0 ≤ η) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ x, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G x) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) x))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN2 : ContDiff ℝ 2 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1)
    (z w : ℝ →ᵇ E) :
    let P := perronPath η G hN hN0 hsmallG
    ‖increaseExponentialWeight (by linarith : η ≤ 2 * η)
      (P w - P z -
        perronLinearResponse G hN (hN2.of_le (by norm_num)) hsmallG η (P z) (w - z))‖ ≤
      ((1 - ‖H‖ * L)⁻¹ * ‖H‖ * M * (1 - ‖G‖ * L)⁻¹ ^ 2) * ‖w - z‖ ^ 2 := by
  dsimp only
  let P := perronPath η G hN hN0 hsmallG
  let J := increaseExponentialWeight (E := E) (by linarith : η ≤ 2 * η)
  let D := linearizedExponentialComposition hN (hN2.of_le (by norm_num)) η (P z)
  let Q := composeExponentialWeight hN hN0 η
  let R := perronLinearResponse H hN (hN2.of_le (by norm_num)) hsmallH η (P z)
  have hH : 0 ≤ (1 - ‖H‖ * L)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hsmallH).le
  have hp : ‖P w - P z‖ ≤ ‖w - z‖ / (1 - ‖G‖ * L) := by
    simpa only [dist_eq_norm] using dist_perronPath_le η G hN hN0 hsmallG w z
  rw [increaseExponentialWeight_perronPath_remainder
    (by linarith : η ≤ 2 * η) G H hcomm hN hN0 (hN2.of_le (by norm_num)) hsmallG hsmallH]
  calc
    ‖R (H (J (Q (P w) - Q (P z) - D (P w - P z))))‖ ≤
        (1 - ‖H‖ * L)⁻¹ * ‖H (J (Q (P w) - Q (P z) - D (P w - P z)))‖ :=
      R.le_of_opNorm_le_of_le
        (norm_perronLinearResponse_le H hN (hN2.of_le (by norm_num)) hsmallH η (P z)) le_rfl
    _ ≤ (1 - ‖H‖ * L)⁻¹ *
        (‖H‖ * ‖J (Q (P w) - Q (P z) - D (P w - P z))‖) :=
      mul_le_mul_of_nonneg_left (H.le_opNorm _) hH
    _ ≤ (1 - ‖H‖ * L)⁻¹ * (‖H‖ * (M * ‖P w - P z‖ ^ 2)) := by
      gcongr
      exact norm_weighted_composition_remainder_le hη hN hN0 hN2 M.coe_nonneg
        (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hDN) (P z) (P w)
    _ ≤ (1 - ‖H‖ * L)⁻¹ * (‖H‖ * (M * (‖w - z‖ / (1 - ‖G‖ * L)) ^ 2)) := by
      gcongr
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

end PDE.Analysis.Evolution
