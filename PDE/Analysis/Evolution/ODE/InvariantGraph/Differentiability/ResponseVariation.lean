/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.LinearResponse
public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.CoefficientVariation

/-!
# Variation of the linear response

The resolvent identity for the linearized equation remains valid across
two exponential weights. A change of base path of weight `η` therefore gives a
Lipschitz bound for the response from weight `α` to `α + η`.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L M : ℝ≥0} {N : E → E}

/-- The cross-weight resolvent identity follows from the linearized
equations and the Green intertwining identity. -/
theorem increaseExponentialWeight_perronLinearResponse_sub
    {α β : ℝ} (hαβ : α ≤ β) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ w, increaseExponentialWeight hαβ (G w) = H (increaseExponentialWeight hαβ w))
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1)
    (η : ℝ) (u v w : ℝ →ᵇ E) :
    increaseExponentialWeight hαβ
      (perronLinearResponse G hN hN1 hsmallG η v w -
        perronLinearResponse G hN hN1 hsmallG η u w) =
      perronLinearResponse H hN hN1 hsmallH η u
        (H (increaseExponentialWeight hαβ
          ((linearizedExponentialComposition hN hN1 η v -
            linearizedExponentialComposition hN hN1 η u)
              (perronLinearResponse G hN hN1 hsmallG η v w)))) := by
  let J := increaseExponentialWeight (E := E) hαβ
  let D := linearizedExponentialComposition hN hN1 η
  let R := perronLinearResponse G hN hN1 hsmallG η
  have he : R v w - R u w =
      G (D u (R v w - R u w)) + G ((D v - D u) (R v w)) := by
    calc
      R v w - R u w = (w + G (D v (R v w))) - (w + G (D u (R u w))) :=
        congrArg₂ (· - ·) (perronLinearResponse_eq G hN hN1 hsmallG η v w)
          (perronLinearResponse_eq G hN hN1 hsmallG η u w)
      _ = _ := by simp only [_root_.sub_apply, map_sub]; abel
  apply perronLinearResponse_unique H hN hN1 hsmallH η u
  change J (R v w - R u w) = H (J ((D v - D u) (R v w))) +
    H (D u (J (R v w - R u w)))
  calc
    J (R v w - R u w) =
        H (J (D u (R v w - R u w))) + H (J ((D v - D u) (R v w))) := by
      conv_lhs => rw [he]
      rw [map_add, hcomm, hcomm]
    _ = _ := by
      rw [increaseExponentialWeight_linearizedExponentialComposition]
      exact add_comm _ _

/-- A Lipschitz derivative yields a quantitative cross-weight bound for the
inverse family, with both contraction margins displayed. -/
theorem norm_increaseExponentialWeight_perronLinearResponse_sub_le
    {η : ℝ} (hη : 0 ≤ η) (α : ℝ) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ w, increaseExponentialWeight (by linarith : α ≤ α + η) (G w) =
      H (increaseExponentialWeight (by linarith : α ≤ α + η) w))
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1)
    (u v : ℝ →ᵇ E) :
    ‖(increaseExponentialWeight (by linarith : α ≤ α + η)).comp
      (perronLinearResponse G hN hN1 hsmallG η v -
        perronLinearResponse G hN hN1 hsmallG η u)‖ ≤
      (1 - ‖H‖ * L)⁻¹ * ‖H‖ * M * ‖v - u‖ * (1 - ‖G‖ * L)⁻¹ := by
  let J := increaseExponentialWeight (E := E) (by linarith : α ≤ α + η)
  let D := linearizedExponentialComposition hN hN1 η
  let R := perronLinearResponse G hN hN1 hsmallG η
  let S := perronLinearResponse H hN hN1 hsmallH η
  have hG : 0 ≤ (1 - ‖G‖ * L)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hsmallG).le
  have hH : 0 ≤ (1 - ‖H‖ * L)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hsmallH).le
  apply ContinuousLinearMap.opNorm_le_bound _
    (by positivity : 0 ≤ (1 - ‖H‖ * L)⁻¹ * ‖H‖ * M * ‖v - u‖ * (1 - ‖G‖ * L)⁻¹)
  intro w
  change ‖J (R v w - R u w)‖ ≤ _
  rw [increaseExponentialWeight_perronLinearResponse_sub
    (by linarith : α ≤ α + η) G H hcomm hN hN1 hsmallG hsmallH]
  calc
    ‖S u (H (J ((D v - D u) (R v w))))‖ ≤
        (1 - ‖H‖ * L)⁻¹ * ‖H (J ((D v - D u) (R v w)))‖ :=
      (S u).le_of_opNorm_le_of_le
        (norm_perronLinearResponse_le H hN hN1 hsmallH η u) le_rfl
    _ ≤ (1 - ‖H‖ * L)⁻¹ * (‖H‖ * ‖J ((D v - D u) (R v w))‖) :=
      mul_le_mul_of_nonneg_left (H.le_opNorm _) hH
    _ ≤ (1 - ‖H‖ * L)⁻¹ * (‖H‖ * ((M * ‖v - u‖) * ‖R v w‖)) := by
      gcongr
      exact (J.comp (D v - D u)).le_of_opNorm_le_of_le
        (norm_increaseExponentialWeight_linearized_sub_le hη α hN hN1 hDN u v) le_rfl
    _ ≤ (1 - ‖H‖ * L)⁻¹ *
        (‖H‖ * ((M * ‖v - u‖) * ((1 - ‖G‖ * L)⁻¹ * ‖w‖))) := by
      gcongr
      exact (R v).le_of_opNorm_le_of_le
        (norm_perronLinearResponse_le G hN hN1 hsmallG η v) le_rfl
    _ = _ := by ring

end PDE.Analysis.Evolution
