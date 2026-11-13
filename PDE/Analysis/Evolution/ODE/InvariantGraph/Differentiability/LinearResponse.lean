/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.FirstVariation

/-!
# The linear response along a constructed path

The derivative along a base path gives a linear contraction on every
admissible variation weight. Its inverse is a bounded linear response
to the homogeneous term. Weight changes commute with this response whenever
they commute with the Green operators.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L : ℝ≥0} {N : E → E}

omit [CompleteSpace E] in
/-- The linearized Green operator has the same strict contraction margin. -/
theorem norm_comp_linearizedExponentialComposition_lt_one
    (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (hsmall : ‖G‖ * L < 1) (η : ℝ) (u : ℝ →ᵇ E) :
    ‖G.comp (linearizedExponentialComposition hN hN1 η u)‖ < 1 :=
  ((G.opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_left (norm_linearizedExponentialComposition_le hN hN1 η u)
      (norm_nonneg G))).trans_lt hsmall

/-- The linear response to a homogeneous perturbation, constructed by the
inverse of the linearized contraction. -/
def perronLinearResponse (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (hsmall : ‖G‖ * L < 1) (η : ℝ) (u : ℝ →ᵇ E) :
    (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  (ContinuousLinearEquiv.ofUnit
    (Units.oneSub (G.comp (linearizedExponentialComposition hN hN1 η u))
      (norm_comp_linearizedExponentialComposition_lt_one G hN hN1
        hsmall η u))).symm.toContinuousLinearMap

/-- The constructed response satisfies its linearized integral equation. -/
theorem perronLinearResponse_eq (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (hsmall : ‖G‖ * L < 1) (η : ℝ) (u v : ℝ →ᵇ E) :
    perronLinearResponse G hN hN1 hsmall η u v =
      v + G (linearizedExponentialComposition hN hN1 η u
        (perronLinearResponse G hN hN1 hsmall η u v)) := by
  have h := (ContinuousLinearEquiv.ofUnit
    (Units.oneSub (G.comp (linearizedExponentialComposition hN hN1 η u))
      (norm_comp_linearizedExponentialComposition_lt_one G hN hN1 hsmall η u))).apply_symm_apply v
  change perronLinearResponse G hN hN1 hsmall η u v -
    G (linearizedExponentialComposition hN hN1 η u
      (perronLinearResponse G hN hN1 hsmall η u v)) = v at h
  exact sub_eq_iff_eq_add.mp h

/-- Every solution of the linearized equation equals the constructed response. -/
theorem perronLinearResponse_unique (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (hsmall : ‖G‖ * L < 1) (η : ℝ) (u v x : ℝ →ᵇ E)
    (hx : x = v + G (linearizedExponentialComposition hN hN1 η u x)) :
    x = perronLinearResponse G hN hN1 hsmall η u v := by
  let e := ContinuousLinearEquiv.ofUnit
    (Units.oneSub (G.comp (linearizedExponentialComposition hN hN1 η u))
      (norm_comp_linearizedExponentialComposition_lt_one G hN hN1 hsmall η u))
  apply e.injective
  change e x = e (e.symm v)
  rw [e.apply_symm_apply]
  exact sub_eq_iff_eq_add.mpr hx

/-- The response bound uses the same contraction margin for every base path. -/
theorem norm_perronLinearResponse_le (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (hsmall : ‖G‖ * L < 1) (η : ℝ) (u : ℝ →ᵇ E) :
    ‖perronLinearResponse G hN hN1 hsmall η u‖ ≤ (1 - ‖G‖ * L)⁻¹ := by
  have hpos : 0 < 1 - ‖G‖ * L := sub_pos.mpr hsmall
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hpos.le)
  intro v
  let x := perronLinearResponse G hN hN1 hsmall η u v
  let D := linearizedExponentialComposition hN hN1 η u
  have hg : ‖G (D x)‖ ≤ (‖G‖ * L) * ‖x‖ := by
    calc
      ‖G (D x)‖ ≤ ‖G‖ * ‖D x‖ := G.le_opNorm _
      _ ≤ ‖G‖ * (L * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          (D.le_of_opNorm_le_of_le
            (norm_linearizedExponentialComposition_le hN hN1 η u) le_rfl) (norm_nonneg G)
      _ = (‖G‖ * L) * ‖x‖ := (mul_assoc _ _ _).symm
  have hx : ‖x‖ ≤ ‖v‖ + (‖G‖ * L) * ‖x‖ := by
    calc
      ‖x‖ = ‖v + G (D x)‖ := congrArg norm (perronLinearResponse_eq G hN hN1 hsmall η u v)
      _ ≤ ‖v‖ + ‖G (D x)‖ := norm_add_le _ _
      _ ≤ ‖v‖ + (‖G‖ * L) * ‖x‖ := add_le_add le_rfl hg
  calc
    ‖x‖ ≤ ‖v‖ / (1 - ‖G‖ * L) := (le_div_iff₀ hpos).mpr (by nlinarith [hx])
    _ = (1 - ‖G‖ * L)⁻¹ * ‖v‖ := by rw [div_eq_mul_inv, mul_comm]

/-- Independently invertible linearizations give one physical variation after
a weight change, using the Green intertwining identity. -/
theorem increaseExponentialWeight_perronLinearResponse
    {α β : ℝ} (hαβ : α ≤ β) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ v, increaseExponentialWeight hαβ (G v) = H (increaseExponentialWeight hαβ v))
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1)
    (η : ℝ) (u v : ℝ →ᵇ E) :
    increaseExponentialWeight hαβ (perronLinearResponse G hN hN1 hsmallG η u v) =
      perronLinearResponse H hN hN1 hsmallH η u (increaseExponentialWeight hαβ v) := by
  apply perronLinearResponse_unique
  conv_lhs => rw [perronLinearResponse_eq]
  rw [map_add, hcomm, increaseExponentialWeight_linearizedExponentialComposition]

/-- Identify the derivative of the nonlinear fixed path with the
constructed linear response at the doubled weight. -/
theorem hasFDerivAt_increaseExponentialWeight_perronPath
    {η : ℝ} (hη : 0 ≤ η) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ v, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G v) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) v))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN2 : ContDiff ℝ 2 N)
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ N) x‖ ≤ M)
    (z : ℝ →ᵇ E) :
    HasFDerivAt
      (fun w ↦ increaseExponentialWeight (by linarith : η ≤ 2 * η)
        (perronPath η G hN hN0 hsmallG w))
      ((perronLinearResponse H hN (hN2.of_le (by norm_num)) hsmallH η
        (perronPath η G hN hN0 hsmallG z)).comp
          (increaseExponentialWeight (by linarith : η ≤ 2 * η))) z := by
  obtain ⟨d, hd, he⟩ := exists_hasFDerivAt_increaseExponentialWeight_perronPath
    hη G H hcomm hN hN0 hN2 hsmallG hsmallH hM hbound z
  have heq : d =
      (perronLinearResponse H hN (hN2.of_le (by norm_num)) hsmallH η
        (perronPath η G hN hN0 hsmallG z)).comp
          (increaseExponentialWeight (by linarith : η ≤ 2 * η)) := by
    apply ContinuousLinearMap.ext
    intro v
    apply perronLinearResponse_unique H hN (hN2.of_le (by norm_num)) hsmallH η
      (perronPath η G hN hN0 hsmallG z)
      (increaseExponentialWeight (by linarith : η ≤ 2 * η) v) (d v)
    have h := congrArg (fun A : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) ↦ A v) he
    change d v - H (linearizedExponentialComposition hN (hN2.of_le (by norm_num)) η
      (perronPath η G hN hN0 hsmallG z) (d v)) =
        increaseExponentialWeight (by linarith : η ≤ 2 * η) v at h
    exact sub_eq_iff_eq_add.mp h
  rwa [heq] at hd

end PDE.Analysis.Evolution
