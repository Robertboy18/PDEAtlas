/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.LinearResponse
public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.Hessian

/-!
# Construction of the second linear response

The Hessian acts on two first variations. The Green operator and the
inverse linearized equation then give a bounded bilinear response in any
admissible weight at least `2η`. Differentiability is proved separately from
the quadratic residual of the fixed path.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L M : ℝ≥0} {N : E → E}

/-- Solve the second linearized equation using the Hessian and two
constructed first responses. -/
def perronSecondResponse {η θ : ℝ} (hηθ : 2 * η ≤ θ)
    (G V : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN2 : ContDiff ℝ 2 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hsmallG : ‖G‖ * L < 1) (hsmallV : ‖V‖ * L < 1) (u : ℝ →ᵇ E) :
    (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  let R := perronLinearResponse G hN (hN2.of_le (by norm_num)) hsmallG η u
  let S := perronLinearResponse V hN (hN2.of_le (by norm_num)) hsmallV η u
  (ContinuousLinearMap.compL ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (ℝ →ᵇ E)
    (S.comp (V.comp (increaseExponentialWeight hηθ)))).comp
      ((secondExponentialComposition hDN hN2 η u).bilinearComp R R)

/-- Evaluation is the Hessian forcing followed by the Green
operator and the inverse linearized equation. -/
@[simp] theorem perronSecondResponse_apply {η θ : ℝ} (hηθ : 2 * η ≤ θ)
    (G V : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN2 : ContDiff ℝ 2 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hsmallG : ‖G‖ * L < 1) (hsmallV : ‖V‖ * L < 1) (u a b : ℝ →ᵇ E) :
    perronSecondResponse hηθ G V hN hN2 hDN hsmallG hsmallV u a b =
      perronLinearResponse V hN (hN2.of_le (by norm_num)) hsmallV η u
        (V (increaseExponentialWeight hηθ
          (secondExponentialComposition hDN hN2 η u
            (perronLinearResponse G hN (hN2.of_le (by norm_num)) hsmallG η u a)
            (perronLinearResponse G hN (hN2.of_le (by norm_num)) hsmallG η u b)))) := rfl

/-- The second response has a uniform bilinear norm bound in every base path. -/
theorem norm_perronSecondResponse_le {η θ : ℝ} (hηθ : 2 * η ≤ θ)
    (G V : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN2 : ContDiff ℝ 2 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hsmallG : ‖G‖ * L < 1) (hsmallV : ‖V‖ * L < 1) (u : ℝ →ᵇ E) :
    ‖perronSecondResponse hηθ G V hN hN2 hDN hsmallG hsmallV u‖ ≤
      (1 - ‖V‖ * L)⁻¹ * ‖V‖ * M * (1 - ‖G‖ * L)⁻¹ ^ 2 := by
  let A := (1 - ‖G‖ * L)⁻¹
  let B := (1 - ‖V‖ * L)⁻¹
  let R := perronLinearResponse G hN (hN2.of_le (by norm_num)) hsmallG η u
  let S := perronLinearResponse V hN (hN2.of_le (by norm_num)) hsmallV η u
  let Q := secondExponentialComposition hDN hN2 η u
  let J := increaseExponentialWeight (E := E) hηθ
  have hA : 0 ≤ A := inv_nonneg.mpr (sub_pos.mpr hsmallG).le
  have hB : 0 ≤ B := inv_nonneg.mpr (sub_pos.mpr hsmallV).le
  have hR (a : ℝ →ᵇ E) : ‖R a‖ ≤ A * ‖a‖ :=
    R.le_of_opNorm_le_of_le (norm_perronLinearResponse_le G hN
      (hN2.of_le (by norm_num)) hsmallG η u) le_rfl
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ B * ‖V‖ * M * A ^ 2)
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _
    (by positivity : 0 ≤ B * ‖V‖ * M * A ^ 2 * ‖a‖)
  intro b
  change ‖S (V (J (Q (R a) (R b))))‖ ≤ _
  calc
    ‖S (V (J (Q (R a) (R b))))‖ ≤ B * ‖V (J (Q (R a) (R b)))‖ :=
      S.le_of_opNorm_le_of_le (norm_perronLinearResponse_le V hN
        (hN2.of_le (by norm_num)) hsmallV η u) le_rfl
    _ ≤ B * (‖V‖ * ‖J (Q (R a) (R b))‖) := mul_le_mul_of_nonneg_left (V.le_opNorm _) hB
    _ ≤ B * (‖V‖ * ‖Q (R a) (R b)‖) := by
      gcongr
      simpa only [one_mul] using J.le_of_opNorm_le_of_le
        (norm_increaseExponentialWeight_le hηθ) (le_rfl (a := ‖Q (R a) (R b)‖))
    _ ≤ B * (‖V‖ * (M * (A * ‖a‖) * (A * ‖b‖))) := by
      gcongr
      exact Q.le_of_opNorm₂_le_of_le
        (norm_secondExponentialComposition_le hDN hN2 η u) (hR a) (hR b)
    _ = _ := by ring

end PDE.Analysis.Evolution
