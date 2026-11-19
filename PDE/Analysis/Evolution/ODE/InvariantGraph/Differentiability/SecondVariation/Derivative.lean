/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.SecondVariation.Construction
public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.SecondVariation.Residual

/-!
# Differentiating the first variation

The operator-valued first response satisfies a linearized equation whose
residual is quadratic in the homogeneous perturbation at weight `3η`.
The third contraction makes its left side invertible. Its derivative is the
constructed second response, using the Hessian and the first
variations.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L M K : ℝ≥0} {N : E → E}

/-- The first variation is Fréchet differentiable into the third
weight. All three contraction bounds are used, and the derivative is the
constructed second response. -/
theorem hasFDerivAt_increaseExponentialWeight_perronLinearResponse
    {η : ℝ} (hη : 0 ≤ η) (G H V : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm12 : ∀ x, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G x) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) x))
    (hcomm13 : ∀ x, increaseExponentialWeight (by linarith : η ≤ 3 * η) (G x) =
      V (increaseExponentialWeight (by linarith : η ≤ 3 * η) x))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN3 : ContDiff ℝ 3 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hDDN : LipschitzWith K (fderiv ℝ (fderiv ℝ N)))
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1) (hsmallV : ‖V‖ * L < 1)
    (z : ℝ →ᵇ E) :
    HasFDerivAt
      (fun w ↦ (increaseExponentialWeight (by linarith : η ≤ 3 * η)).comp
        (perronLinearResponse G hN (hN3.of_le (by norm_num)) hsmallG η
          (perronPath η G hN hN0 hsmallG w)))
      (perronSecondResponse (by linarith : 2 * η ≤ 3 * η) G V hN
        (hN3.of_le (by norm_num)) hDN hsmallG hsmallV
          (perronPath η G hN hN0 hsmallG z)) z := by
  let P := perronPath η G hN hN0 hsmallG
  let R := perronLinearResponse G hN (hN3.of_le (by norm_num)) hsmallG η
  let D := linearizedExponentialComposition hN (hN3.of_le (by norm_num)) η
  let Q := secondExponentialComposition hDN (hN3.of_le (by norm_num)) η (P z)
  let J13 := increaseExponentialWeight (E := E) (by linarith : η ≤ 3 * η)
  let J23 := increaseExponentialWeight (E := E) (by linarith : 2 * η ≤ 3 * η)
  let F := fun w ↦ J13.comp (R (P w))
  let T := ContinuousLinearMap.compL ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (ℝ →ᵇ E) (V.comp (D (P z)))
  let B := (ContinuousLinearMap.compL ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (ℝ →ᵇ E)
    (V.comp J23)).comp (Q.bilinearComp (R (P z)) (R (P z)))
  let A := (1 - ‖G‖ * L)⁻¹
  let C := K * A ^ 3 +
    2 * M * A * ((1 - ‖H‖ * L)⁻¹ * ‖H‖ * M * A ^ 2)
  have hT : ‖T‖ < 1 :=
    (T.opNorm_le_bound (norm_nonneg _) fun S ↦ (V.comp (D (P z))).opNorm_comp_le S).trans_lt
      (norm_comp_linearizedExponentialComposition_lt_one V hN (hN3.of_le (by norm_num)) hsmallV η
        (P z))
  have hr (w : ℝ →ᵇ E) :
      ‖F w - F z - T (F w - F z) - B (w - z)‖ ≤ ‖V‖ * C * ‖w - z‖ ^ 2 := by
    let S := (J13.comp (D (P w) - D (P z))).comp (R (P w)) -
      (J23.comp (Q (R (P z) (w - z)))).comp (R (P z))
    have he : F w - F z - T (F w - F z) - B (w - z) = V.comp S := by
      refine ContinuousLinearMap.ext fun x ↦ ?_
      have hi := increaseExponentialWeight_perronLinearResponse_sub
        (by linarith : η ≤ 3 * η) G V hcomm13 hN (hN3.of_le (by norm_num))
          hsmallG hsmallV η (P z) (P w) x
      have hl := perronLinearResponse_eq V hN (hN3.of_le (by norm_num)) hsmallV η (P z)
        (V (J13 ((D (P w) - D (P z)) (R (P w) x))))
      rw [← hi] at hl
      have hl' :
          J13 (R (P w) x) - J13 (R (P z) x) =
            V (J13 ((D (P w) - D (P z)) (R (P w) x))) +
              V (D (P z) (J13 (R (P w) x) - J13 (R (P z) x))) := by
        simpa only [map_sub] using hl
      change J13 (R (P w) x) - J13 (R (P z) x) -
        V (D (P z) (J13 (R (P w) x) - J13 (R (P z) x))) -
        V (J23 (Q (R (P z) (w - z)) (R (P z) x))) =
          V (J13 ((D (P w) - D (P z)) (R (P w) x)) -
            J23 (Q (R (P z) (w - z)) (R (P z) x)))
      rw [V.map_sub]
      exact congrArg (· - V (J23 (Q (R (P z) (w - z)) (R (P z) x))))
        (sub_eq_iff_eq_add.mpr hl')
    rw [he, mul_assoc]
    exact (V.opNorm_comp_le S).trans (mul_le_mul_of_nonneg_left
      (norm_perron_second_variation_residual_le hη G H hcomm12 hN hN0 hN3 hDN hDDN hsmallG
        hsmallH z w) (norm_nonneg V))
  have hd := hasFDerivAt_of_quadratic_contraction_residual F z T hT B (‖V‖ * C) hr
  let e := ContinuousLinearEquiv.ofUnit (Units.oneSub T hT)
  have heq : e.symm.toContinuousLinearMap.comp B =
      perronSecondResponse (by linarith : 2 * η ≤ 3 * η) G V hN
        (hN3.of_le (by norm_num)) hDN hsmallG hsmallV (P z) := by
    refine ContinuousLinearMap.ext fun a ↦ ContinuousLinearMap.ext fun b ↦ ?_
    change (e.symm (B a)) b =
      perronLinearResponse V hN (hN3.of_le (by norm_num)) hsmallV η (P z)
        (V (J23 (Q (R (P z) a) (R (P z) b))))
    apply perronLinearResponse_unique V hN (hN3.of_le (by norm_num)) hsmallV η (P z)
    have he := congrArg (fun S : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) ↦ S b) (e.apply_symm_apply (B a))
    change (e.symm (B a)) b - V (D (P z) ((e.symm (B a)) b)) =
      V (J23 (Q (R (P z) a) (R (P z) b))) at he
    exact sub_eq_iff_eq_add.mp he
  rwa [heq] at hd

end PDE.Analysis.Evolution
