/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.ResponseVariation
public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.Remainder
public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.CoefficientRemainder

/-!
# The second-variation residual in the third weight

The residual has three terms: the Taylor remainder of the first derivative,
the change of the linear response, and the first-order remainder of the base
path. Each is quadratic in the homogeneous perturbation after passing to
weight `3η`.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L M K : ℝ≥0} {N : E → E}

/-- The coefficient variation applied to the perturbed response has the
Hessian as its first-order term, with a quadratic remainder in weight
`3η`. Only the first two contraction margins enter this residual estimate. -/
theorem norm_perron_second_variation_residual_le
    {η : ℝ} (hη : 0 ≤ η) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ x, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G x) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) x))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN3 : ContDiff ℝ 3 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hDDN : LipschitzWith K (fderiv ℝ (fderiv ℝ N)))
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1)
    (z w : ℝ →ᵇ E) :
    let P := perronPath η G hN hN0 hsmallG
    let R := perronLinearResponse G hN (hN3.of_le (by norm_num)) hsmallG η
    let D := linearizedExponentialComposition hN (hN3.of_le (by norm_num)) η
    let Q := secondExponentialComposition hDN (hN3.of_le (by norm_num)) η
    let A := (1 - ‖G‖ * L)⁻¹
    let B := (1 - ‖H‖ * L)⁻¹ * ‖H‖ * M * A ^ 2
    ‖((increaseExponentialWeight (by linarith : η ≤ 3 * η)).comp
        (D (P w) - D (P z))).comp (R (P w)) -
      ((increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η)).comp
        (Q (P z) (R (P z) (w - z)))).comp (R (P z))‖ ≤
      (K * A ^ 3 + 2 * M * A * B) * ‖w - z‖ ^ 2 := by
  dsimp only
  let P := perronPath η G hN hN0 hsmallG
  let R := perronLinearResponse G hN (hN3.of_le (by norm_num)) hsmallG η
  let D := linearizedExponentialComposition hN (hN3.of_le (by norm_num)) η
  let Q := secondExponentialComposition hDN (hN3.of_le (by norm_num)) η (P z)
  let J12 := increaseExponentialWeight (E := E) (by linarith : η ≤ 2 * η)
  let J23 := increaseExponentialWeight (E := E) (by linarith : 2 * η ≤ 3 * η)
  let J13 := increaseExponentialWeight (E := E) (by linarith : η ≤ 3 * η)
  let A := (1 - ‖G‖ * L)⁻¹
  let B := (1 - ‖H‖ * L)⁻¹ * ‖H‖ * M * A ^ 2
  have hA : 0 ≤ A := inv_nonneg.mpr (sub_pos.mpr hsmallG).le
  have hH : 0 ≤ (1 - ‖H‖ * L)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hsmallH).le
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hp : ‖P w - P z‖ ≤ A * ‖w - z‖ := by
    simpa only [dist_eq_norm, div_eq_inv_mul] using dist_perronPath_le η G hN hN0 hsmallG w z
  have hR (v x : ℝ →ᵇ E) : ‖R v x‖ ≤ A * ‖x‖ :=
    (R v).le_of_opNorm_le_of_le
      (norm_perronLinearResponse_le G hN (hN3.of_le (by norm_num)) hsmallG η v) le_rfl
  have hQ : ‖Q‖ ≤ M :=
    norm_secondExponentialComposition_le hDN (hN3.of_le (by norm_num)) η (P z)
  have hRv : ‖J12.comp (R (P w) - R (P z))‖ ≤ B * ‖w - z‖ := by
    refine (show _ ≤ (1 - ‖H‖ * L)⁻¹ * ‖H‖ * M * ‖P w - P z‖ * A by
      simpa only [← two_mul] using norm_increaseExponentialWeight_perronLinearResponse_sub_le
        hη η G H (fun v ↦ by simpa only [two_mul] using hcomm v) hN (hN3.of_le (by norm_num))
        hDN hsmallG hsmallH (P z) (P w)).trans ?_
    calc _ ≤ (1 - ‖H‖ * L)⁻¹ * ‖H‖ * M * (A * ‖w - z‖) * A := by gcongr
      _ = B * ‖w - z‖ := by dsimp only [B]; ring
  have hPr : ‖J12 (P w - P z - R (P z) (w - z))‖ ≤ B * ‖w - z‖ ^ 2 :=
    norm_increaseExponentialWeight_perronPath_remainder_le hη G H hcomm hN hN0
      (hN3.of_le (by norm_num)) hDN hsmallG hsmallH z w
  have hQr (a b : ℝ →ᵇ E) : J23 (Q a b) = Q a (J12 b) := by
    simpa only [show η + η = 2 * η by ring, show η + 2 * η = 3 * η by ring] using
      increaseExponentialWeight_secondExponentialComposition
        hDN (hN3.of_le (by norm_num)) η η (by linarith : η ≤ 2 * η) (P z) a b
  have hQl (a b : ℝ →ᵇ E) : J23 (Q a b) = Q (J12 a) b := by
    simpa only [show η + η = 2 * η by ring, show 2 * η + η = 3 * η by ring] using
      increaseExponentialWeight_secondExponentialComposition_left
        hDN (hN3.of_le (by norm_num)) η η (by linarith : η ≤ 2 * η) (P z) a b
  let T := J13.comp (D (P w) - D (P z)) - J23.comp (Q (P w - P z))
  have hT : ‖T‖ ≤ K * ‖P w - P z‖ ^ 2 := by
    simpa only [show η + 2 * η = 3 * η by ring, show η + η = 2 * η by ring] using
      norm_increaseExponentialWeight_linearized_remainder_le hη η hN hN3 hDN hDDN (P z) (P w)
  apply ContinuousLinearMap.opNorm_le_bound _
    (by positivity : 0 ≤ (K * A ^ 3 + 2 * M * A * B) * ‖w - z‖ ^ 2)
  intro x
  let t1 := T (R (P w) x)
  let t2 := J23 (Q (P w - P z) (R (P w) x - R (P z) x))
  let t3 := J23 (Q (P w - P z - R (P z) (w - z)) (R (P z) x))
  have he :
      ((J13.comp (D (P w) - D (P z))).comp (R (P w)) -
        (J23.comp (Q (R (P z) (w - z)))).comp (R (P z))) x = t1 + t2 + t3 := by
    dsimp only [t1, t2, t3, T]
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply, map_sub]
    abel
  rw [he]
  have ht1 : ‖t1‖ ≤ K * (A * ‖w - z‖) ^ 2 * (A * ‖x‖) :=
    (T.le_of_opNorm_le_of_le hT (hR (P w) x)).trans (by gcongr)
  have ht2 : ‖t2‖ ≤ M * (A * ‖w - z‖) * (B * ‖w - z‖ * ‖x‖) := by
    rw [show t2 = Q (P w - P z) (J12 (R (P w) x - R (P z) x)) from hQr _ _]
    exact Q.le_of_opNorm₂_le_of_le hQ hp
      ((J12.comp (R (P w) - R (P z))).le_of_opNorm_le_of_le hRv le_rfl)
  have ht3 : ‖t3‖ ≤ M * (B * ‖w - z‖ ^ 2) * (A * ‖x‖) := by
    rw [show t3 = Q (J12 (P w - P z - R (P z) (w - z))) (R (P z) x) from hQl _ _]
    exact Q.le_of_opNorm₂_le_of_le hQ hPr (hR (P z) x)
  linarith [norm_add₃_le (a := t1) (b := t2) (c := t3)]

end PDE.Analysis.Evolution
