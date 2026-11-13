/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.SecondVariation.Construction
public import
  PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.SecondVariation.ForcingVariation

/-!
# Continuity of the second response

The second response is Lipschitz into the third weight. One term comes from
the change of the inverse linearized equation, and the other from the change
of its Hessian forcing. Coherence of the second and third inverses
avoids introducing a fourth weight.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L M K : ℝ≥0} {N : E → E}

/-- The constructed second response has a quantitative Lipschitz bound in
the base path. The first three contraction margins suffice. -/
theorem norm_perronSecondResponse_sub_le
    {η : ℝ} (hη : 0 ≤ η) (G H V : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm12 : ∀ x, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G x) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) x))
    (hcomm23 : ∀ x, increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η) (H x) =
      V (increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η) x))
    (hN : LipschitzWith L N) (hN2 : ContDiff ℝ 2 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hDDN : LipschitzWith K (fderiv ℝ (fderiv ℝ N)))
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1) (hsmallV : ‖V‖ * L < 1)
    (u v : ℝ →ᵇ E) :
    ‖perronSecondResponse (by linarith : 2 * η ≤ 3 * η) G V hN hN2 hDN
        hsmallG hsmallV v -
      perronSecondResponse (by linarith : 2 * η ≤ 3 * η) G V hN hN2 hDN
        hsmallG hsmallV u‖ ≤
      (1 - ‖V‖ * L)⁻¹ * ‖V‖ *
        (K + 3 * (1 - ‖H‖ * L)⁻¹ * ‖H‖ * M ^ 2) *
          (1 - ‖G‖ * L)⁻¹ ^ 2 * ‖v - u‖ := by
  let A := (1 - ‖G‖ * L)⁻¹
  let B := (1 - ‖H‖ * L)⁻¹
  let C := (1 - ‖V‖ * L)⁻¹
  let R := perronLinearResponse G hN (hN2.of_le (by norm_num)) hsmallG η
  let S := perronLinearResponse H hN (hN2.of_le (by norm_num)) hsmallH η
  let T := perronLinearResponse V hN (hN2.of_le (by norm_num)) hsmallV η
  let Q := secondExponentialComposition hDN hN2 η
  let F := fun w a b ↦ Q w (R w a) (R w b)
  let J := increaseExponentialWeight (E := E) (by linarith : 2 * η ≤ 3 * η)
  have hA : 0 ≤ A := inv_nonneg.mpr (sub_pos.mpr hsmallG).le
  have hB : 0 ≤ B := inv_nonneg.mpr (sub_pos.mpr hsmallH).le
  have hC : 0 ≤ C := inv_nonneg.mpr (sub_pos.mpr hsmallV).le
  have hR (w x : ℝ →ᵇ E) : ‖R w x‖ ≤ A * ‖x‖ :=
    (R w).le_of_opNorm_le_of_le
      (norm_perronLinearResponse_le G hN (hN2.of_le (by norm_num)) hsmallG η w) le_rfl
  have hF (w a b : ℝ →ᵇ E) : ‖F w a b‖ ≤ M * A ^ 2 * ‖a‖ * ‖b‖ :=
    ((Q w).le_of_opNorm₂_le_of_le (norm_secondExponentialComposition_le hDN hN2 η w)
      (hR w a) (hR w b)).trans_eq (by ring)
  have hcoh (w y : ℝ →ᵇ E) : J (S w (H y)) = T w (V (J y)) :=
    (increaseExponentialWeight_perronLinearResponse (by linarith : 2 * η ≤ 3 * η)
      H V hcomm23 hN (hN2.of_le (by norm_num)) hsmallH hsmallV η w (H y)).trans
      (congrArg (T w) (hcomm23 y))
  have hD : ‖J.comp (S v - S u)‖ ≤ C * ‖V‖ * M * ‖v - u‖ * B := by
    simpa only [show 2 * η + η = 3 * η by ring] using
      norm_increaseExponentialWeight_perronLinearResponse_sub_le hη (2 * η) H V
        (by simpa only [show 2 * η + η = 3 * η by ring] using hcomm23)
        hN (hN2.of_le (by norm_num)) hDN hsmallH hsmallV u v
  apply ContinuousLinearMap.opNorm_le_bound _
    (by positivity : 0 ≤ C * ‖V‖ * (K + 3 * B * ‖H‖ * M ^ 2) * A ^ 2 * ‖v - u‖)
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _
    (by positivity : 0 ≤ C * ‖V‖ * (K + 3 * B * ‖H‖ * M ^ 2) *
      A ^ 2 * ‖v - u‖ * ‖a‖)
  intro b
  have he :
      T v (V (J (F v a b))) - T u (V (J (F u a b))) =
        J (S v (H (F v a b)) - S u (H (F v a b))) +
          T u (V (J (F v a b - F u a b))) := by
    rw [J.map_sub, hcoh, hcoh]
    simp only [map_sub]
    abel
  change ‖T v (V (J (F v a b))) - T u (V (J (F u a b)))‖ ≤ _
  have h1 : ‖J (S v (H (F v a b)) - S u (H (F v a b)))‖ ≤
      (C * ‖V‖ * M * ‖v - u‖ * B) * (‖H‖ * (M * A ^ 2 * ‖a‖ * ‖b‖)) :=
    (J.comp (S v - S u)).le_of_opNorm_le_of_le hD (H.le_of_opNorm_le_of_le le_rfl (hF v a b))
  have h2 : ‖T u (V (J (F v a b - F u a b)))‖ ≤
      C * (‖V‖ * ((K + 2 * B * ‖H‖ * M ^ 2) * A ^ 2 * ‖v - u‖ * ‖a‖ * ‖b‖)) :=
    (T u).le_of_opNorm_le_of_le
      (norm_perronLinearResponse_le V hN (hN2.of_le (by norm_num)) hsmallV η u)
      (V.le_of_opNorm_le_of_le le_rfl (norm_increaseExponentialWeight_perron_second_forcing_sub_le
        hη G H hcomm12 hN hN2 hDN hDDN hsmallG hsmallH u v a b))
  rw [he]
  linarith [norm_add_le (J (S v (H (F v a b)) - S u (H (F v a b))))
    (T u (V (J (F v a b - F u a b))))]

/-- The second response varies continuously in its base path at the
third weight. -/
theorem continuous_perronSecondResponse
    {η : ℝ} (hη : 0 ≤ η) (G H V : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm12 : ∀ x, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G x) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) x))
    (hcomm23 : ∀ x, increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η) (H x) =
      V (increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η) x))
    (hN : LipschitzWith L N) (hN2 : ContDiff ℝ 2 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hDDN : LipschitzWith K (fderiv ℝ (fderiv ℝ N)))
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1) (hsmallV : ‖V‖ * L < 1) :
    Continuous (perronSecondResponse (by linarith : 2 * η ≤ 3 * η) G V hN hN2 hDN
      hsmallG hsmallV) := by
  have hH : 0 ≤ (1 - ‖H‖ * L)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hsmallH).le
  have hV : 0 ≤ (1 - ‖V‖ * L)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hsmallV).le
  let C : ℝ≥0 := ⟨(1 - ‖V‖ * L)⁻¹ * ‖V‖ *
    (K + 3 * (1 - ‖H‖ * L)⁻¹ * ‖H‖ * M ^ 2) *
      (1 - ‖G‖ * L)⁻¹ ^ 2, by positivity⟩
  have hLip : LipschitzWith C
      (perronSecondResponse (by linarith : 2 * η ≤ 3 * η) G V hN hN2 hDN
        hsmallG hsmallV) := LipschitzWith.of_dist_le_mul fun v u ↦ by
    simp only [dist_eq_norm]
    convert norm_perronSecondResponse_sub_le hη G H V hcomm12 hcomm23 hN hN2 hDN hDDN
      hsmallG hsmallH hsmallV u v using 1
    rfl
  exact hLip.continuous

end PDE.Analysis.Evolution
