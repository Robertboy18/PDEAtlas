/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.ResponseVariation
public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.HessianVariation

/-!
# Variation of the second linearized forcing

The Hessian forcing changes through its base path and its two first
variations. Each change costs one exponential weight. Thus its difference
has a Lipschitz bound at the third weight, using the first two contractions.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L M K : ℝ≥0} {N : E → E}

/-- The Hessian forcing is Lipschitz in its base path after increasing
the output from the second to the third weight. -/
theorem norm_increaseExponentialWeight_perron_second_forcing_sub_le
    {η : ℝ} (hη : 0 ≤ η) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ x, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G x) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) x))
    (hN : LipschitzWith L N) (hN2 : ContDiff ℝ 2 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hDDN : LipschitzWith K (fderiv ℝ (fderiv ℝ N)))
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1)
    (u v a b : ℝ →ᵇ E) :
    let R := perronLinearResponse G hN (hN2.of_le (by norm_num)) hsmallG η
    let Q := secondExponentialComposition hDN hN2 η
    ‖increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η)
      (Q v (R v a) (R v b) - Q u (R u a) (R u b))‖ ≤
      (K + 2 * (1 - ‖H‖ * L)⁻¹ * ‖H‖ * M ^ 2) *
        (1 - ‖G‖ * L)⁻¹ ^ 2 * ‖v - u‖ * ‖a‖ * ‖b‖ := by
  dsimp only
  let A := (1 - ‖G‖ * L)⁻¹
  let B := (1 - ‖H‖ * L)⁻¹
  let R := perronLinearResponse G hN (hN2.of_le (by norm_num)) hsmallG η
  let Q := secondExponentialComposition hDN hN2 η
  let J12 := increaseExponentialWeight (E := E) (by linarith : η ≤ 2 * η)
  let J23 := increaseExponentialWeight (E := E) (by linarith : 2 * η ≤ 3 * η)
  have hA : 0 ≤ A := inv_nonneg.mpr (sub_pos.mpr hsmallG).le
  have hB : 0 ≤ B := inv_nonneg.mpr (sub_pos.mpr hsmallH).le
  have hR (w x : ℝ →ᵇ E) : ‖R w x‖ ≤ A * ‖x‖ :=
    (R w).le_of_opNorm_le_of_le
      (norm_perronLinearResponse_le G hN (hN2.of_le (by norm_num)) hsmallG η w) le_rfl
  have hD (x : ℝ →ᵇ E) :
      ‖J12 (R v x - R u x)‖ ≤ B * ‖H‖ * M * ‖v - u‖ * A * ‖x‖ := by
    have hd : ‖J12.comp (R v - R u)‖ ≤ B * ‖H‖ * M * ‖v - u‖ * A := by
      simpa only [← two_mul] using
        norm_increaseExponentialWeight_perronLinearResponse_sub_le hη η G H
          (by simpa only [← two_mul] using hcomm)
          hN (hN2.of_le (by norm_num)) hDN hsmallG hsmallH u v
    exact (J12.comp (R v - R u)).le_of_opNorm_le_of_le hd le_rfl
  have hQl (x y : ℝ →ᵇ E) : J23 (Q u x y) = Q u (J12 x) y := by
    simpa only [show η + η = 2 * η by ring, show 2 * η + η = 3 * η by ring] using
      increaseExponentialWeight_secondExponentialComposition_left hDN hN2 η η
        (by linarith : η ≤ 2 * η) u x y
  have hQr (x y : ℝ →ᵇ E) : J23 (Q u x y) = Q u x (J12 y) := by
    simpa only [show η + η = 2 * η by ring, show η + 2 * η = 3 * η by ring] using
      increaseExponentialWeight_secondExponentialComposition hDN hN2 η η
        (by linarith : η ≤ 2 * η) u x y
  have he :
      J23 (Q v (R v a) (R v b) - Q u (R u a) (R u b)) =
        J23 (Q v (R v a) (R v b) - Q u (R v a) (R v b)) +
          Q u (J12 (R v a - R u a)) (R v b) +
          Q u (R u a) (J12 (R v b - R u b)) := by
    rw [← hQl, ← hQr]
    simp only [map_sub, _root_.sub_apply]
    abel
  rw [he]
  calc
    ‖J23 (Q v (R v a) (R v b) - Q u (R v a) (R v b)) +
        Q u (J12 (R v a - R u a)) (R v b) +
        Q u (R u a) (J12 (R v b - R u b))‖ ≤
      ‖J23 (Q v (R v a) (R v b) - Q u (R v a) (R v b))‖ +
        ‖Q u (J12 (R v a - R u a)) (R v b)‖ +
        ‖Q u (R u a) (J12 (R v b - R u b))‖ := norm_add₃_le
    _ ≤ K * ‖v - u‖ * (A * ‖a‖) * (A * ‖b‖) +
        M * (B * ‖H‖ * M * ‖v - u‖ * A * ‖a‖) * (A * ‖b‖) +
        M * (A * ‖a‖) * (B * ‖H‖ * M * ‖v - u‖ * A * ‖b‖) := by
      apply add_le_add
      · apply add_le_add
        · calc
            _ ≤ K * ‖v - u‖ * ‖R v a‖ * ‖R v b‖ := by
              simpa only [show η + η = 2 * η by ring,
                show 2 * η + η = 3 * η by ring] using
                norm_increaseExponentialWeight_second_sub_le hη η η hN2 hDN hDDN
                  u v (R v a) (R v b)
            _ ≤ _ := by gcongr <;> apply hR
        · exact (Q u).le_of_opNorm₂_le_of_le
            (norm_secondExponentialComposition_le hDN hN2 η u) (hD a) (hR v b)
      · exact (Q u).le_of_opNorm₂_le_of_le
          (norm_secondExponentialComposition_le hDN hN2 η u) (hR u a) (hD b)
    _ = _ := by ring

end PDE.Analysis.Evolution
