/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.SecondVariation.Derivative
public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.SecondVariation.Continuity

/-!
# Twice continuous differentiability of the fixed path

Three compatible, independently contractive Green operators give a `C²`
Perron path from the first exponential weight to the third. Its first and
second derivatives are the constructed responses. Evaluation gives `C²` dependence of every
physical point of the path.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L M K : ℝ≥0} {N : E → E}

/-- The Perron fixed path is twice continuously differentiable after
increasing its exponential weight from `η` to `3η`. -/
theorem contDiff_two_increaseExponentialWeight_perronPath
    {η : ℝ} (hη : 0 ≤ η) (G H V : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm12 : ∀ x, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G x) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) x))
    (hcomm23 : ∀ x, increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η) (H x) =
      V (increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η) x))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN3 : ContDiff ℝ 3 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hDDN : LipschitzWith K (fderiv ℝ (fderiv ℝ N)))
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1) (hsmallV : ‖V‖ * L < 1) :
    ContDiff ℝ 2 (fun z ↦ increaseExponentialWeight (by linarith : η ≤ 3 * η)
      (perronPath η G hN hN0 hsmallG z)) := by
  let P := perronPath η G hN hN0 hsmallG
  let J12 := increaseExponentialWeight (E := E) (by linarith : η ≤ 2 * η)
  let J23 := increaseExponentialWeight (E := E) (by linarith : 2 * η ≤ 3 * η)
  let J13 := increaseExponentialWeight (E := E) (by linarith : η ≤ 3 * η)
  let R := perronLinearResponse G hN (hN3.of_le (by norm_num)) hsmallG η
  let d := fun z ↦ J13.comp (R (P z))
  let d₂ := perronSecondResponse (by linarith : 2 * η ≤ 3 * η) G V hN
    (hN3.of_le (by norm_num)) hDN hsmallG hsmallV
  have hJ (x : ℝ →ᵇ E) : J23 (J12 x) = J13 x := by
    dsimp only [J12, J23, J13]
    apply exponentialLift_injective (3 * η)
    ext t
    simp only [exponentialLift_increaseExponentialWeight]
  have hcomm13 (x : ℝ →ᵇ E) : J13 (G x) = V (J13 x) := by
    calc
      J13 (G x) = J23 (J12 (G x)) := (hJ (G x)).symm
      _ = J23 (H (J12 x)) := congrArg J23 (hcomm12 x)
      _ = V (J23 (J12 x)) := hcomm23 (J12 x)
      _ = V (J13 x) := congrArg V (hJ x)
  have hP : Continuous P := by
    let A : ℝ≥0 := ⟨(1 - ‖G‖ * L)⁻¹, inv_nonneg.mpr (sub_pos.mpr hsmallG).le⟩
    have hLip : LipschitzWith A P := LipschitzWith.of_dist_le_mul fun w z ↦ by
      calc
        dist (P w) (P z) ≤ dist w z / (1 - ‖G‖ * L) :=
          dist_perronPath_le η G hN hN0 hsmallG w z
        _ = A * dist w z := by
          rw [div_eq_mul_inv, mul_comm]
          rfl
    exact hLip.continuous
  have hd : ContDiff ℝ 1 d := by
    apply contDiff_one_iff_hasFDerivAt.mpr
    refine ⟨fun z ↦ d₂ (P z), ?_, ?_⟩
    · exact (continuous_perronSecondResponse hη G H V hcomm12 hcomm23 hN
        (hN3.of_le (by norm_num)) hDN hDDN hsmallG hsmallH hsmallV).comp hP
    · intro z
      exact hasFDerivAt_increaseExponentialWeight_perronLinearResponse
        hη G H V hcomm12 hcomm13 hN hN0 hN3 hDN hDDN hsmallG hsmallH hsmallV z
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨d, hd, fun z ↦ ?_⟩
  have hp := hasFDerivAt_increaseExponentialWeight_perronPath hη G H hcomm12 hN hN0
    (hN3.of_le (by norm_num)) hsmallG hsmallH M.coe_nonneg
      (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hDN) z
  have hd' := J23.hasFDerivAt.comp z hp
  have hf : (fun w ↦ J23 (J12 (P w))) = (fun w ↦ J13 (P w)) := funext fun w ↦ hJ (P w)
  have he :
      J23.comp ((perronLinearResponse H hN (hN3.of_le (by norm_num)) hsmallH η (P z)).comp
        J12) = d z := by
    apply ContinuousLinearMap.ext
    intro v
    change J23 (perronLinearResponse H hN (hN3.of_le (by norm_num)) hsmallH η (P z)
      (J12 v)) = J13 (R (P z) v)
    rw [← increaseExponentialWeight_perronLinearResponse
      (by linarith : η ≤ 2 * η) G H hcomm12 hN (hN3.of_le (by norm_num))
        hsmallG hsmallH η (P z) v]
    exact hJ (R (P z) v)
  change HasFDerivAt (fun w ↦ J23 (J12 (P w))) _ z at hd'
  rwa [hf, he] at hd'

end PDE.Analysis.Evolution
