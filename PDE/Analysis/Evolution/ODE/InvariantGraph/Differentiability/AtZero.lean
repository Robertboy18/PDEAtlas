/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.LinearResponse

/-!
# The first variation at the zero path

When the nonlinear remainder and its derivative vanish at zero, the constructed
zero path has the identity first response. Consequently its derivative with
respect to the homogeneous term is exactly the change of exponential weight.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {L M : ℝ≥0} {N : E → E}

/-- A vanishing derivative of the nonlinear remainder makes the first
response at the zero path the identity. -/
theorem perronLinearResponse_zero
    (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E)) (hN : LipschitzWith L N)
    (hN1 : ContDiff ℝ 1 N) (hsmall : ‖G‖ * L < 1)
    (hDN0 : fderiv ℝ N 0 = 0) (η : ℝ) :
    perronLinearResponse G hN hN1 hsmall η 0 = ContinuousLinearMap.id ℝ (ℝ →ᵇ E) := by
  have hD (v : ℝ →ᵇ E) : linearizedExponentialComposition hN hN1 η 0 v = 0 := by
    ext t
    change fderiv ℝ N (Real.exp (η * |t|) • (0 : E)) (v t) = 0
    rw [smul_zero, hDN0, zero_apply]
  apply ContinuousLinearMap.ext
  intro v
  change perronLinearResponse G hN hN1 hsmall η 0 v = v
  rw [perronLinearResponse_eq, hD, map_zero, add_zero]

/-- The derivative of the fixed path at the origin is precisely the
inclusion into the doubled exponential weight. -/
theorem hasFDerivAt_increaseExponentialWeight_perronPath_zero
    {η : ℝ} (hη : 0 ≤ η) (G H : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hcomm : ∀ v, increaseExponentialWeight (by linarith : η ≤ 2 * η) (G v) =
      H (increaseExponentialWeight (by linarith : η ≤ 2 * η) v))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN2 : ContDiff ℝ 2 N)
    (hDN : LipschitzWith M (fderiv ℝ N)) (hDN0 : fderiv ℝ N 0 = 0)
    (hsmallG : ‖G‖ * L < 1) (hsmallH : ‖H‖ * L < 1) :
    HasFDerivAt
      (fun z ↦ increaseExponentialWeight (by linarith : η ≤ 2 * η)
        (perronPath η G hN hN0 hsmallG z))
      (increaseExponentialWeight (by linarith : η ≤ 2 * η)) 0 := by
  have hp := hasFDerivAt_increaseExponentialWeight_perronPath hη G H hcomm hN hN0 hN2
    hsmallG hsmallH M.coe_nonneg (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hDN) 0
  rw [perronPath_zero, perronLinearResponse_zero H hN (hN2.of_le (by norm_num))
    hsmallH hDN0 η] at hp
  simpa only [ContinuousLinearMap.id_comp] using hp

end PDE.Analysis.Evolution
