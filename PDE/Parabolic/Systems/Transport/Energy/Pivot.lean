/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Energy.Coefficients

/-!
# Pivot energy of the symmetric transport operator

The bounded operator from H¹ to L² is the same negative matrix-gradient
contraction used by the transport equation. Its quadratic L² pairing is
controlled by spatial derivatives of the coefficient matrices. Continuous
W¹,∞ coefficient paths yield one bound on a compact time slab.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

variable {n m : ℕ}

/-- The transport operator is one-sided bounded in the L² pivot norm,
with the sum of the spatial coefficient derivative norms as constant. -/
theorem vectorTransportCLM_pivot_energy_le
    (A : Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ∀ j p q, wkpBaseCoordinateCLM (A j p q) = wkpBaseCoordinateCLM (A j q p))
    (U : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) :
    2 * ⟪WithLp.toLp 2 (vectorTransportCLM
      (fun j p q ↦ wkpBaseCoordinateCLM (A j p q)) (fun p ↦ U p)),
      WithLp.toLp 2 (fun p ↦ wkpBaseCoordinateCLM (U p))⟫_ℝ ≤
      (∑ j, ∑ p, ∑ q, ‖wkpCoordinateCLM (singleDerivIndex n j) (A j p q)‖) *
        ‖WithLp.toLp 2 (fun p ↦ wkpBaseCoordinateCLM (U p))‖ ^ 2 := by
  simpa only [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2] using
    vectorTransportCLM_energy_le A hA (fun p ↦ U p)

/-- Continuous W¹,∞ coefficient paths have a single pivot energy constant
on the closed time slab, chosen independently of the state and forcing. -/
theorem exists_vectorTransportCLM_uniform_pivot_energy_bound
    {a b : ℝ} (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn A (Icc a b))
    (hsym : ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b,
      ∀ U : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)),
      2 * ⟪WithLp.toLp 2 (vectorTransportCLM
        (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q)) (fun p ↦ U p)),
        WithLp.toLp 2 (fun p ↦ wkpBaseCoordinateCLM (U p))⟫_ℝ ≤
        K * ‖WithLp.toLp 2 (fun p ↦ wkpBaseCoordinateCLM (U p))‖ ^ 2 := by
  obtain ⟨K, _M, hK, _hM, hderiv, _hop⟩ :=
    PDE.Parabolic.Systems.exists_transport_energy_coefficient_bounds A hA
  refine ⟨K, hK, ?_⟩
  intro t ht U
  have hsum : (∑ j, ∑ p, ∑ q,
      ‖wkpCoordinateCLM (singleDerivIndex n j) (A t j p q)‖) ≤
      transportDerivativeSum (A t) := by
    apply le_add_of_nonneg_right
    positivity
  exact (vectorTransportCLM_pivot_energy_le (A t) (hsym t ht) U).trans
    (mul_le_mul_of_nonneg_right (hsum.trans (hderiv t ht)) (sq_nonneg _))

end SobolevSpace.GraphSpace
