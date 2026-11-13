/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.IntegrableForcing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherForcing

/-!
# Higher Sobolev Duhamel trajectories with integrable forcing

The higher propagator is uniformly bounded because it is conjugate to the
energy contraction. Integrable higher forcing therefore gives a continuous
higher trajectory, and the energy inclusion commutes with its
retarded integral.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution Hyperbolic.Variational

variable (n k : ℕ)

/-- Conjugating the energy contraction gives a uniform bound at each higher
Sobolev order, in the ordinary product norm. -/
theorem norm_higherLinearSemigroup_le (t : NNReal) :
    ‖higherLinearSemigroup n k t‖ ≤ ‖(higherEnergyEquiv n k).symm.toContinuousLinearMap‖ *
      ‖(higherEnergyEquiv n k).toContinuousLinearMap‖ := by
  let A := (higherEnergyEquiv n k).symm.toContinuousLinearMap
  let B := (higherEnergyEquiv n k).toContinuousLinearMap
  have hS := waveContractionSemigroup_isContraction (energyTriple n) (massForm n)
    (massForm_coercive n) massForm_symmetric
  apply (higherLinearSemigroup n k t).opNorm_le_bound (mul_nonneg (norm_nonneg A) (norm_nonneg B))
  intro x
  change ‖A (linearSemigroup n t (B x))‖ ≤ ‖A‖ * ‖B‖ * ‖x‖
  calc
    _ ≤ ‖A‖ * ‖linearSemigroup n t (B x)‖ := A.le_opNorm _
    _ ≤ ‖A‖ * ‖B x‖ := mul_le_mul_of_nonneg_left (hS.norm_apply_le t (B x)) (norm_nonneg A)
    _ ≤ ‖A‖ * (‖B‖ * ‖x‖) := mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg A)
    _ = ‖A‖ * ‖B‖ * ‖x‖ := (mul_assoc _ _ _).symm

/-- Forgetting higher derivatives commutes with Duhamel integration of an
interval-integrable force. -/
theorem higherEnergyInclusionCLM_duhamel_of_intervalIntegrable
    {F : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {t : ℝ} (hF : IntervalIntegrable F volume 0 t) :
    higherEnergyInclusionCLM n k ((higherLinearSemigroup n k).duhamel F t) =
      (linearSemigroup n).duhamel (fun s ↦ higherEnergyInclusionCLM n k (F s)) t := by
  unfold StronglyContinuousSemigroup.duhamel
  rw [← (higherEnergyInclusionCLM n k).intervalIntegral_comp_comm
    (intervalIntegrable_duhamelIntegrand (higherLinearSemigroup n k)
      (norm_higherLinearSemigroup_le n k) hF t)]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  exact higherEnergyInclusionCLM_higherLinearSemigroup n k (t - s).toNNReal (F s)

/-- The higher forced trajectory projects to the energy forced trajectory for
locally integrable higher forcing. -/
theorem higherEnergyInclusionCLM_forced_of_locallyIntegrable (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {F : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} (hF : LocallyIntegrable F volume) (t : ℝ) :
    higherEnergyInclusionCLM n k
        ((higherLinearSemigroup n k).realOrbit x t +
          (higherLinearSemigroup n k).duhamel F t) =
      (linearSemigroup n).realOrbit (higherEnergyInclusionCLM n k x) t +
        (linearSemigroup n).duhamel
          (fun s ↦ higherEnergyInclusionCLM n k (F s)) t := by
  have hi : IntervalIntegrable F volume 0 t := intervalIntegrable_iff.mpr
      ((hF.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self)
  rw [map_add, higherEnergyInclusionCLM_duhamel_of_intervalIntegrable n k hi,
    StronglyContinuousSemigroup.realOrbit, higherEnergyInclusionCLM_higherLinearSemigroup]
  rfl

/-- Locally integrable higher forcing constructs a continuous higher Sobolev
trajectory, with its energy projection and original trace identified. -/
theorem exists_continuous_higherOrder_forced_of_locallyIntegrable
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) {F : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)}
    (hF : LocallyIntegrable F volume) :
    ∃ u : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)), u 0 = x ∧
      ∀ t : ℝ, higherEnergyInclusionCLM n k (u t) =
        (linearSemigroup n).realOrbit (higherEnergyInclusionCLM n k x) t +
          (linearSemigroup n).duhamel
            (fun s ↦ higherEnergyInclusionCLM n k (F s)) t := by
  refine ⟨⟨_, ((higherLinearSemigroup n k).continuous_realOrbit x).add
    (continuous_duhamel_of_locallyIntegrable (higherLinearSemigroup n k)
      (norm_higherLinearSemigroup_le n k) hF)⟩, ?_, ?_⟩
  · simp only [ContinuousMap.coe_mk, Pi.add_apply, StronglyContinuousSemigroup.realOrbit_zero,
      StronglyContinuousSemigroup.duhamel_zero, add_zero]
  · exact higherEnergyInclusionCLM_forced_of_locallyIntegrable n k x hF

end PDE.Hyperbolic.NonlinearWave.Cauchy
