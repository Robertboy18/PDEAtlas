/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherLinear

/-!
# Higher Sobolev regularity of the forced whole-space wave

Continuous forcing at a higher Sobolev energy level gives a continuous
trajectory at that level by the constructed semigroup and Duhamel integral.
Forgetting the extra derivatives commutes with both terms. In particular,
this construction upgrades the original energy trajectory whenever its
forcing has been shown to possess the corresponding spatial derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution

variable (n k : ℕ)

/-- Higher Sobolev inclusion commutes with the Duhamel integral. -/
theorem higherEnergyInclusionCLM_duhamel {F : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)}
    (hF : Continuous F) (t : ℝ) :
    higherEnergyInclusionCLM n k ((higherLinearSemigroup n k).duhamel F t) =
      (linearSemigroup n).duhamel (fun s ↦ higherEnergyInclusionCLM n k (F s)) t := by
  unfold StronglyContinuousSemigroup.duhamel
  rw [← (higherEnergyInclusionCLM n k).intervalIntegral_comp_comm
    (((higherLinearSemigroup n k).continuous_duhamelIntegrand hF t).intervalIntegrable 0 t)]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  exact higherEnergyInclusionCLM_higherLinearSemigroup n k (t - s).toNNReal (F s)

/-- The higher forced trajectory projects to the forced energy trajectory. -/
theorem higherEnergyInclusionCLM_forced (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {F : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} (hF : Continuous F) (t : ℝ) :
    higherEnergyInclusionCLM n k
        ((higherLinearSemigroup n k).realOrbit x t +
          (higherLinearSemigroup n k).duhamel F t) =
      (linearSemigroup n).realOrbit (higherEnergyInclusionCLM n k x) t +
        (linearSemigroup n).duhamel
          (fun s ↦ higherEnergyInclusionCLM n k (F s)) t := by
  rw [map_add, higherEnergyInclusionCLM_duhamel n k hF, StronglyContinuousSemigroup.realOrbit,
    higherEnergyInclusionCLM_higherLinearSemigroup]
  rfl

/-- Continuous higher-order data and forcing construct a continuous higher
Sobolev trajectory with the same initial value and energy evolution. -/
theorem exists_continuous_higherOrder_forced (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {F : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} (hF : Continuous F) :
    ∃ u : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)), u 0 = x ∧
      ∀ t : ℝ, higherEnergyInclusionCLM n k (u t) =
        (linearSemigroup n).realOrbit (higherEnergyInclusionCLM n k x) t +
          (linearSemigroup n).duhamel
            (fun s ↦ higherEnergyInclusionCLM n k (F s)) t := by
  refine ⟨⟨_, ((higherLinearSemigroup n k).continuous_realOrbit x).add
    ((higherLinearSemigroup n k).continuous_duhamel hF)⟩, ?_, ?_⟩
  · simp only [ContinuousMap.coe_mk, Pi.add_apply, StronglyContinuousSemigroup.realOrbit_zero,
      StronglyContinuousSemigroup.duhamel_zero, add_zero]
  · exact higherEnergyInclusionCLM_forced n k x hF

end PDE.Hyperbolic.NonlinearWave.Cauchy
