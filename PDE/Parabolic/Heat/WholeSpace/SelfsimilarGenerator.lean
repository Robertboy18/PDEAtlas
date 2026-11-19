/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarResolventVector
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# The free self-similar resolvent on vector fields as a generator resolvent

From dimension two on, the free self-similar evolution contracts vector `L²` fields. Its
Laplace transform at `μ > 0` is the componentwise resolvent `vectorSelfsimilarResolvent`, so
that resolvent maps into the domain of the generator `A₀ = -L₀` of the vector evolution and
satisfies `A₀ R_μ f = μ R_μ f - f`. The second-order realization of the resolvent lowers to
it.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Set
open scoped NNReal Sobolev

namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- From dimension two on, the vector free self-similar evolution on `L²` is a contraction
semigroup. -/
theorem isContraction_vectorSelfsimilarHeatSemigroup (hn : 2 ≤ n) :
    (vectorSelfsimilarHeatSemigroup n 0).IsContraction := by
  intro τ
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul, vectorSelfsimilarHeatSemigroup_apply]
  apply PiLp.norm_mono
  intro j
  rw [vectorSelfsimilarHeat_apply]
  have h := (isContraction_selfsimilarHeatSobolevSemigroup hn).norm_apply_le τ (u j)
  rwa [selfsimilarHeatSobolevSemigroup_apply] at h

/-- The componentwise free resolvent is the Laplace transform of the vector free evolution. -/
theorem vectorSelfsimilarResolvent_eq_laplaceTransform (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ) :
    vectorSelfsimilarResolvent n hn hμ =
      (vectorSelfsimilarHeatSemigroup n 0).laplaceTransform
        (isContraction_vectorSelfsimilarHeatSemigroup hn) hμ := by
  ext1 u
  rw [vectorSelfsimilarResolvent_eq_integral, StronglyContinuousSemigroup.laplaceTransform_apply]
  simp only [StronglyContinuousSemigroup.realOrbit, vectorSelfsimilarHeatSemigroup_apply]

/-- The free resolvent of a vector field lies in the generator domain of the free evolution,
with generator value `μ R_μ f - f`. -/
theorem hasGeneratorAt_vectorSelfsimilarResolvent (hn : 2 ≤ n) {μ : ℝ} (hμ : 0 < μ)
    (f : VectorH n 0) :
    (vectorSelfsimilarHeatSemigroup n 0).HasGeneratorAt (vectorSelfsimilarResolvent n hn hμ f)
      (μ • vectorSelfsimilarResolvent n hn hμ f - f) := by
  have h := (vectorSelfsimilarHeatSemigroup n 0).hasGeneratorAt_generatorPMap
    ⟨_, (vectorSelfsimilarHeatSemigroup n 0).laplaceTransform_mem_generatorPMap_domain
      (isContraction_vectorSelfsimilarHeatSemigroup hn) hμ f⟩
  rw [StronglyContinuousSemigroup.generatorPMap_laplaceTransform] at h
  rw [vectorSelfsimilarResolvent_eq_laplaceTransform hn hμ]
  exact h

/-- Forgetting both gained derivatives of the second-order realization of the free resolvent
gives the free resolvent on `L²`. -/
theorem vectorLower_vectorLower_vectorSelfsimilarResolventH2 (hn : 2 ≤ n) {μ : ℝ}
    (hμ : 1 / 2 ≤ μ) (u : VectorH n 0) :
    vectorLower n 0 (vectorLower n 1 (vectorSelfsimilarResolventH2 n hn hμ u)) =
      vectorSelfsimilarResolvent n hn (by linarith : 0 < μ) u := by
  refine PiLp.ext fun j ↦ wkpBaseCoordinateCLM_injective isOpen_univ ?_
  rw [vectorLower_apply, vectorLower_apply, wkpBaseCoordinateCLM_lowerOrderCLM,
    wkpBaseCoordinateCLM_lowerOrderCLM, wkpBaseCoordinateCLM_vectorSelfsimilarResolventH2]

end HeatEquation.WholeSpace
