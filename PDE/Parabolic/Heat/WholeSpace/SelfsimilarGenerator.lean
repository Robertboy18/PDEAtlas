/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarResolventVector
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# The free self-similar resolvent on vector fields as a generator resolvent

At similarity time `τ` the free self-similar evolution of vector `L²` fields has operator norm
at most `e^{(2-n)τ/4}`, with constant one (`norm_vectorSelfsimilarHeatSemigroup_le`). This is
`e^{-τ/4}` in dimension three, and from dimension two on the evolution is a contraction. Its
Laplace transform at `μ > 0` is the componentwise resolvent `vectorSelfsimilarResolvent`, so
that resolvent maps into the domain of the generator `A₀ = -L₀` of the vector evolution and
satisfies `A₀ R_μ f = μ R_μ f - f`. The second-order realization of the resolvent lowers to
it. Conversely every `x` in the domain of the generator is `R₁ (x - A₀ x)`, so the domain lies
in `H²` (`vectorLower_vectorSelfsimilarResolventH2_of_hasGeneratorAt`).
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Set
open scoped NNReal Sobolev

namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- **The vector free self-similar evolution on `L²` decays like `e^{(2-n)τ/4}`, with constant
one**: `‖vectorSelfsimilarHeatSemigroup n 0 τ‖ ≤ e^{(2-n)τ/4}` in every dimension `n`, which is
`e^{-τ/4}` in dimension three. Each component obeys
`norm_baseL2_selfsimilarHeatSobolev_le_exp`. -/
theorem norm_vectorSelfsimilarHeatSemigroup_le (τ : ℝ≥0) :
    ‖vectorSelfsimilarHeatSemigroup n 0 τ‖ ≤ Real.exp (((2 : ℝ) - n) * τ / 4) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun u ↦ ?_
  rw [vectorSelfsimilarHeatSemigroup_apply]
  apply PiLp.norm_le_mul_of_norm_apply_le _ u (Real.exp_pos _).le
  intro j
  rw [vectorSelfsimilarHeat_apply, norm_eq_norm_baseL2_of_order_zero,
    norm_eq_norm_baseL2_of_order_zero]
  exact norm_baseL2_selfsimilarHeatSobolev_le_exp τ (u j)

/-- From dimension two on, the vector free self-similar evolution on `L²` is a contraction
semigroup: `e^{(2-n)τ/4} ≤ 1` in `norm_vectorSelfsimilarHeatSemigroup_le`. -/
theorem isContraction_vectorSelfsimilarHeatSemigroup (hn : 2 ≤ n) :
    (vectorSelfsimilarHeatSemigroup n 0).IsContraction := by
  intro τ
  refine (norm_vectorSelfsimilarHeatSemigroup_le τ).trans (Real.exp_le_one_iff.mpr ?_)
  have : (2 : ℝ) - n ≤ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hτ : (0 : ℝ) ≤ τ := τ.property
  nlinarith

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

/-- **The domain of the generator lies in `H²`.** If `x` is in the domain of the generator of
the free self-similar evolution on vector `L²(ℝⁿ)`, `n ≥ 2`, with value `y`, then `x` is the
`H²` field `R₁ (x - y)` with its two derivatives forgotten. Here `R₁` is the second-order
realization of the resolvent at `μ = 1`, and the identity is the Laplace transform identity of
the generator at `μ = 1`. -/
theorem vectorLower_vectorSelfsimilarResolventH2_of_hasGeneratorAt (hn : 2 ≤ n)
    {x y : VectorH n 0} (h : (vectorSelfsimilarHeatSemigroup n 0).HasGeneratorAt x y) :
    vectorLower n 0 (vectorLower n 1 (vectorSelfsimilarResolventH2 n hn
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (x - y))) = x := by
  have hy : (vectorSelfsimilarHeatSemigroup n 0).generatorPMap ⟨x, ⟨y, h⟩⟩ = y :=
    StronglyContinuousSemigroup.HasGeneratorAt.unique
      ((vectorSelfsimilarHeatSemigroup n 0).hasGeneratorAt_generatorPMap ⟨x, ⟨y, h⟩⟩) h
  have hid := (vectorSelfsimilarHeatSemigroup n 0).laplaceTransform_generator_identity
    (isContraction_vectorSelfsimilarHeatSemigroup hn) one_pos ⟨x, ⟨y, h⟩⟩
  rw [hy, one_smul] at hid
  rw [vectorLower_vectorLower_vectorSelfsimilarResolventH2,
    vectorSelfsimilarResolvent_eq_laplaceTransform hn one_pos]
  exact hid

end HeatEquation.WholeSpace
