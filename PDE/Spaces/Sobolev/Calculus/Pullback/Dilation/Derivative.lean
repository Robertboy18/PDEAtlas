/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.HigherOrder
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivativeCoordinates

/-!
# Weak partial derivatives of dilated Sobolev functions

For `(δ_a u)(x) = u(a x)` the chain rule gives `∂ᵢ (δ_a u) = a δ_a (∂ᵢ u)`, as an identity of
whole-space Sobolev functions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The chain rule for dilations: `∂ᵢ (δ_a u) = a δ_a (∂ᵢ u)`. -/
theorem partialDerivCLM_dilationWkpCLM (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0) (i : Fin n)
    (u : W^{k + 1,p}(ℝ^n)) :
    partialDerivCLM i (dilationWkpCLM hp a ha u) =
      a • dilationWkpCLM hp a ha (partialDerivCLM i u) := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  rw [wkpBaseCoordinateCLM_partialDerivCLM, map_smul]
  change wkpCoordinateCLM _ (dilationWkpCLM hp a ha u) =
    a • wkpCoordinateCLM (baseIndex n k) (dilationWkpCLM hp a ha (partialDerivCLM i u))
  rw [dilationWkpCLM_coordinate, dilationWkpCLM_coordinate, firstDerivIndex_toList,
    baseIndex_toList, List.length_singleton, List.length_nil, pow_one, pow_zero, one_smul]
  congr 2
  change _ = wkpBaseCoordinateCLM (partialDerivCLM i u)
  rw [wkpBaseCoordinateCLM_partialDerivCLM]

end SobolevSpace.GraphSpace
