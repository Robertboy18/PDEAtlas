/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives

/-!
# Coordinates of weak partial derivatives

The weak partial derivative `∂ᵢU ∈ W^{k,p}(Ω)` of `U ∈ W^{k+1,p}(Ω)` is formed from the
derivative coordinates of `U`. Its base coordinate and its base representative are the
first-derivative coordinate of `U` in the direction `i`, and taking a weak partial derivative
commutes with lowering the Sobolev order. These identities hold for every order, exponent and
domain.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open scoped ENNReal Sobolev

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}

/-- Lowering the order commutes with taking a weak partial derivative. -/
theorem lowerOrderCLM_partialDerivCLM {r : ℕ} (hrk : r ≤ k) (i : Fin n)
    (U : W^{k + 1,p}(Ω)) :
    lowerOrderCLM hrk (partialDerivCLM i U) =
      partialDerivCLM i (lowerOrderCLM (Nat.succ_le_succ hrk) U) := by
  rw [partialDerivCLM, partialDerivCLM, lowerOrderCLM_derivativeWordCLM_apply,
    derivativeWordCLM_lowerOrderCLM_apply]

/-- The base coordinate of a weak partial derivative is the corresponding first-derivative
coordinate. -/
theorem wkpBaseCoordinateCLM_partialDerivCLM (i : Fin n) (U : W^{k + 1,p}(Ω)) :
    wkpBaseCoordinateCLM (partialDerivCLM i U) =
      wkpCoordinateCLM (firstDerivIndex n (k + 1) (Nat.succ_pos k) i) U := by
  rw [wkpBaseCoordinateCLM_apply, partialDerivCLM, derivativeWordCLM_apply,
    derivativeWordIndex_baseIndex]
  rfl

/-- The base representative of a weak partial derivative is the corresponding first-derivative
coordinate. -/
theorem baseRepresentative_partialDerivCLM (i : Fin n) (U : W^{k + 1,p}(Ω)) :
    baseRepresentative (partialDerivCLM i U) =
      (((U : WkpAmbientOn n (k + 1) p Ω) (firstDerivIndex n (k + 1) (Nat.succ_pos k) i) :
        DerivLp n p Ω) : ℝ^n → ℝ) :=
  baseRepresentative_derivativeWordCLM [i] _ U

end SobolevSpace.GraphSpace
