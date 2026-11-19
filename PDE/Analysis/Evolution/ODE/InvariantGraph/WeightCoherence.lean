/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Characterization

/-!
# Agreement of the construction across exponential weights

Increasing the weight commutes with composition, constant center seeds, and the
diagonal Green operator. The last assertion follows from uniqueness for the
weighted linear differential equation, including its center values at
zero. Consequently the contractions at different admissible weights construct
one and the same whole-line path.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {L : ℝ≥0} {N : E → E} {η θ : ℝ}

/-- Composition represents the same nonlinear forcing after a weight change. -/
theorem increaseExponentialWeight_composeExponentialWeight (hηθ : η ≤ θ)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (u : ℝ →ᵇ E) :
    increaseExponentialWeight hηθ (composeExponentialWeight hN hN0 η u) =
      composeExponentialWeight hN hN0 θ (increaseExponentialWeight hηθ u) := by
  apply exponentialLift_injective θ
  ext t
  simp only [exponentialLift_increaseExponentialWeight, exponentialLift_composeExponentialWeight]

end BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {η θ : ℝ}

/-- The constant center path is independent of the weight used to encode it. -/
theorem increaseExponentialWeight_centerSeed (hη : 0 ≤ η) (hηθ : η ≤ θ) (ξ : E) :
    increaseExponentialWeight hηθ (centerSeed hη ξ) = centerSeed (hη.trans hηθ) ξ := by
  apply exponentialLift_injective θ
  ext t
  simp only [exponentialLift_increaseExponentialWeight, exponentialLift_centerSeed]

variable {ι : Type*} [Fintype ι]

/-- The Green solution commutes with an admissible increase in weight. -/
theorem increaseExponentialWeight_diagonalGreen (hη : 0 < η) (hηθ : η ≤ θ)
    (rate : ι → ℝ) (hgapη : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hgapθ : ∀ i, rate i ≠ 0 → θ < |rate i|) (f : ℝ →ᵇ (ι → ℝ)) :
    increaseExponentialWeight hηθ (diagonalGreen hη rate hgapη f) =
      diagonalGreen (hη.trans_le hηθ) rate hgapθ (increaseExponentialWeight hηθ f) := by
  apply eq_of_weighted_diagonal_hasDerivAt rate hgapθ _ _ (exponentialLift η f)
  · intro t
    simpa only [exponentialLift_increaseExponentialWeight] using
      hasDerivAt_exponentialLift_diagonalGreen hη rate hgapη f t
  · intro t
    simpa only [exponentialLift_increaseExponentialWeight] using
      hasDerivAt_exponentialLift_diagonalGreen (hη.trans_le hηθ) rate hgapθ
        (increaseExponentialWeight hηθ f) t
  · intro i hi
    have hzero := congrArg (fun g : C(ℝ, ι → ℝ) ↦ g 0 i)
      (exponentialLift_increaseExponentialWeight hηθ (diagonalGreen hη rate hgapη f))
    simpa only [exponentialLift_zero,
      diagonalGreen_zero_apply_of_rate_eq_zero hη rate hgapη f i hi,
      diagonalGreen_zero_apply_of_rate_eq_zero (hη.trans_le hηθ) rate hgapθ
        (increaseExponentialWeight hηθ f) i hi] using hzero

variable {L : ℝ≥0} {N : (ι → ℝ) → (ι → ℝ)}

/-- Independently contracting constructions at two weights give the same
path. Each contraction bound is an explicit hypothesis. -/
theorem increaseExponentialWeight_perronPath (hη : 0 < η) (hηθ : η ≤ θ)
    (rate : ι → ℝ) (hgapη : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hgapθ : ∀ i, rate i ≠ 0 → θ < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmallη : ‖diagonalGreen hη rate hgapη‖ * L < 1)
    (hsmallθ : ‖diagonalGreen (hη.trans_le hηθ) rate hgapθ‖ * L < 1) (ξ : ι → ℝ) :
    increaseExponentialWeight hηθ
        (perronPath η (diagonalGreen hη rate hgapη) hN hN0 hsmallη (centerSeed hη.le ξ)) =
      perronPath θ (diagonalGreen (hη.trans_le hηθ) rate hgapθ) hN hN0 hsmallθ
        (centerSeed (hη.le.trans hηθ) ξ) := by
  apply perronPath_unique
  conv_lhs => rw [perronPath_eq]
  rw [map_add, increaseExponentialWeight_centerSeed,
    increaseExponentialWeight_diagonalGreen,
    increaseExponentialWeight_composeExponentialWeight]

end PDE.Analysis.Evolution
