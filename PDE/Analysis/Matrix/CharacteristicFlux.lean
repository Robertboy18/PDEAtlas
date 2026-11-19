/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Quadratic energy and characteristic flux

Completing the square in a positive semidefinite matrix bounds the bilinear
flux in a unit characteristic direction by kinetic plus quadratic energy.
-/

@[expose] public section

namespace Matrix.PosSemidef

open scoped Matrix

/-- A direction of unit quadratic length has flux bounded by the associated energy. -/
theorem mul_dotProduct_mulVec_le_half {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (v z : ι → ℝ) (w : ℝ)
    (hz : z ⬝ᵥ (A *ᵥ z) = 1) :
    w * (v ⬝ᵥ (A *ᵥ z)) ≤ (1 / 2 : ℝ) * (w ^ 2 + v ⬝ᵥ (A *ᵥ v)) := by
  have hc : z ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ z) := by
    simpa only [star_trivial] using hA.isHermitian.star_dotProduct_mulVec_comm z v
  have h := hA.dotProduct_mulVec_nonneg (v - w • z)
  simp only [star_trivial, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
  rw [hz, hc] at h
  nlinarith

end Matrix.PosSemidef
