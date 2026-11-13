/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Pointwise

/-!
# The vector of coordinate difference quotients

The simultaneous coordinate quotients take values in Euclidean space. In particular,
their Lp norm uses the same pointwise Euclidean norm as the weak gradient.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

variable {n : ℕ}

/-- The vector whose coordinates are the forward coordinate difference quotients. -/
def vectorDifference (h : ℝ) (u : ℝ^n → ℝ) (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 (fun i ↦ forwardDifference i h u x)

/-- A coordinate of the vector difference quotient is the scalar difference quotient. -/
@[simp] theorem vectorDifference_apply (h : ℝ) (u : ℝ^n → ℝ) (x : ℝ^n) (i : Fin n) :
    vectorDifference h u x i = forwardDifference i h u x := rfl

end SobolevSpace.GraphSpace.DifferenceQuotient
