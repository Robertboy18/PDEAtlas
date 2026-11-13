/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SymmetricSystem
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Matrix coefficients for the first-order system

Mathlib's Euclidean matrix operator turns coefficient matrices into operators
for the first-order system. Symmetric real matrices give precisely the
operator symmetry used by that system, and the operator coordinates expose
the full matrix contraction.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem

open PDE.Common

variable {n m : ℕ}

/-- A system specified by its matrices, using Mathlib's Euclidean matrix
operator and the first-order system type. -/
def ofMatrices (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (f : SpaceTime n → ℝ^m) (Ω : Set (SpaceTime n)) :
    LinearFirstOrderSystem n m where
  coefficient j y := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) (B j y)
  forcing := f
  domain := Ω

/-- Symmetry of the real matrices is exactly symmetry of the
system's coefficient operators on its domain. -/
theorem ofMatrices_isSymmetric_iff (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (f : SpaceTime n → ℝ^m) (Ω : Set (SpaceTime n)) :
    (ofMatrices B f Ω).IsSymmetric ↔ ∀ y ∈ Ω, ∀ j, (B j y).IsSymm := by
  simp only [IsSymmetric, IsSymmetricAt, ofMatrices, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.isSymmetric_toEuclideanLin_iff, Matrix.isHermitian_iff_isSymm]

/-- The operator acts by the full matrix contraction in every
component; no diagonal or decoupling assumption is introduced. -/
theorem ofMatrices_operator_apply (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (f : SpaceTime n → ℝ^m) (Ω : Set (SpaceTime n)) (u : SpaceTime n → ℝ^m) (y : SpaceTime n)
    (p : Fin m) :
    (ofMatrices B f Ω).operator u y p = (∂[0] u) y p + ∑ j, ∑ q, B j y p q * (∂[j.succ] u) y q := by
  simp only [operator, ofMatrices, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]

end PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem
