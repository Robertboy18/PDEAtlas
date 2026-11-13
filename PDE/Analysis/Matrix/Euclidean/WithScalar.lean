/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.Euclidean
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# A matrix and a scalar in joint Euclidean coordinates

The scalar occupies coordinate zero, followed by the row-major matrix
coordinates. This is a continuous linear equivalence, so joint convexity and
Fréchet differentiability transport to a Euclidean Hilbert space.
It also includes empty rectangular matrices.
-/

@[expose] public noncomputable section

namespace Matrix

variable {m n : ℕ}

/-- Joint Euclidean coordinates for a real matrix and one scalar. -/
def euclideanScalarEquiv :
    (Matrix (Fin m) (Fin n) ℝ × ℝ) ≃L[ℝ] ℝ^(m * n + 1) :=
  (ContinuousLinearEquiv.prodComm ℝ (Matrix (Fin m) (Fin n) ℝ) ℝ).trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (euclideanEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ _))).trans
      ((Fin.consLinearEquiv ℝ (fun _ : Fin (m * n + 1) ↦ ℝ)).toContinuousLinearEquiv.trans
        (PiLp.continuousLinearEquiv 2 ℝ _).symm))

/-- Coordinate zero is the independent scalar. -/
@[simp]
theorem euclideanScalarEquiv_apply_zero (A : Matrix (Fin m) (Fin n) ℝ) (r : ℝ) :
    euclideanScalarEquiv (A, r) 0 = r :=
  rfl

/-- The remaining coordinates are exactly the original row-major matrix entries. -/
@[simp]
theorem euclideanScalarEquiv_apply_succ (A : Matrix (Fin m) (Fin n) ℝ) (r : ℝ)
    (i : Fin m) (j : Fin n) :
    euclideanScalarEquiv (A, r) (finProdFinEquiv (i, j)).succ = A i j :=
  congrArg (fun k : Fin m × Fin n ↦ A k.1 k.2)
    (finProdFinEquiv.symm_apply_apply (i, j))

/-- Decoding selects the original matrix entries. -/
@[simp]
theorem euclideanScalarEquiv_symm_fst (v : ℝ^(m * n + 1)) (i : Fin m) (j : Fin n) :
    (euclideanScalarEquiv.symm v).1 i j = v (finProdFinEquiv (i, j)).succ :=
  rfl

/-- Decoding selects the scalar in coordinate zero. -/
@[simp]
theorem euclideanScalarEquiv_symm_snd (v : ℝ^(m * n + 1)) :
    (euclideanScalarEquiv.symm v).2 = v 0 :=
  rfl

end Matrix
