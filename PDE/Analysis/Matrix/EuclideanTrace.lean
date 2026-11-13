/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.Euclidean

/-!
# The trace of a flattened matrix

`euclideanTraceCLM` is the trace of a square matrix in the row-major Euclidean coordinates of
`Matrix.euclideanEquiv`: the sum of the entries at `finProdFinEquiv (i, i)`. Applied to the
flattened weak gradient of a vector field it is the weak divergence.
-/

@[expose] public noncomputable section

namespace Matrix

variable {m : ℕ}

/-- The trace of a square matrix in row-major Euclidean coordinates. -/
def euclideanTraceCLM : ℝ^(m * m) →L[ℝ] ℝ :=
  ∑ i : Fin m, EuclideanSpace.proj (finProdFinEquiv (i, i))

/-- The trace is the sum of the diagonal coordinates. -/
theorem euclideanTraceCLM_apply (v : ℝ^(m * m)) :
    euclideanTraceCLM v = ∑ i, v (finProdFinEquiv (i, i)) := by
  simp [euclideanTraceCLM]

/-- In the coordinates of `euclideanEquiv` it is the matrix trace. -/
theorem euclideanTraceCLM_euclideanEquiv (A : Matrix (Fin m) (Fin m) ℝ) :
    euclideanTraceCLM (euclideanEquiv A) = A.trace := by
  rw [euclideanTraceCLM_apply, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← euclideanEquiv_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

end Matrix
