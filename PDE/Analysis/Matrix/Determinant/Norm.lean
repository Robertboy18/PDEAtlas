/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.Determinant.Derivative

/-!
# A homogeneous norm bound for the determinant

The operator norm of the alternating determinant depends only on the dimension.
It bounds the determinant by the corresponding power of the entrywise matrix norm.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise

namespace PDE.Analysis.Matrix

/-- A dimension-only constant controlling the determinant in the entrywise norm. -/
def detNormBound (n : ℕ) : ℝ :=
  ‖(detContinuousAlternating (ι := Fin n)).toContinuousMultilinearMap‖

/-- The determinant bound is nonnegative. -/
theorem detNormBound_nonneg (n : ℕ) : 0 ≤ detNormBound n :=
  norm_nonneg _

/-- The determinant has homogeneous growth of degree equal to the dimension. -/
theorem norm_det_le (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) :
    ‖P.det‖ ≤ detNormBound n * ‖P‖ ^ n :=
  detContinuousAlternating.toContinuousMultilinearMap.le_opNorm_mul_pow_of_le le_rfl

end PDE.Analysis.Matrix
