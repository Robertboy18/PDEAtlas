/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Center projection for a finite real diagonal operator

The zero-rate coordinates form the center space. Their canonical coordinate
projection has norm at most one in the supremum norm, including an empty index
type or an empty fast complement.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Evolution

variable {ι : Type*}

/-- Retain precisely the zero-rate coordinates of a diagonal equation. -/
def diagonalCenterProjection (rate : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ if rate i = 0 then ContinuousLinearMap.proj i else 0

/-- The center projection is the usual coordinate restriction extended by zero. -/
@[simp] theorem diagonalCenterProjection_apply (rate : ι → ℝ) (x : ι → ℝ) (i : ι) :
    diagonalCenterProjection rate x i = if rate i = 0 then x i else 0 := by
  by_cases hi : rate i = 0 <;> simp [diagonalCenterProjection, hi]

/-- Every projected vector lies in the kernel of the diagonal operator. -/
theorem rate_mul_diagonalCenterProjection (rate : ι → ℝ) (x : ι → ℝ) (i : ι) :
    rate i * diagonalCenterProjection rate x i = 0 := by
  by_cases hi : rate i = 0 <;> simp [hi]

/-- A vector in the diagonal kernel is unchanged by the center projection. -/
theorem diagonalCenterProjection_eq_self (rate : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, rate i * x i = 0) :
    diagonalCenterProjection rate x = x := by
  ext i
  by_cases hi : rate i = 0
  · simp [hi]
  · have hxi : x i = 0 := (mul_eq_zero.mp (hx i)).resolve_left hi
    simp [hi, hxi]

variable [Fintype ι]

/-- The canonical center projection is nonexpansive in the finite product norm. -/
theorem norm_diagonalCenterProjection_le (rate : ι → ℝ) :
    ‖diagonalCenterProjection rate‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  by_cases hi : rate i = 0
  · simpa only [diagonalCenterProjection_apply, ite_eq_left hi] using norm_le_pi_norm x i
  · simp only [diagonalCenterProjection_apply, ite_eq_right hi, norm_zero, norm_nonneg]

end PDE.Analysis.Evolution
