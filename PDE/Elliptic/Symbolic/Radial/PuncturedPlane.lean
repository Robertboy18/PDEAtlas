/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
import Mathlib.Tactic.Positivity.Finset

/-!
# Elementary geometry of the punctured plane

The logarithmic and rational harmonic examples share the same domain and the
same nonvanishing fact for `x² + y²`. Keeping those facts here avoids a false
dependency between the two examples.
-/

@[expose] public section

namespace LaplacianEquation.Symbolic

noncomputable section

/-- The plane with the origin removed. -/
def puncturedPlane2D : Set (ℝ^2) :=
  {p | p ≠ 0}

/-- The squared coordinate radius is positive away from the origin. -/
theorem sum_sq_pos_of_ne_zero (p : ℝ^2) (hp : p ≠ 0) :
    0 < (p 0) ^ 2 + (p 1) ^ 2 := by
  have hnorm : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p
  have hnorm_pos : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hnorm_sq_pos : 0 < ‖p‖ ^ 2 := sq_pos_of_pos hnorm_pos
  simpa [hnorm.symm] using hnorm_sq_pos

/-- The squared coordinate radius is nonzero on the punctured plane. -/
theorem sum_sq_ne_zero_of_ne_zero (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    (p 0) ^ 2 + (p 1) ^ 2 ≠ 0 :=
  (sum_sq_pos_of_ne_zero p hp).ne'

/-- The fourth power of the coordinate radius is nonzero away from the origin. -/
theorem sum_sq_sq_ne_zero_of_ne_zero (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    ((p 0) ^ 2 + (p 1) ^ 2) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (sum_sq_ne_zero_of_ne_zero p hp)

end


end LaplacianEquation.Symbolic
