/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Superlinear.Existence
import CAS.IntegrationTactic

/-!
# A nonzero cubic Dirichlet solution on the unit ball

The reaction `f(s) = s³` with primitive `F(s) = s⁴/4` satisfies the hypotheses
`Hypotheses` of the superlinear existence theorem `exists_nonzero_weak_solution`. It
gives a nonzero weak solution of `-Δu = u³` with zero boundary values on the
three-dimensional unit ball (`exists_nonzero_cubic_unitBall_three`), and also in
dimensions one and two (`exists_nonzero_cubic_unitBall_lowDimension`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace
open PDE.Elliptic.Semilinear.Superlinear
open scoped Sobolev
open PDE.Analysis (primitive)

namespace PDE.Examples.Elliptic.Semilinear

/-- The derivative of `s³` is `3s²`. -/
theorem deriv_cubic (z : ℝ) : deriv (fun s : ℝ ↦ s ^ 3) z = 3 * z ^ 2 := by
  cas

/-- The primitive of `s³` from `0` to `z` is `z⁴/4`, for every real `z`. -/
theorem primitive_cubic (z : ℝ) :
    primitive (fun s : ℝ ↦ s ^ 3) z = z ^ 4 / 4 := by
  unfold primitive
  cas

/-- The cubic reaction satisfies all scalar hypotheses of the existence theorem. -/
theorem cubic_hypotheses :
    Hypotheses (fun s : ℝ ↦ s ^ 3) 3 3 (1 / 4) (1 / 4) (1 / 4) := by
  have habs (z : ℝ) : |z| ^ 4 = z ^ 4 := (by decide : Even 4).pow_abs z
  refine {
    contDiff := contDiff_id.pow 3
    one_lt := by norm_num
    reaction_bound := ?_
    deriv_bound := ?_
    primitive_nonneg := ?_
    primitive_le := ?_
    gamma_lt_half := by norm_num
    lower_pos := by norm_num
    lower_le_upper := le_rfl
    primitive_lower := ?_
    primitive_upper := ?_
  }
  · intro z
    have heq : |z ^ 3| = |z| ^ (3 : ℝ) := by norm_num [Real.rpow_natCast, abs_pow]
    rw [heq]
    have hp : 0 ≤ |z| ^ (3 : ℝ) := by positivity
    linarith
  · intro z
    norm_num [deriv_cubic, Real.rpow_natCast, abs_mul, abs_pow]
  · intro z
    rw [primitive_cubic]
    positivity
  · intro z
    rw [primitive_cubic]
    exact le_of_eq (by cas)
  · intro z
    norm_num [primitive_cubic, Real.rpow_natCast, abs_div, abs_pow, habs]
    exact le_of_eq (by cas)
  · intro z
    norm_num [primitive_cubic, Real.rpow_natCast, abs_div, abs_pow, habs]
    exact le_of_eq (by cas)

/-- A nonzero solution of `-Δu = u³` on the three-dimensional unit ball,
satisfying the weak equation against every zero-boundary test function. -/
theorem exists_nonzero_cubic_unitBall_three :
    ∃ u : H¹₀(ball (0 : ℝ^3) 1), u ≠ 0 ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ -(z ^ 3)) 0 u := by
  exact cubic_hypotheses.exists_nonzero_weak_solution (by norm_num)
    isOpen_ball isBounded_ball (nonempty_ball.mpr (by norm_num)) (by norm_num)

/-- The cubic equation also has a nonzero weak solution on the unit ball in dimensions
one and two. -/
theorem exists_nonzero_cubic_unitBall_lowDimension
    {n : ℕ} (hn : 0 < n) (hn2 : n ≤ 2) :
    ∃ u : H¹₀(ball (0 : ℝ^n) 1), u ≠ 0 ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ -(z ^ 3)) 0 u :=
  cubic_hypotheses.exists_nonzero_weak_solution_lowDimension hn hn2
    isOpen_ball isBounded_ball (nonempty_ball.mpr (by norm_num))

end PDE.Examples.Elliptic.Semilinear
