/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Ball volumes in even and odd dimensions

Mathlib's integer and half-integer Gamma evaluations give the factorial and
double-factorial forms of Mathlib's ball volume. The formulas include the
zero-dimensional volume and the length of the one-dimensional unit ball.
-/

@[expose] public noncomputable section

open scoped Nat

namespace PDE.Analysis

/-- Unit-ball volume in even dimension, including dimension zero. -/
theorem unitBallVolume_two_mul (k : ℕ) :
    unitBallVolume (2 * k) = Real.pi ^ k / k ! := by
  have harg : ((2 * k : ℕ) : ℝ) / 2 + 1 = (k : ℝ) + 1 := by
    push_cast
    ring
  rw [unitBallVolume, pow_mul, Real.sq_sqrt Real.pi_nonneg, harg,
    Real.Gamma_nat_eq_factorial]

/-- Unit-ball volume in odd dimension, in double-factorial form. -/
theorem unitBallVolume_two_mul_add_one (k : ℕ) :
    unitBallVolume (2 * k + 1) = Real.pi ^ k * 2 ^ (k + 1) / (2 * k + 1)‼ := by
  have harg : ((2 * k + 1 : ℕ) : ℝ) / 2 + 1 = (k : ℝ) + 1 + 1 / 2 := by
    push_cast
    ring
  rw [unitBallVolume, harg, Real.Gamma_nat_add_one_add_half,
    pow_succ, pow_mul, Real.sq_sqrt Real.pi_nonneg]
  have hs : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp

end PDE.Analysis
