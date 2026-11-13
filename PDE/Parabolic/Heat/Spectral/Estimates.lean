/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.SeparationOfVariables
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Summable bounds for interval heat modes

At a fixed positive time, the exponential Dirichlet multiplier absorbs every power
of the frequency. The bounds are uniform in space and on every time strip `t ≥ τ > 0`.
They supply the convergence estimates for the separated heat series of Evans §4.1.1.
-/

@[expose] public section

namespace HeatEquation

open PDE.Representations

/-- A summable bound for a spatial derivative of order `k` on a positive-time strip. -/
noncomputable def intervalHeatMajorant (k : ℕ) (τ : ℝ) (n : ℕ) : ℝ :=
  ((n.succ : ℝ) * Real.pi) ^ k * intervalHeatTimeMode n τ

/-- The interval eigenvalue dominates the positive mode number. -/
theorem nat_succ_le_intervalDirichletEigenvalue (n : ℕ) :
    (n.succ : ℝ) ≤ intervalDirichletEigenvalue n := by
  have hn : 1 ≤ (n.succ : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hπ : 1 ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hf : (n.succ : ℝ) ≤ (n.succ : ℝ) * Real.pi := by nlinarith
  unfold intervalDirichletEigenvalue
  nlinarith

/-- Every interval Dirichlet eigenvalue is nonnegative. -/
theorem intervalDirichletEigenvalue_nonneg (n : ℕ) :
    0 ≤ intervalDirichletEigenvalue n :=
  sq_nonneg _

/-- The heat multiplier is positive, including at time zero. -/
theorem intervalHeatTimeMode_pos (n : ℕ) (t : ℝ) :
    0 < intervalHeatTimeMode n t :=
  Real.exp_pos _

/-- The heat multiplier decreases with time. -/
theorem intervalHeatTimeMode_antitone (n : ℕ) : Antitone (intervalHeatTimeMode n) := by
  intro s t hst
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left hst (neg_nonpos.mpr (intervalDirichletEigenvalue_nonneg n)))

/-- Nonnegative time multipliers are contractions. -/
theorem intervalHeatTimeMode_le_one (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    intervalHeatTimeMode n t ≤ 1 := by
  simpa [intervalHeatTimeMode] using intervalHeatTimeMode_antitone n ht

/-- The derivative majorants are nonnegative. -/
theorem intervalHeatMajorant_nonneg (k : ℕ) (τ : ℝ) (n : ℕ) :
    0 ≤ intervalHeatMajorant k τ n := by
  unfold intervalHeatMajorant
  exact mul_nonneg (pow_nonneg (by positivity) _) (intervalHeatTimeMode_pos n τ).le

/-- Exponential damping makes every polynomial frequency weight summable. -/
theorem summable_intervalHeatMajorant (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (intervalHeatMajorant k τ) := by
  have hsum : Summable (fun n : ℕ ↦
      Real.pi ^ k * ((n.succ : ℝ) ^ k * Real.exp (-τ * (n.succ : ℝ)))) :=
    ((summable_nat_add_iff 1).mpr
      (Real.summable_pow_mul_exp_neg_nat_mul k hτ)).mul_left _
  apply hsum.of_nonneg_of_le (intervalHeatMajorant_nonneg k τ)
  intro n
  unfold intervalHeatMajorant intervalHeatTimeMode
  calc
    ((n.succ : ℝ) * Real.pi) ^ k *
        Real.exp (-intervalDirichletEigenvalue n * τ) ≤
      ((n.succ : ℝ) * Real.pi) ^ k * Real.exp (-τ * (n.succ : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        have := nat_succ_le_intervalDirichletEigenvalue n
        nlinarith
    _ = Real.pi ^ k * ((n.succ : ℝ) ^ k * Real.exp (-τ * (n.succ : ℝ))) := by
      rw [mul_pow]
      ring

/-- A sine mode has absolute value at most one. -/
theorem norm_intervalDirichletSineMode_le (n : ℕ) (x : ℝ) :
    ‖intervalDirichletSineMode n x‖ ≤ 1 :=
  Real.abs_sin_le_one _

/-- A sine mode's first derivative is bounded by its frequency. -/
theorem norm_deriv_intervalDirichletSineMode_le (n : ℕ) (x : ℝ) :
    ‖deriv (intervalDirichletSineMode n) x‖ ≤ (n.succ : ℝ) * Real.pi := by
  rw [intervalDirichletSineMode_deriv, norm_mul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (n.succ : ℝ) * Real.pi)]
  exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)

/-- The separated mode is bounded uniformly in space on a time strip. -/
theorem norm_intervalHeatMode_le (n : ℕ) {τ t : ℝ} (ht : τ ≤ t) (x : ℝ) :
    ‖intervalHeatMode n t x‖ ≤ intervalHeatMajorant 0 τ n := by
  rw [intervalHeatMode, norm_mul, Real.norm_of_nonneg (intervalHeatTimeMode_pos n t).le]
  calc
    ‖intervalDirichletSineMode n x‖ * intervalHeatTimeMode n t ≤
        intervalHeatTimeMode n t :=
      mul_le_of_le_one_left (intervalHeatTimeMode_pos n t).le
        (norm_intervalDirichletSineMode_le n x)
    _ ≤ intervalHeatMajorant 0 τ n := by
      simpa [intervalHeatMajorant] using intervalHeatTimeMode_antitone n ht

end HeatEquation
