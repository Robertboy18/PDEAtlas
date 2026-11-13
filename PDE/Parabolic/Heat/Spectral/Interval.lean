/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.Estimates
public import Mathlib.Analysis.Calculus.SmoothSeries
import CAS.ExactTactic

/-!
# The convergent Dirichlet heat series on the unit interval

For bounded real coefficients, the separated sine series converges absolutely at positive
time, uniformly in space on each strip `t ≥ τ > 0`. Its time derivative and its first two
space derivatives are obtained by differentiating the series. In particular the sum
satisfies `u_t = u_xx` and vanishes at both endpoints.

This supplies the convergence and differentiation step behind the interval heat
representation in Evans §4.1.1. Bounded coefficients alone do not specify a function-valued
initial trace; the initial-data theorem is in `Spectral.Initial`.
-/

@[expose] public section

namespace HeatEquation

open PDE.Representations Filter
open scoped Topology

/-- The Dirichlet sine series with heat damping. Convergence at positive time is proved
below from boundedness of the coefficients. -/
noncomputable def intervalHeatSeries (a : ℕ → ℝ) (t x : ℝ) : ℝ :=
  ∑' n, a n * intervalHeatMode n t x

/-- The series obtained by differentiating once in space. -/
noncomputable def intervalHeatSeriesDx (a : ℕ → ℝ) (t x : ℝ) : ℝ :=
  ∑' n, a n * (deriv (intervalDirichletSineMode n) x * intervalHeatTimeMode n t)

/-- The common series for the time derivative and the second space derivative. -/
noncomputable def intervalHeatSeriesDt (a : ℕ → ℝ) (t x : ℝ) : ℝ :=
  ∑' n, a n * (-intervalDirichletEigenvalue n * intervalHeatMode n t x)

/-- The spatial derivative of a separated heat mode, as a genuine derivative witness. -/
theorem hasDerivAt_intervalHeatMode_space (n : ℕ) (t x : ℝ) :
    HasDerivAt (intervalHeatMode n t)
      (deriv (intervalDirichletSineMode n) x * intervalHeatTimeMode n t) x :=
  ((contDiff_intervalDirichletSineMode (k := 1) n).differentiable_one x).hasDerivAt.mul_const _

/-- The second spatial derivative of a separated heat mode. -/
theorem hasDerivAt_intervalHeatMode_space_deriv (n : ℕ) (t x : ℝ) :
    HasDerivAt
      (fun y ↦ deriv (intervalDirichletSineMode n) y * intervalHeatTimeMode n t)
      (-intervalDirichletEigenvalue n * intervalHeatMode n t x) x := by
  have h := (contDiff_intervalDirichletSineMode (k := 2) n).differentiable_deriv_two
  simpa only [intervalDirichletSineMode_second_deriv, intervalHeatMode, mul_assoc] using
    (h x).hasDerivAt.mul_const (intervalHeatTimeMode n t)

/-- The time derivative of a separated heat mode. -/
theorem hasDerivAt_intervalHeatMode_time (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun s ↦ intervalHeatMode n s x)
      (-intervalDirichletEigenvalue n * intervalHeatMode n t x) t := by
  have h : HasDerivAt (intervalHeatTimeMode n)
      (-intervalDirichletEigenvalue n * intervalHeatTimeMode n t) t := by
    unfold intervalHeatTimeMode
    cas
  simpa only [intervalHeatMode, mul_left_comm] using h.const_mul (intervalDirichletSineMode n x)

/-- A uniform bound for the first spatial derivative of a heat mode. -/
theorem norm_intervalHeatMode_space_deriv_le (n : ℕ) {τ t : ℝ}
    (ht : τ ≤ t) (x : ℝ) :
    ‖deriv (intervalDirichletSineMode n) x * intervalHeatTimeMode n t‖ ≤
      intervalHeatMajorant 1 τ n := by
  rw [norm_mul, Real.norm_of_nonneg (intervalHeatTimeMode_pos n t).le]
  simpa only [intervalHeatMajorant, pow_one] using
    mul_le_mul (norm_deriv_intervalDirichletSineMode_le n x)
      (intervalHeatTimeMode_antitone n ht) (intervalHeatTimeMode_pos n t).le
      (by positivity : 0 ≤ (n.succ : ℝ) * Real.pi)

/-- A uniform bound for the time derivative and second spatial derivative of a heat mode. -/
theorem norm_intervalHeatMode_time_deriv_le (n : ℕ) {τ t : ℝ}
    (ht : τ ≤ t) (x : ℝ) :
    ‖-intervalDirichletEigenvalue n * intervalHeatMode n t x‖ ≤
      intervalHeatMajorant 2 τ n := by
  rw [norm_mul, norm_neg,
    Real.norm_of_nonneg (intervalDirichletEigenvalue_nonneg n)]
  simpa only [intervalHeatMajorant, pow_zero, one_mul, intervalDirichletEigenvalue] using
    mul_le_mul_of_nonneg_left (norm_intervalHeatMode_le n ht x)
      (intervalDirichletEigenvalue_nonneg n)

variable {a : ℕ → ℝ} {C : ℝ}

/-- Absolute convergence of the heat series at every positive time. -/
theorem summable_intervalHeatSeries (ha : ∀ n, ‖a n‖ ≤ C) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    Summable (fun n ↦ a n * intervalHeatMode n t x) :=
  ((summable_intervalHeatMajorant 0 ht).mul_left C).of_norm_bounded fun n ↦ by
    rw [norm_mul]
    exact mul_le_mul (ha n) (norm_intervalHeatMode_le n le_rfl x) (norm_nonneg _)
      ((norm_nonneg (a 0)).trans (ha 0))

/-- Absolute convergence of the first spatial derivative series. -/
theorem summable_intervalHeatSeriesDx (ha : ∀ n, ‖a n‖ ≤ C) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    Summable (fun n ↦
      a n * (deriv (intervalDirichletSineMode n) x * intervalHeatTimeMode n t)) :=
  ((summable_intervalHeatMajorant 1 ht).mul_left C).of_norm_bounded fun n ↦ by
    rw [norm_mul]
    exact mul_le_mul (ha n) (norm_intervalHeatMode_space_deriv_le n le_rfl x)
      (norm_nonneg _) ((norm_nonneg (a 0)).trans (ha 0))

/-- Absolute convergence of the time derivative series. -/
theorem summable_intervalHeatSeriesDt (ha : ∀ n, ‖a n‖ ≤ C) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    Summable (fun n ↦ a n * (-intervalDirichletEigenvalue n * intervalHeatMode n t x)) :=
  ((summable_intervalHeatMajorant 2 ht).mul_left C).of_norm_bounded fun n ↦ by
    rw [norm_mul]
    exact mul_le_mul (ha n) (norm_intervalHeatMode_time_deriv_le n le_rfl x)
      (norm_nonneg _) ((norm_nonneg (a 0)).trans (ha 0))

/-- The finite separated solutions converge uniformly on every positive-time strip. -/
theorem tendstoUniformlyOn_intervalHeatSeries (ha : ∀ n, ‖a n‖ ≤ C)
    {τ : ℝ} (hτ : 0 < τ) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ) ↦ ∑ n ∈ Finset.range N, a n * intervalHeatMode n p.1 p.2)
      (fun p ↦ intervalHeatSeries a p.1 p.2) atTop {p | τ ≤ p.1} := by
  apply tendstoUniformlyOn_tsum_nat ((summable_intervalHeatMajorant 0 hτ).mul_left C)
  intro n p hp
  rw [norm_mul]
  exact mul_le_mul (ha n) (norm_intervalHeatMode_le n hp p.2) (norm_nonneg _)
    ((norm_nonneg (a 0)).trans (ha 0))

/-- Termwise differentiation of the heat series in space. -/
theorem hasDerivAt_intervalHeatSeries_space (ha : ∀ n, ‖a n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (intervalHeatSeries a t) (intervalHeatSeriesDx a t x) x := by
  refine hasDerivAt_tsum ((summable_intervalHeatMajorant 1 ht).mul_left C)
    (fun n y ↦ (hasDerivAt_intervalHeatMode_space n t y).const_mul (a n))
    (fun n y ↦ ?_) (summable_intervalHeatSeries ha ht 0) x
  rw [norm_mul]
  exact mul_le_mul (ha n) (norm_intervalHeatMode_space_deriv_le n le_rfl y)
    (norm_nonneg _) ((norm_nonneg (a 0)).trans (ha 0))

/-- Termwise second spatial differentiation, with the same series as the time derivative. -/
theorem hasDerivAt_intervalHeatSeriesDx_space (ha : ∀ n, ‖a n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (intervalHeatSeriesDx a t) (intervalHeatSeriesDt a t x) x := by
  refine hasDerivAt_tsum ((summable_intervalHeatMajorant 2 ht).mul_left C)
    (fun n y ↦ (hasDerivAt_intervalHeatMode_space_deriv n t y).const_mul (a n))
    (fun n y ↦ ?_) (summable_intervalHeatSeriesDx ha ht 0) x
  rw [norm_mul]
  exact mul_le_mul (ha n) (norm_intervalHeatMode_time_deriv_le n le_rfl y)
    (norm_nonneg _) ((norm_nonneg (a 0)).trans (ha 0))

/-- Termwise time differentiation uses a summable bound on the neighborhood `s > t / 2`. -/
theorem hasDerivAt_intervalHeatSeries_time (ha : ∀ n, ‖a n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s ↦ intervalHeatSeries a s x) (intervalHeatSeriesDt a t x) t := by
  refine hasDerivAt_tsum_of_isPreconnected
    ((summable_intervalHeatMajorant 2 (half_pos ht)).mul_left C)
    isOpen_Ioi (convex_Ioi (t / 2)).isPreconnected
    (fun n s _ ↦ (hasDerivAt_intervalHeatMode_time n s x).const_mul (a n))
    (fun n s hs ↦ ?_) (show t ∈ Set.Ioi (t / 2) from half_lt_self ht)
    (summable_intervalHeatSeries ha ht x) (half_lt_self ht)
  rw [norm_mul]
  exact mul_le_mul (ha n) (norm_intervalHeatMode_time_deriv_le n hs.le x)
    (norm_nonneg _) ((norm_nonneg (a 0)).trans (ha 0))

/-- The convergent sine series satisfies the heat equation pointwise at positive time. -/
theorem intervalHeatSeries_heat_equation (ha : ∀ n, ‖a n‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s ↦ intervalHeatSeries a s x) t =
      deriv (deriv (intervalHeatSeries a t)) x := by
  have hspace : deriv (intervalHeatSeries a t) = intervalHeatSeriesDx a t :=
    funext fun y ↦ (hasDerivAt_intervalHeatSeries_space ha ht y).deriv
  rw [(hasDerivAt_intervalHeatSeries_time ha ht x).deriv, hspace,
    (hasDerivAt_intervalHeatSeriesDx_space ha ht x).deriv]

/-- Every heat sine series vanishes at the left endpoint. -/
@[simp] theorem intervalHeatSeries_left_boundary (a : ℕ → ℝ) (t : ℝ) :
    intervalHeatSeries a t 0 = 0 := by
  simp [intervalHeatSeries]

/-- Every heat sine series vanishes at the right endpoint. -/
@[simp] theorem intervalHeatSeries_right_boundary (a : ℕ → ℝ) (t : ℝ) :
    intervalHeatSeries a t 1 = 0 := by
  simp [intervalHeatSeries]

end HeatEquation
