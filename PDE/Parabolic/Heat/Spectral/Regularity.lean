/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.Interval
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Continuity of the differentiated heat series

The same summable bounds that justify termwise differentiation also give joint continuity
of the solution and its derivatives. Thus the positive-time solution is classical: `u`,
`u_x`, `u_xx`, and `u_t` are continuous, and `u_t = u_xx`.
-/

@[expose] public section

namespace HeatEquation

open PDE.Representations Filter

variable {a : ℕ → ℝ} {C : ℝ}

/-- Uniform convergence of the first spatial derivative series on a positive-time strip. -/
theorem tendstoUniformlyOn_intervalHeatSeriesDx (ha : ∀ n, ‖a n‖ ≤ C)
    {τ : ℝ} (hτ : 0 < τ) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ) ↦ ∑ n ∈ Finset.range N,
        a n * (deriv (intervalDirichletSineMode n) p.2 * intervalHeatTimeMode n p.1))
      (fun p ↦ intervalHeatSeriesDx a p.1 p.2) atTop {p | τ ≤ p.1} := by
  apply tendstoUniformlyOn_tsum_nat ((summable_intervalHeatMajorant 1 hτ).mul_left C)
  intro n p hp
  rw [norm_mul]
  exact mul_le_mul (ha n) (norm_intervalHeatMode_space_deriv_le n hp p.2) (norm_nonneg _)
    ((norm_nonneg (a 0)).trans (ha 0))

/-- Uniform convergence of the time and second spatial derivative series on a time strip. -/
theorem tendstoUniformlyOn_intervalHeatSeriesDt (ha : ∀ n, ‖a n‖ ≤ C)
    {τ : ℝ} (hτ : 0 < τ) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ) ↦ ∑ n ∈ Finset.range N,
        a n * (-intervalDirichletEigenvalue n * intervalHeatMode n p.1 p.2))
      (fun p ↦ intervalHeatSeriesDt a p.1 p.2) atTop {p | τ ≤ p.1} := by
  apply tendstoUniformlyOn_tsum_nat ((summable_intervalHeatMajorant 2 hτ).mul_left C)
  intro n p hp
  rw [norm_mul]
  exact mul_le_mul (ha n) (norm_intervalHeatMode_time_deriv_le n hp p.2) (norm_nonneg _)
    ((norm_nonneg (a 0)).trans (ha 0))

private theorem continuousOn_positiveTime_of_strips {f : ℝ × ℝ → ℝ}
    (hf : ∀ τ : ℝ, 0 < τ → ContinuousOn f {p | τ ≤ p.1}) :
    ContinuousOn f {p | 0 < p.1} := by
  apply continuousOn_of_locally_continuousOn
  intro p hp
  refine ⟨{q | p.1 / 2 < q.1}, isOpen_lt continuous_const continuous_fst,
    (show p.1 / 2 < p.1 from half_lt_self hp), (hf (p.1 / 2) (half_pos hp)).mono ?_⟩
  intro q hq
  exact (show p.1 / 2 < q.1 from hq.2).le

/-- Joint continuity of the solution at positive time, including the spatial endpoints. -/
theorem continuousOn_intervalHeatSeries (ha : ∀ n, ‖a n‖ ≤ C) :
    ContinuousOn (fun p : ℝ × ℝ ↦ intervalHeatSeries a p.1 p.2) {p | 0 < p.1} := by
  apply continuousOn_positiveTime_of_strips
  intro τ hτ
  apply (tendstoUniformlyOn_intervalHeatSeries ha hτ).continuousOn
  apply Frequently.of_forall
  intro N
  apply continuousOn_finsetSum
  intro n _
  unfold intervalHeatMode intervalHeatTimeMode intervalDirichletSineMode
  fun_prop

/-- Joint continuity of the first spatial derivative at positive time. -/
theorem continuousOn_intervalHeatSeriesDx (ha : ∀ n, ‖a n‖ ≤ C) :
    ContinuousOn (fun p : ℝ × ℝ ↦ intervalHeatSeriesDx a p.1 p.2) {p | 0 < p.1} := by
  apply continuousOn_positiveTime_of_strips
  intro τ hτ
  apply (tendstoUniformlyOn_intervalHeatSeriesDx ha hτ).continuousOn
  apply Frequently.of_forall
  intro N
  apply continuousOn_finsetSum
  intro n _
  simp_rw [intervalDirichletSineMode_deriv]
  unfold intervalHeatTimeMode
  fun_prop

/-- Joint continuity of the time and second spatial derivatives at positive time. -/
theorem continuousOn_intervalHeatSeriesDt (ha : ∀ n, ‖a n‖ ≤ C) :
    ContinuousOn (fun p : ℝ × ℝ ↦ intervalHeatSeriesDt a p.1 p.2) {p | 0 < p.1} := by
  apply continuousOn_positiveTime_of_strips
  intro τ hτ
  apply (tendstoUniformlyOn_intervalHeatSeriesDt ha hτ).continuousOn
  apply Frequently.of_forall
  intro N
  apply continuousOn_finsetSum
  intro n _
  unfold intervalHeatMode intervalHeatTimeMode intervalDirichletSineMode
  fun_prop

end HeatEquation
