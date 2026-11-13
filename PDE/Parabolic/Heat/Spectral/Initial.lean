/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.Regularity
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Uniform initial attainment for summable sine coefficients

Absolutely summable sine coefficients define continuous Dirichlet data. Their heat series
is jointly continuous up to time zero and attains those data uniformly in space.
The coefficient hypothesis is a data-space condition; convergence and differentiation of
the heat solution are conclusions (`Spectral.Interval`, `Spectral.Regularity`).
-/

@[expose] public section

namespace HeatEquation

open PDE.Representations Filter
open scoped Topology

variable {a : ℕ → ℝ}

/-- Summable coefficient data give absolute convergence even at time zero. -/
theorem summable_intervalHeatSeries_of_summable (ha : Summable (fun n ↦ ‖a n‖))
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    Summable (fun n ↦ a n * intervalHeatMode n t x) := by
  apply ha.of_norm_bounded
  intro n
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  simpa [intervalHeatMajorant, intervalHeatTimeMode] using norm_intervalHeatMode_le n ht x

/-- Joint continuity up to the initial time for absolutely summable sine data. -/
theorem continuousOn_intervalHeatSeries_of_summable (ha : Summable (fun n ↦ ‖a n‖)) :
    ContinuousOn (fun p : ℝ × ℝ ↦ intervalHeatSeries a p.1 p.2) {p | 0 ≤ p.1} := by
  refine continuousOn_tsum (fun n ↦ ?_) ha (fun n p hp ↦ ?_)
  · unfold intervalHeatMode intervalHeatTimeMode intervalDirichletSineMode
    fun_prop
  · rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    simpa [intervalHeatMajorant, intervalHeatTimeMode] using norm_intervalHeatMode_le n hp p.2

/-- A nonnegative-time multiplier differs from its initial value by at most one. -/
theorem norm_intervalHeatTimeMode_sub_one_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖intervalHeatTimeMode n t - 1‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [intervalHeatTimeMode_pos n t]
  · linarith [intervalHeatTimeMode_le_one n ht]

/-- The scalar majorant of the initial error tends to zero by dominated convergence. -/
theorem tendsto_intervalHeatSeries_initial_majorant
    (ha : Summable (fun n ↦ ‖a n‖)) :
    Tendsto (fun t ↦ ∑' n, ‖a n‖ * ‖intervalHeatTimeMode n t - 1‖)
      (𝓝[Set.Ici 0] 0) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence ha
    (𝓕 := 𝓝[Set.Ici 0] 0)
    (f := fun t n ↦ ‖a n‖ * ‖intervalHeatTimeMode n t - 1‖)
    (g := fun _ ↦ (0 : ℝ)) ?_ ?_
  · simpa using h
  · intro n
    have hc : Continuous (fun t ↦ ‖a n‖ * ‖intervalHeatTimeMode n t - 1‖) := by
      unfold intervalHeatTimeMode
      fun_prop
    simpa only [ContinuousWithinAt, intervalHeatTimeMode, mul_zero, Real.exp_zero,
      sub_self, norm_zero] using hc.continuousWithinAt
      (s := Set.Ici 0) (x := 0)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    intro n
    rw [norm_mul, norm_norm, norm_norm]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_intervalHeatTimeMode_sub_one_le n ht)

/-- A spatially uniform bound for the initial error. -/
theorem norm_intervalHeatSeries_sub_initial_le (ha : Summable (fun n ↦ ‖a n‖))
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ‖intervalHeatSeries a t x - intervalHeatSeries a 0 x‖ ≤
      ∑' n, ‖a n‖ * ‖intervalHeatTimeMode n t - 1‖ := by
  have hbound : Summable (fun n ↦ ‖a n‖ * ‖intervalHeatTimeMode n t - 1‖) :=
    ha.of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦
      mul_le_of_le_one_right (norm_nonneg _) (norm_intervalHeatTimeMode_sub_one_le n ht)
  rw [intervalHeatSeries, intervalHeatSeries,
    ← (summable_intervalHeatSeries_of_summable ha ht x).tsum_sub
      (summable_intervalHeatSeries_of_summable ha le_rfl x)]
  apply tsum_of_norm_bounded hbound.hasSum
  intro n
  have heq : a n * intervalHeatMode n t x - a n * intervalHeatMode n 0 x =
      (a n * intervalDirichletSineMode n x) * (intervalHeatTimeMode n t - 1) := by
    simp only [intervalHeatMode, intervalHeatTimeMode, mul_zero, Real.exp_zero]
    ring
  rw [heq, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (norm_nonneg _) (norm_intervalDirichletSineMode_le n x))
    (norm_nonneg _)

/-- The heat series attains its initial sine sum uniformly on the entire real line,
hence in particular uniformly on the closed unit interval. -/
theorem tendstoUniformly_intervalHeatSeries_initial (ha : Summable (fun n ↦ ‖a n‖)) :
    TendstoUniformly (fun t x ↦ intervalHeatSeries a t x) (intervalHeatSeries a 0)
      (𝓝[Set.Ici 0] 0) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(tendsto_order.mp (tendsto_intervalHeatSeries_initial_majorant ha)).2 ε hε,
    self_mem_nhdsWithin] with t ht ht0
  intro x
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_intervalHeatSeries_sub_initial_le ha ht0 x).trans_lt ht

end HeatEquation
