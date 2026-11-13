/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.Initial
public import PDE.Analysis.Fourier.SineSeries.SmoothData

/-!
# A classical Dirichlet solution constructed by separation of variables

For odd, two-periodic `C²` real data, the Fourier sine coefficients construct a
classical heat solution on the unit interval. The series converges absolutely, its
positive-time derivatives are obtained term by term, and its initial value is attained
uniformly. The solution and its time and first two space derivatives are jointly
continuous at positive time; the solution is jointly continuous up to time zero.

This is the separation-of-variables construction of Evans, *Partial Differential
Equations*, §4.1.1, for smooth compatible data on the unit interval. The Fourier
completeness step uses Mathlib's circle basis.
-/

@[expose] public section

namespace HeatEquation

open PDE.Analysis.Fourier.SineSeries PDE.Representations Filter
open scoped Topology

/-- Odd, two-periodic `C²` data admit a classical Dirichlet heat solution on `[0, 1]`,
constructed by the convergent sine series. The derivative witnesses identify the
termwise series, and the continuity assertions give the classical positive-time class.
Initial attainment is uniform on `ℝ`, and thus also on `[0, 1]`.

There is no assumed solution, convergent expansion, or termwise differentiation identity:
the coefficients are computed from `g`, and all these properties are conclusions. -/
theorem exists_classical_intervalHeatSolution (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hper : Function.Periodic g 2) (hodd : ∀ x, g (-x) = -g x) :
    let a : ℕ → ℝ := fun n ↦ 2 * ∫ x in (0 : ℝ)..1, g x * intervalDirichletSineMode n x
    ∃ u : ℝ → ℝ → ℝ,
      (∀ t, 0 ≤ t → ∀ x, HasSum (fun n ↦ a n * intervalHeatMode n t x) (u t x)) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ u p.1 p.2) {p | 0 ≤ p.1} ∧
      (∀ t, 0 < t → ∀ x,
        HasDerivAt (u t) (intervalHeatSeriesDx a t x) x ∧
        HasDerivAt (deriv (u t)) (intervalHeatSeriesDt a t x) x ∧
        HasDerivAt (fun s ↦ u s x) (intervalHeatSeriesDt a t x) t) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (u p.1) p.2) {p | 0 < p.1} ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (deriv (u p.1)) p.2) {p | 0 < p.1} ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun s ↦ u s p.2) p.1) {p | 0 < p.1} ∧
      (∀ t, 0 < t → ∀ x, deriv (fun s ↦ u s x) t = deriv (deriv (u t)) x) ∧
      (∀ t, 0 ≤ t → u t 0 = 0 ∧ u t 1 = 0) ∧
      (∀ x, u 0 x = g x) ∧
      TendstoUniformly u g (𝓝[Set.Ici 0] 0) := by
  simp only [← periodicCoefficient_eq_integral g hg.continuous hper hodd]
  let a := periodicCoefficient g hg.continuous hper
  have ha : Summable (fun n ↦ ‖a n‖) := summable_norm_periodicCoefficient g hg hper
  have hb : ∀ n, ‖a n‖ ≤ ∑' i, ‖a i‖ := fun n ↦
    ha.le_tsum n (fun _ _ ↦ norm_nonneg _)
  have hspace (t : ℝ) (ht : 0 < t) :
      deriv (intervalHeatSeries a t) = intervalHeatSeriesDx a t :=
    funext fun x ↦ (hasDerivAt_intervalHeatSeries_space hb ht x).deriv
  have hsecond (t : ℝ) (ht : 0 < t) (x : ℝ) :
      deriv (deriv (intervalHeatSeries a t)) x = intervalHeatSeriesDt a t x := by
    rw [hspace t ht, (hasDerivAt_intervalHeatSeriesDx_space hb ht x).deriv]
  have hinitial : intervalHeatSeries a 0 = g := by
    funext x
    simpa only [intervalHeatSeries, intervalHeatMode_initial_trace] using
      (hasSum_periodicCoefficient_sineMode g hg hper hodd x).tsum_eq
  refine ⟨intervalHeatSeries a, fun t ht x ↦
    (summable_intervalHeatSeries_of_summable ha ht x).hasSum,
    continuousOn_intervalHeatSeries_of_summable ha, ?_, ?_, ?_, ?_,
    fun _ ht x ↦ intervalHeatSeries_heat_equation hb ht x,
    fun t _ ↦ ⟨intervalHeatSeries_left_boundary a t, intervalHeatSeries_right_boundary a t⟩,
    fun x ↦ congrFun hinitial x, ?_⟩
  · intro t ht x
    refine ⟨hasDerivAt_intervalHeatSeries_space hb ht x, ?_,
      hasDerivAt_intervalHeatSeries_time hb ht x⟩
    rw [hspace t ht]
    exact hasDerivAt_intervalHeatSeriesDx_space hb ht x
  · apply (continuousOn_intervalHeatSeriesDx hb).congr
    intro p hp
    exact (hasDerivAt_intervalHeatSeries_space hb hp p.2).deriv
  · apply (continuousOn_intervalHeatSeriesDt hb).congr
    intro p hp
    exact hsecond p.1 hp p.2
  · apply (continuousOn_intervalHeatSeriesDt hb).congr
    intro p hp
    exact (hasDerivAt_intervalHeatSeries_time hb hp p.2).deriv
  · simpa only [hinitial] using tendstoUniformly_intervalHeatSeries_initial ha

end HeatEquation
