/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.IntervalData
public import PDE.Parabolic.Heat.Spectral.Initial

/-!
# The interval Dirichlet heat problem for arbitrary `C²` data

Interval smoothness and zero endpoint values suffice for the classical sine-series
construction. Absolute summability and reconstruction follow from interval integration
by parts and Fourier completeness. No smooth periodic extension is assumed.

The solution attains the given data uniformly on `[0, 1]`. Its periodic continuation
outside that interval need not equal the supplied real function.
-/

@[expose] public section

namespace HeatEquation

open PDE.Analysis.Fourier.SineSeries PDE.Representations Filter Set
open scoped Topology

/-- For arbitrary `C²` data on `[0, 1]` with zero endpoint values, the convergent
sine series gives a classical positive-time Dirichlet heat solution and attains the
data uniformly on the closed interval. Derivatives are the termwise differentiated
series and are jointly continuous at positive time.

The regularity hypothesis concerns only the interval. In particular it imposes no
condition on the endpoint second derivatives or on an odd periodic extension. -/
theorem exists_classical_intervalHeatSolution_of_contDiffOn (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ 2 g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0) :
    let a := intervalCoefficient g
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
      EqOn (u 0) g (Icc 0 1) ∧
      TendstoUniformlyOn u g (𝓝[Ici 0] 0) (Icc 0 1) := by
  let a := intervalCoefficient g
  have ha : Summable (fun n ↦ ‖a n‖) := summable_norm_intervalCoefficient hg hzero hone
  have hb : ∀ n, ‖a n‖ ≤ ∑' i, ‖a i‖ := fun n ↦
    ha.le_tsum n (fun _ _ ↦ norm_nonneg _)
  have hspace (t : ℝ) (ht : 0 < t) :
      deriv (intervalHeatSeries a t) = intervalHeatSeriesDx a t :=
    funext fun x ↦ (hasDerivAt_intervalHeatSeries_space hb ht x).deriv
  have hsecond (t : ℝ) (ht : 0 < t) (x : ℝ) :
      deriv (deriv (intervalHeatSeries a t)) x = intervalHeatSeriesDt a t x := by
    rw [hspace t ht, (hasDerivAt_intervalHeatSeriesDx_space hb ht x).deriv]
  have hinitial : EqOn (intervalHeatSeries a 0) g (Icc 0 1) := by
    intro x hx
    simpa only [intervalHeatSeries, intervalHeatMode_initial_trace] using
      (hasSum_intervalCoefficient_sineMode hg hzero hone hx).tsum_eq
  refine ⟨intervalHeatSeries a, fun t ht x ↦
    (summable_intervalHeatSeries_of_summable ha ht x).hasSum,
    continuousOn_intervalHeatSeries_of_summable ha, ?_, ?_, ?_, ?_,
    fun _ ht x ↦ intervalHeatSeries_heat_equation hb ht x,
    fun t _ ↦ ⟨intervalHeatSeries_left_boundary a t, intervalHeatSeries_right_boundary a t⟩,
    hinitial, ?_⟩
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
  · exact (tendstoUniformly_intervalHeatSeries_initial ha).tendstoUniformlyOn.congr_right hinitial

end HeatEquation
