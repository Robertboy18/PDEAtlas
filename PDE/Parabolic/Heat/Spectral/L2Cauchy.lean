/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.L2Evolution
public import PDE.Analysis.Fourier.SineSeries.IntervalRestriction

/-!
# Classical positive-time heat flow with an interval `L²` initial trace

Arbitrary real `L²(0,1)` data determine the sine coefficients by integration.
The resulting series is classical for positive time, vanishes at both endpoints,
and attains the given data in the ordinary interval `L²` norm. No endpoint values
or pointwise initial Fourier expansion are required.

Uniform initial attainment for interval `C²` data is `Spectral.IntervalCauchy`.
-/

@[expose] public section

namespace HeatEquation

open MeasureTheory Set Filter PDE.Representations PDE.Analysis.Fourier.SineSeries
open scoped ENNReal NNReal Topology

/-- The real interval `L²` trajectory obtained from the Fourier heat evolution. -/
noncomputable def intervalHeatTrajectory (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (t : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  Complex.reCLM.compLpL 2 _ (circleIntervalRestriction (intervalHeatL2 g hg t))

/-- The interval trajectory is continuous in the usual Lebesgue `L²` norm. -/
theorem continuous_intervalHeatTrajectory {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    Continuous (intervalHeatTrajectory g hg) :=
  (Complex.reCLM.compLpL 2 _).continuous.comp
    (circleIntervalRestriction.continuous.comp (continuous_intervalHeatL2 hg))

/-- The real interval trajectory starts at the original data, modulo null sets. -/
@[simp] theorem intervalHeatTrajectory_zero {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    intervalHeatTrajectory g hg 0 = hg.toLp g := by
  unfold intervalHeatTrajectory
  rw [intervalHeatL2_zero, circleIntervalRestriction_oddIntervalL2]
  apply Lp.ext
  have hg' : MemLp (fun x ↦ (g x : ℂ)) 2 (volume.restrict (Ioc 0 1)) := hg.ofReal
  filter_upwards [Complex.reCLM.coeFn_compLpL (hg'.toLp _),
    hg'.coeFn_toLp, hg.coeFn_toLp] with x hx hcx hgx
  rw [hx, hcx, hgx]
  rfl

/-- At every positive time the real trajectory is represented by the pointwise
classical sine series. This identifies its initial norm limit with that solution. -/
theorem intervalHeatTrajectory_coe {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    intervalHeatTrajectory g hg t =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      intervalHeatSeries (intervalCoefficient g) t := by
  have hc := ae_interval_coe_of_ae_circle
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
      (intervalHeatCircle g t))
  rw [toLp_intervalHeatCircle hg ht] at hc
  filter_upwards [Complex.reCLM.coeFn_compLpL
    (circleIntervalRestriction (intervalHeatL2 g hg t)),
    circleIntervalRestriction_coe (intervalHeatL2 g hg t), hc] with x hx hr hcx
  change (Complex.reCLM.compLpL 2 _ _ : Lp ℝ 2 _) x = _
  rw [hx, hr, hcx, intervalHeatCircle_coe hg ht]
  rfl

/-- The positive-time solution attains arbitrary `L²` data in interval norm. -/
theorem tendsto_intervalHeatTrajectory_initial {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    Tendsto (intervalHeatTrajectory g hg) (𝓝 (0 : ℝ≥0)) (𝓝 (hg.toLp g)) := by
  simpa only [intervalHeatTrajectory_zero] using
    (continuous_intervalHeatTrajectory hg).continuousAt.tendsto (x := (0 : ℝ≥0))

/-- Arbitrary interval `L²` data give a convergent classical Dirichlet sine-series
solution for positive time and a continuous interval `L²` trajectory representing it.
The first two spatial derivatives and the time derivative are the differentiated
series. Initial attainment is in `L²`, with no pointwise claim at time zero. -/
theorem exists_classical_intervalHeatSolution_of_memLp (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    let a := intervalCoefficient g
    ∃ (u : ℝ → ℝ → ℝ) (U : ℝ≥0 → Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) 1))),
      (∀ t, 0 < t → ∀ x, HasSum (fun n ↦ a n * intervalHeatMode n t x) (u t x)) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ u p.1 p.2) {p | 0 < p.1} ∧
      (∀ t, 0 < t → ∀ x,
        HasDerivAt (u t) (intervalHeatSeriesDx a t x) x ∧
        HasDerivAt (deriv (u t)) (intervalHeatSeriesDt a t x) x ∧
        HasDerivAt (fun s ↦ u s x) (intervalHeatSeriesDt a t x) t) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (u p.1) p.2) {p | 0 < p.1} ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (deriv (u p.1)) p.2) {p | 0 < p.1} ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun s ↦ u s p.2) p.1) {p | 0 < p.1} ∧
      (∀ t, 0 < t → ∀ x, deriv (fun s ↦ u s x) t = deriv (deriv (u t)) x) ∧
      (∀ t, 0 < t → u t 0 = 0 ∧ u t 1 = 0) ∧
      Continuous U ∧
      (∀ t : ℝ≥0, 0 < (t : ℝ) → U t =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] u t) ∧
      U 0 = hg.toLp g ∧ Tendsto U (𝓝 (0 : ℝ≥0)) (𝓝 (hg.toLp g)) := by
  let a := intervalCoefficient g
  have hb : ∀ n, ‖a n‖ ≤ 2 * ‖oddIntervalL2 g hg‖ := norm_intervalCoefficient_le hg
  have hspace (t : ℝ) (ht : 0 < t) :
      deriv (intervalHeatSeries a t) = intervalHeatSeriesDx a t :=
    funext fun x ↦ (hasDerivAt_intervalHeatSeries_space hb ht x).deriv
  have hsecond (t : ℝ) (ht : 0 < t) (x : ℝ) :
      deriv (deriv (intervalHeatSeries a t)) x = intervalHeatSeriesDt a t x := by
    rw [hspace t ht, (hasDerivAt_intervalHeatSeriesDx_space hb ht x).deriv]
  refine ⟨intervalHeatSeries a, intervalHeatTrajectory g hg,
    fun t ht x ↦ (summable_intervalHeatSeries hb ht x).hasSum,
    continuousOn_intervalHeatSeries hb, ?_, ?_, ?_, ?_,
    fun _ ht x ↦ intervalHeatSeries_heat_equation hb ht x,
    fun t _ ↦ ⟨intervalHeatSeries_left_boundary a t, intervalHeatSeries_right_boundary a t⟩,
    continuous_intervalHeatTrajectory hg, fun _ ht ↦ intervalHeatTrajectory_coe hg ht,
    intervalHeatTrajectory_zero hg, tendsto_intervalHeatTrajectory_initial hg⟩
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

end HeatEquation
