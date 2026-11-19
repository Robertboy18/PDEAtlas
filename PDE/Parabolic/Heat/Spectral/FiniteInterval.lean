/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.ContinuousInitial
public import PDE.Parabolic.Heat.Spectral.Rescaling
import CAS.ExactTactic

/-!
# Continuous Dirichlet data on a finite interval

The initial coefficients are the normalized sine integrals on `[a, b]`.
Parabolic rescaling gives a convergent classical heat series at positive time,
with zero boundary values and uniform initial attainment on the closed interval
for arbitrary continuous zero-boundary data. The construction uses the same
unit-interval coefficients as the `L²` evolution of `Spectral.L2Evolution`.
-/

@[expose] public section

namespace HeatEquation

open Set Filter PDE.Analysis.Fourier.SineSeries PDE.Representations
open scoped Topology

/-- Sine coefficients of interval data, defined by transport to the unit interval.
The normalized integral formula is proved in `finiteIntervalCoefficient_eq_integral`. -/
noncomputable def finiteIntervalCoefficient (a b : ℝ) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  intervalCoefficient (fun y ↦ g (a + (b - a) * y)) n

/-- The affine unit-interval parametrization preserves continuity on the closed interval. -/
theorem continuousOn_finiteIntervalPullback {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    ContinuousOn (fun y ↦ g (a + (b - a) * y)) (Icc 0 1) := by
  apply hg.comp (f := fun y ↦ a + (b - a) * y) (by fun_prop)
  intro y hy
  constructor <;> nlinarith [hy.1, hy.2]

/-- The transported coefficients have the usual normalization `2 / (b - a)` and
frequency `(n + 1)π / (b - a)` in the original interval coordinates. -/
theorem finiteIntervalCoefficient_eq_integral {a b : ℝ} (hab : a < b)
    (g : ℝ → ℝ) (n : ℕ) :
    finiteIntervalCoefficient a b g n =
      2 / (b - a) * ∫ x in a..b, g x * Real.sin (finiteIntervalFrequency a b n * (x - a)) := by
  have hL : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have he (y : ℝ) :
      Real.sin (finiteIntervalFrequency a b n * (a + (b - a) * y - a)) =
        intervalDirichletSineMode n y := by
    unfold finiteIntervalFrequency intervalDirichletSineMode
    cas using hL
  have hb : a + (b - a) * 1 = b := by cas
  have hchange := intervalIntegral.integral_comp_add_mul
    (fun x ↦ g x * Real.sin (finiteIntervalFrequency a b n * (x - a)))
    (a := (0 : ℝ)) (b := 1) hL a
  simp only [he, mul_zero, add_zero, hb, smul_eq_mul] at hchange
  unfold finiteIntervalCoefficient intervalCoefficient
  rw [hchange]
  ring

/-- Uniform initial attainment on any nondegenerate finite interval. The approach to
zero is through positive times; no convergence of the undamped sine series is required. -/
theorem tendstoUniformlyOn_finiteIntervalHeatSeries_initial {a b : ℝ} (hab : a < b)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) (ha : g a = 0) (hb : g b = 0) :
    TendstoUniformlyOn (finiteIntervalHeatSeries a b (finiteIntervalCoefficient a b g)) g
      (𝓝[>] (0 : ℝ)) (Icc a b) := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have he : a + (b - a) * 1 = b := by cas
  have hf := continuousOn_finiteIntervalPullback hab hg
  have htrace := tendstoUniformlyOn_intervalHeatSeries_initial_of_continuousOn hf
    (by simpa only [mul_zero, add_zero] using ha) (by simpa only [he] using hb)
  have hscale : Tendsto (fun t : ℝ ↦ t / (b - a) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [zero_div, id_eq] using
        ((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)).div_const
          ((b - a) ^ 2)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_pos ht (sq_pos_of_pos hL)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hscale.eventually (Metric.tendstoUniformlyOn_iff.mp htrace ε hε)] with t ht
  intro x hx
  have hy : (x - a) / (b - a) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hx.1) hL.le,
      (div_le_one hL).mpr (sub_le_sub_right hx.2 a)⟩
  have hi : a + (b - a) * ((x - a) / (b - a)) = x := by cas using hL.ne'
  unfold finiteIntervalHeatSeries finiteIntervalCoefficient
  simpa only [hi] using
    ht ((x - a) / (b - a)) hy

/-- Every continuous function on a finite interval with zero endpoint values has
a classical positive-time Dirichlet heat solution given by its convergent sine
series, with space and time derivatives and uniform initial attainment.

The series at positive time, its derivatives, and the initial trace belong to the
same witness. The raw undamped series at time zero is not used as a pointwise representative. -/
theorem exists_classical_finiteIntervalHeatSolution_of_continuousOn {a b : ℝ} (hab : a < b)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b)) (ha : g a = 0) (hb : g b = 0) :
    let c := finiteIntervalCoefficient a b g
    ∃ u : ℝ → ℝ → ℝ,
      (∀ t, 0 < t → ∀ x, HasSum (fun n ↦ c n * finiteIntervalHeatMode a b n t x) (u t x)) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ u p.1 p.2) {p | 0 < p.1} ∧
      (∀ t, 0 < t → ∀ x,
        HasDerivAt (u t) (finiteIntervalHeatSeriesDx a b c t x) x ∧
        HasDerivAt (deriv (u t)) (finiteIntervalHeatSeriesDt a b c t x) x ∧
        HasDerivAt (fun s ↦ u s x) (finiteIntervalHeatSeriesDt a b c t x) t) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (u p.1) p.2) {p | 0 < p.1} ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (deriv (u p.1)) p.2) {p | 0 < p.1} ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun s ↦ u s p.2) p.1) {p | 0 < p.1} ∧
      (∀ t, 0 < t → ∀ x, deriv (fun s ↦ u s x) t = deriv (deriv (u t)) x) ∧
      (∀ t, 0 < t → u t a = 0 ∧ u t b = 0) ∧
      TendstoUniformlyOn u g (𝓝[>] (0 : ℝ)) (Icc a b) := by
  let c := finiteIntervalCoefficient a b g
  have hm := memLp_interval_of_continuousOn (continuousOn_finiteIntervalPullback hab hg) 2
  have hbound : ∀ n, ‖c n‖ ≤ 2 * ‖oddIntervalL2 _ hm‖ := norm_intervalCoefficient_le hm
  have hspace (t : ℝ) (ht : 0 < t) :
      deriv (finiteIntervalHeatSeries a b c t) = finiteIntervalHeatSeriesDx a b c t :=
    funext fun x ↦ (hasDerivAt_finiteIntervalHeatSeries_space hab hbound ht x).deriv
  have hsecond (t : ℝ) (ht : 0 < t) (x : ℝ) :
      deriv (deriv (finiteIntervalHeatSeries a b c t)) x =
        finiteIntervalHeatSeriesDt a b c t x := by
    rw [hspace t ht, (hasDerivAt_finiteIntervalHeatSeriesDx_space hab hbound ht x).deriv]
  refine ⟨finiteIntervalHeatSeries a b c, fun t ht x ↦
    hasSum_finiteIntervalHeatSeries hab hbound ht x,
    continuousOn_finiteIntervalHeatSeries hab hbound, ?_, ?_, ?_, ?_,
    fun _ ht x ↦ finiteIntervalHeatSeries_heat_equation hab hbound ht x,
    fun t _ ↦ ⟨finiteIntervalHeatSeries_left_boundary a b c t,
      finiteIntervalHeatSeries_right_boundary hab c t⟩,
    tendstoUniformlyOn_finiteIntervalHeatSeries_initial hab hg ha hb⟩
  · intro t ht x
    refine ⟨hasDerivAt_finiteIntervalHeatSeries_space hab hbound ht x, ?_,
      hasDerivAt_finiteIntervalHeatSeries_time hab hbound ht x⟩
    rw [hspace t ht]
    exact hasDerivAt_finiteIntervalHeatSeriesDx_space hab hbound ht x
  · apply (continuousOn_finiteIntervalHeatSeriesDx hab hbound).congr
    intro p hp
    exact (hasDerivAt_finiteIntervalHeatSeries_space hab hbound hp p.2).deriv
  · apply (continuousOn_finiteIntervalHeatSeriesDt hab hbound).congr
    intro p hp
    exact hsecond p.1 hp p.2
  · apply (continuousOn_finiteIntervalHeatSeriesDt hab hbound).congr
    intro p hp
    exact (hasDerivAt_finiteIntervalHeatSeries_time hab hbound hp p.2).deriv

end HeatEquation
