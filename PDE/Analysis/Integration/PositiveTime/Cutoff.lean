/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.PeakFunction

/-!
# Smooth cutoffs approaching the initial time

The derivative of the increasing cutoff on `[ε, 2ε]` has mass one and recovers
right limits.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

/-- For positive `ε`, a smooth cutoff that vanishes before `ε` and equals one after `2ε`. -/
def initialTimeCutoff (ε t : ℝ) : ℝ :=
  Real.smoothTransition (t / ε - 1)

/-- The time transition is twice continuously differentiable. -/
theorem contDiff_initialTimeCutoff (ε : ℝ) :
    ContDiff ℝ 2 (initialTimeCutoff ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.div_const ε).sub contDiff_const)

/-- The initial time transition vanishes before its transition interval. -/
theorem initialTimeCutoff_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ ε) :
    initialTimeCutoff ε t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by
    have := (div_le_one hε).2 ht
    linarith)

/-- The initial time transition is one after its transition interval. -/
theorem initialTimeCutoff_one {ε t : ℝ} (hε : 0 < ε) (ht : 2 * ε ≤ t) :
    initialTimeCutoff ε t = 1 :=
  Real.smoothTransition.one_of_one_le (by
    have := (le_div_iff₀ hε).2 ht
    linarith)

/-- The increasing time transition has nonnegative derivative. -/
theorem deriv_initialTimeCutoff_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (initialTimeCutoff ε) t := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  exact Real.smoothTransition.monotone (sub_le_sub_right (div_le_div_of_nonneg_right hxy hε.le) 1)

/-- The derivative of the time transition is continuous. -/
theorem continuous_deriv_initialTimeCutoff (ε : ℝ) :
    Continuous (deriv (initialTimeCutoff ε)) :=
  (contDiff_initialTimeCutoff ε).continuous_deriv (by norm_num)

/-- The derivative is supported on the transition interval. -/
theorem deriv_initialTimeCutoff_eq_zero {ε t : ℝ} (hε : 0 < ε)
    (ht_original : t ∉ Icc ε (2 * ε)) :
    deriv (initialTimeCutoff ε) t = 0 := by
  rcases lt_or_ge t ε with ht | ht
  · have heq : initialTimeCutoff ε =ᶠ[𝓝 t] fun _ ↦ 0 := by
      filter_upwards [gt_mem_nhds ht] with s hs
      exact initialTimeCutoff_zero hε hs.le
    simpa using heq.deriv_eq
  · have ht : 2 * ε < t := lt_of_not_ge (fun h ↦ ht_original ⟨ht, h⟩)
    have heq : initialTimeCutoff ε =ᶠ[𝓝 t] fun _ ↦ 1 := by
      filter_upwards [lt_mem_nhds ht] with s hs
      exact initialTimeCutoff_one hε hs.le
    simpa using heq.deriv_eq

/-- A sufficiently small initial transition has derivative of mass one. -/
theorem setIntegral_deriv_initialTimeCutoff {ε : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1 / 2) :
    (∫ t : ℝ in Ioc 0 1, deriv (initialTimeCutoff ε) t) = 1 := by
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 from zero_le_one)]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun _ _ ↦ (contDiff_initialTimeCutoff ε).differentiable (by simp) _)
    ((continuous_deriv_initialTimeCutoff ε).intervalIntegrable 0 1)]
  rw [initialTimeCutoff_zero hε hε.le, initialTimeCutoff_one hε (by linarith)]
  simp

/-- The initial transition kernel recovers a strong right trace of an integrable function. -/
theorem tendsto_integral_deriv_initialTimeCutoff_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ → E} {a : E} (hF : IntegrableOn F (Ioi 0))
    (hlim : Tendsto F (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun ε : ℝ ↦ ∫ t : ℝ in Ioi 0, deriv (initialTimeCutoff ε) t • F t)
      (𝓝[>] 0) (𝓝 a) := by
  apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    measurableSet_Ioi measurableSet_Ioc Ioc_subset_Ioi_self
    (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one))
    (by simp)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact fun t _ ↦ deriv_initialTimeCutoff_nonneg hε t
  · intro U hU hzero
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 hzero
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro δ hδ
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < r / 2 from half_pos hr))] with ε hε hε'
    intro t ht
    have ht' : t ∉ Icc ε (2 * ε) := by
      intro hmem
      apply ht.2
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
      linarith [hmem.2, show ε < r / 2 from hε']
    simpa [deriv_initialTimeCutoff_eq_zero hε ht'] using hδ
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 from by norm_num))] with ε hε hε'
    exact (setIntegral_deriv_initialTimeCutoff hε hε'.le).symm
  · filter_upwards with ε
    exact (continuous_deriv_initialTimeCutoff ε).aestronglyMeasurable
  · exact hF
  · exact hlim

/-- The initial time transition takes values in the unit interval. -/
theorem norm_initialTimeCutoff_le (ε t : ℝ) :
    ‖initialTimeCutoff ε t‖ ≤ 1 := by
  unfold initialTimeCutoff
  rw [Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _


end PDE.Analysis
