/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Height integrals for compactly supported dilations

A positive displacement imposes a positive lower bound on height. Integrating the
resulting power tail gives the fractional kernel. At zero displacement, cancellation
must be used before integrating the singular height weight.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

/-- The positive power tail as an extended nonnegative integral. -/
theorem lintegral_Ioi_ofReal_rpow_neg {q c : ℝ} (hq : 0 < q) (hc : 0 < c) :
    (∫⁻ t in Ioi c, ENNReal.ofReal (t ^ (-(q + 1)))) =
      ENNReal.ofReal (c ^ (-q) / q) := by
  have ha : -(q + 1) < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt ha hc)]
  · rw [integral_Ioi_rpow_of_lt ha hc, show -(q + 1) + 1 = -q by ring]
    congr 1
    exact neg_div_neg_eq _ _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hc.le.trans (mem_Ioi.mp ht).le) _

/-- Cancellation at radius zero permits integrating the singular height weight. -/
theorem lintegral_Ioi_indicator_mul_rpow_eq {q R r : ℝ}
    (hq : 0 < q) (hR : 0 < R) (hr : 0 ≤ r) (a : ℝ≥0∞) (ha : r = 0 → a = 0) :
    (∫⁻ t in Ioi (0 : ℝ),
      if r < R * t then ENNReal.ofReal (t ^ (-(q + 1))) * a else 0) =
      ENNReal.ofReal (R ^ q / q) * (ENNReal.ofReal (r ^ (-q)) * a) := by
  classical
  rcases hr.eq_or_lt with hr | hr
  · simp [ha hr.symm]
  have hc : 0 < r / R := div_pos hr hR
  have hset : Ioi (r / R) ∩ Ioi (0 : ℝ) = Ioi (r / R) :=
    inter_eq_left.mpr (Ioi_subset_Ioi hc.le)
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ),
        (Ioi (r / R)).indicator
          (fun t ↦ ENNReal.ofReal (t ^ (-(q + 1))) * a) t := by
      apply lintegral_congr
      intro t
      simp only [indicator_apply, mem_Ioi, div_lt_iff₀ hR, mul_comm t R]
    _ = ∫⁻ t in Ioi (r / R), ENNReal.ofReal (t ^ (-(q + 1))) * a := by
      rw [setLIntegral_indicator measurableSet_Ioi, hset]
    _ = ENNReal.ofReal ((r / R) ^ (-q) / q) * a := by
      rw [lintegral_mul_const _ (by fun_prop), lintegral_Ioi_ofReal_rpow_neg hq hc]
    _ = _ := by
      have heq : (r / R) ^ (-q) / q = R ^ q / q * r ^ (-q) := by
        rw [Real.div_rpow hr.le hR.le, Real.rpow_neg hR.le, div_inv_eq_mul]
        ring
      rw [heq, ENNReal.ofReal_mul (by positivity), mul_assoc]

/-- Integrating expanding balls over positive heights produces a fractional radial weight. -/
theorem lintegral_height_ball_eq
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [SFinite μ] {q R : ℝ} (hq : 0 < q) (hR : 0 < R)
    {f : E → ℝ≥0∞} (hf : Measurable f) (hf0 : f 0 = 0) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ h in Metric.ball (0 : E) (R * t),
      ENNReal.ofReal (t ^ (-(q + 1))) * f h ∂μ) =
      ENNReal.ofReal (R ^ q / q) *
        ∫⁻ h, ENNReal.ofReal (‖h‖ ^ (-q)) * f h ∂μ := by
  classical
  have hm : Measurable fun z : ℝ × E ↦
      if ‖z.2‖ < R * z.1 then ENNReal.ofReal (z.1 ^ (-(q + 1))) * f z.2 else 0 := by
    apply Measurable.ite
    · exact (isOpen_lt continuous_snd.norm (continuous_const.mul continuous_fst)).measurableSet
    · exact (by fun_prop : Measurable fun z : ℝ × E ↦
        ENNReal.ofReal (z.1 ^ (-(q + 1)))).mul (hf.comp measurable_snd)
    · exact measurable_const
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ h,
        (if ‖h‖ < R * t then ENNReal.ofReal (t ^ (-(q + 1))) * f h else 0) ∂μ := by
      apply lintegral_congr
      intro t
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro h
      simp only [indicator_apply, Metric.mem_ball, dist_zero_right]
    _ = ∫⁻ h, (∫⁻ t in Ioi (0 : ℝ),
        if ‖h‖ < R * t then ENNReal.ofReal (t ^ (-(q + 1))) * f h else 0) ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ h, ENNReal.ofReal (R ^ q / q) *
        (ENNReal.ofReal (‖h‖ ^ (-q)) * f h) ∂μ := by
      apply lintegral_congr
      intro h
      exact lintegral_Ioi_indicator_mul_rpow_eq hq hR (norm_nonneg h) (f h)
        (fun hh ↦ (norm_eq_zero.mp hh) ▸ hf0)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end MeasureTheory
