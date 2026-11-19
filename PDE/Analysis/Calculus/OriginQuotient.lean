/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Integrable singular quotients from a vanishing first jet

A function with zero value and derivative at the origin is quadratically small
there if it is locally C². Two applications of the mean value theorem give this
bound. Compact support and continuity then control the quotient everywhere else.

For perturbations with a fixed origin slope, this supplies the L² hypothesis
on `f / x²` used in the singular Hilbert cancellation. Smoothness is needed
only near the origin, so corners at the support endpoints are allowed.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace PDE.Analysis.Calculus

/-- A zero first jet and local C² regularity give a quadratic bound near zero. -/
theorem exists_norm_le_mul_sq_of_contDiffAt
    {f : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (hzero : f 0 = 0) (hderivzero : deriv f 0 = 0) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ x, |x| < δ → ‖f x‖ ≤ C * x ^ 2 := by
  have hd : ContDiffAt ℝ 1 (deriv f) 0 :=
    hf.derivWithin (by norm_num)
  have hdd : ContinuousAt (deriv (deriv f)) 0 :=
    (hd.derivWithin (m := 0) (by norm_num)).continuousAt
  let C := ‖deriv (deriv f) 0‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᶠ y in 𝓝 (0 : ℝ), ‖deriv (deriv f) y‖ < C :=
    hdd.norm.tendsto.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp
    ((hf.eventually (by simp)).and hbound)
  have hlocal' (y : ℝ) (hy : |y| < δ) :
      ContDiffAt ℝ 2 f y ∧ ‖deriv (deriv f) y‖ ≤ C := by
    have h := hlocal (by simpa only [dist_zero_right, Real.norm_eq_abs] using hy)
    exact ⟨h.1, h.2.le⟩
  have hfirst (y : ℝ) (hy : |y| < δ) : ‖deriv f y‖ ≤ C * |y| := by
    have h := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz ↦ by
        have hz' := (hlocal' z (by simpa using hz)).1.derivWithin (m := 1) (by norm_num)
        exact (hz'.differentiableAt one_ne_zero).hasDerivAt.hasDerivWithinAt)
      (fun z hz ↦ (hlocal' z (by simpa using hz)).2)
      (Metric.mem_ball_self hδ)
      (show y ∈ Metric.ball 0 δ from by simpa using hy)
    simpa only [hderivzero, sub_zero, Real.norm_eq_abs] using h
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro x hx
  have hsmall (y : ℝ) (hy : y ∈ Icc (-|x|) |x|) : |y| < δ :=
    (abs_le.mpr hy).trans_lt hx
  have h := (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy ↦ by
      have hy' := (hlocal' y (hsmall y hy)).1.differentiableAt two_ne_zero
      exact hy'.hasDerivAt.hasDerivWithinAt)
    (fun y hy ↦ (hfirst y (hsmall y hy)).trans
      (mul_le_mul_of_nonneg_left (abs_le.mpr hy) hC))
    (show (0 : ℝ) ∈ Icc (-|x|) |x| from ⟨neg_nonpos.mpr (abs_nonneg _), abs_nonneg _⟩)
    (show x ∈ Icc (-|x|) |x| from ⟨neg_abs_le _, le_abs_self _⟩)
  simpa only [hzero, sub_zero, Real.norm_eq_abs, mul_assoc, ← pow_two, sq_abs] using h

/-- Compact continuous input with a vanishing first jet and local C² regularity
has its quadratic coordinate quotient in every Lᵖ space, including L∞. -/
theorem memLp_div_sq_of_contDiffAt
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hregular : ContDiffAt ℝ 2 f 0)
    (hzero : f 0 = 0) (hderivzero : deriv f 0 = 0) (p : ℝ≥0∞) :
    MemLp (fun x ↦ f x / x ^ 2) p volume := by
  obtain ⟨C, δ, hC, hδ, hlocal⟩ :=
    exists_norm_le_mul_sq_of_contDiffAt hregular hzero hderivzero
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hf
  have hMnonneg : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hsupport : HasCompactSupport (fun x ↦ f x / x ^ 2) := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      hc.mul_right (f' := fun x ↦ (x ^ 2)⁻¹)
  apply hsupport.memLp_of_bound
    (hf.measurable.div (measurable_id.pow_const 2)).aestronglyMeasurable
    (max C (M / δ ^ 2))
  apply Eventually.of_forall
  intro x
  by_cases hxzero : x = 0
  · simp only [hxzero, zero_pow (by decide : 2 ≠ 0), div_zero, norm_zero]
    exact hC.trans (le_max_left _ _)
  simp only [norm_div, norm_pow, Real.norm_eq_abs, sq_abs]
  by_cases hx : |x| < δ
  · exact ((div_le_iff₀ (sq_pos_of_ne_zero hxzero)).mpr (hlocal x hx)).trans
      (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    have hden : δ ^ 2 ≤ x ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ hδ.le (abs_nonneg x)).mpr (not_lt.mp hx)
    exact div_le_div₀ hMnonneg (hM x) (sq_pos_of_pos hδ) hden

/-- A vanishing first jet makes the cubic Hardy boundary flux tend to zero
from the right. Only C² regularity near the origin is needed. -/
theorem tendsto_origin_hardy_flux_of_contDiffAt
    {omega : ℝ → ℝ} (hregular : ContDiffAt ℝ 2 omega 0)
    (hzero : omega 0 = 0) (hderivzero : deriv omega 0 = 0) :
    Tendsto (fun x ↦ omega x ^ 2 / x ^ 3) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, δ, hC, hδ, hbound⟩ :=
    exists_norm_le_mul_sq_of_contDiffAt hregular hzero hderivzero
  have hsmall : ∀ᶠ x in 𝓝[>] (0 : ℝ), |x| < δ :=
    ((continuous_abs.tendsto (0 : ℝ)).eventually
      (gt_mem_nhds (by simpa only [abs_zero] using hδ))).filter_mono inf_le_left
  apply squeeze_zero'
    (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hx) _))
    ?_ (show Tendsto (fun x : ℝ ↦ C ^ 2 * x) (𝓝[>] 0) (𝓝 0) by
      have hid : Tendsto (fun x : ℝ ↦ x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left inf_le_left
      have ht : Tendsto (fun x : ℝ ↦ C ^ 2 * x) (𝓝[>] (0 : ℝ)) (𝓝 (C ^ 2 * 0)) :=
        hid.const_mul (C ^ 2)
      rwa [mul_zero] at ht)
  filter_upwards [hsmall, self_mem_nhdsWithin] with x hx hxpos
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (sq_nonneg x))).mpr (hbound x hx)
  rw [Real.norm_eq_abs, sq_abs] at hs
  apply (div_le_iff₀ (pow_pos hxpos 3)).mpr
  nlinarith

/-- A nonzero continuous origin trace would force a nonintegrable `1/x` singularity. -/
theorem eq_zero_of_continuousAt_integrable_div_id
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hf : ContinuousAt f 0)
    (hi : IntegrableOn (fun x ↦ f x / x) (Ioo 0 L)) : f 0 = 0 := by
  by_contra hn
  have hpos : 0 < ‖f 0‖ / 2 := by positivity
  have hlower : ∀ᶠ x in 𝓝[>] (0 : ℝ), ‖f 0‖ / 2 < ‖f x‖ :=
    (hf.norm.tendsto.eventually (lt_mem_nhds (by linarith [norm_pos_iff.mpr hn]))).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨b, hb, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hlower
  let d := min b L
  have hd : 0 < d := lt_min hb hL
  have hdL : Ioo (0 : ℝ) d ⊆ Ioo 0 L := Ioo_subset_Ioo le_rfl (min_le_right _ _)
  have hinv : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioo 0 d) := by
    apply ((hi.mono_set hdL).norm.const_mul (1 / (‖f 0‖ / 2))).mono'
      measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hfbound : ‖f 0‖ / 2 ≤ ‖f x‖ :=
      (hbound ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩).le
    calc
      ‖x⁻¹‖ = 1 / x := by simp [Real.norm_eq_abs, abs_of_pos hx.1]
      _ ≤ (‖f x‖ / (‖f 0‖ / 2)) / x :=
        div_le_div_of_nonneg_right ((le_div_iff₀ hpos).mpr (by simpa using hfbound)) hx.1.le
      _ = (1 / (‖f 0‖ / 2)) * ‖f x / x‖ := by
        rw [norm_div, Real.norm_eq_abs x, abs_of_pos hx.1]
        ring
  have hbad := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -1) hd).mp
    (by simpa only [Real.rpow_neg_one] using hinv)
  exact (lt_irrefl (-1 : ℝ)) hbad

end PDE.Analysis.Calculus
