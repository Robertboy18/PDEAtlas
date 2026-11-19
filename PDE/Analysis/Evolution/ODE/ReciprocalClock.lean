/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.AmplitudeClock

/-!
# The reciprocal-amplitude clock

Let `sU' = -cU sU` on `[0, ∞)` with `sU(0) > 0` and `cU ≤ -γ`. Then
`sU(t) ≥ sU(0) e^{γ t}`, so `1/sU(t) ≤ e^{-γ t}/sU(0)`. For `γ > 0` the reciprocal
is integrable on `(0, ∞)`, and the clock `t ↦ ∫₀ᵗ 1/sU` is continuous and strictly
increasing, maps `[0, ∞)` onto `[0, T)` with `T = ∫₀^∞ 1/sU`, and satisfies
`T - ∫₀ᵗ 1/sU ≤ e^{-γ t}/(γ sU(0))`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE.Analysis.Evolution.ODE

variable (sU cU : ℝ → ℝ) (gamma : ℝ)
  (hsU0 : 0 < sU 0)
  (hscale : ∀ x ∈ Ici (0 : ℝ), HasDerivAt sU (-cU x * sU x) x)
  (hrate : ∀ x ∈ Ici (0 : ℝ), cU x ≤ -gamma)

include hsU0 hscale hrate

/-- The reciprocal amplitude is dominated by the explicit decaying exponential. -/
theorem reciprocal_amplitude_le_exp {t : ℝ} (ht : 0 ≤ t) :
    (sU t)⁻¹ ≤ (sU 0)⁻¹ * Real.exp (-gamma * t) := by
  have hlower := amplitude_scale_lower_bound sU cU gamma t ht hscale
    (fun x hx ↦ (amplitude_scale_pos sU cU gamma hsU0 hscale hrate hx).le) hrate
  have hpos := amplitude_scale_pos sU cU gamma hsU0 hscale hrate ht
  calc
    (sU t)⁻¹ ≤ (sU 0 * Real.exp (gamma * t))⁻¹ :=
      (inv_le_inv₀ hpos (mul_pos hsU0 (Real.exp_pos _))).mpr hlower
    _ = (sU 0)⁻¹ * Real.exp (-gamma * t) := by
      simp only [mul_inv, ← Real.exp_neg, neg_mul]

/-- For `γ > 0` the reciprocal amplitude is integrable on `(0, ∞)`, so the total
physical lifetime is finite. -/
theorem integrableOn_reciprocal_amplitude (hgamma : 0 < gamma) :
    IntegrableOn (fun t ↦ (sU t)⁻¹) (Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn (fun t ↦ (sU t)⁻¹) (Ioi (0 : ℝ)) := by
    intro t ht
    exact ((hscale t (Ioi_subset_Ici_self ht)).continuousAt.inv₀
      (amplitude_scale_pos sU cU gamma hsU0 hscale hrate ht.le).ne').continuousWithinAt
  have hexp : IntegrableOn (fun t : ℝ ↦ (sU 0)⁻¹ * Real.exp (-gamma * t))
      (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hgamma) 0).const_mul _
  apply hexp.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
    (amplitude_scale_pos sU cU gamma hsU0 hscale hrate ht.le))]
  exact reciprocal_amplitude_le_exp sU cU gamma hsU0 hscale hrate ht.le

/-- Integrating the exponential bound on the reciprocal amplitude bounds the remaining
physical time. -/
theorem reciprocal_amplitude_tail_le (hgamma : 0 < gamma) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Ioi t, (sU s)⁻¹) ≤ (sU 0)⁻¹ * Real.exp (-gamma * t) / gamma := by
  apply physical_clock_tail_le (fun s ↦ (sU s)⁻¹) ((sU 0)⁻¹) gamma t hgamma
  · exact (integrableOn_reciprocal_amplitude sU cU gamma hsU0 hscale
      hrate hgamma).mono_set (Ioi_subset_Ioi ht)
  · intro s hs
    have hs0 : 0 ≤ s := ht.trans hs.le
    exact ⟨(inv_pos.mpr (amplitude_scale_pos sU cU gamma hsU0 hscale hrate hs0)).le,
      reciprocal_amplitude_le_exp sU cU gamma hsU0 hscale hrate hs0⟩

/-- Every finite rescaled time leaves a strictly positive amount of physical time. -/
theorem reciprocal_amplitude_tail_pos (hgamma : 0 < gamma) {t : ℝ} (ht : 0 ≤ t) :
    0 < ∫ s in Ioi t, (sU s)⁻¹ := by
  have hint : IntegrableOn (fun s ↦ (sU s)⁻¹) (Ioi t) :=
    (integrableOn_reciprocal_amplitude sU cU gamma hsU0 hscale
      hrate hgamma).mono_set (Ioi_subset_Ioi ht)
  have hnonneg : ∀ᵐ s ∂volume.restrict (Ioi t), 0 ≤ (sU s)⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact (inv_pos.mpr
      (amplitude_scale_pos sU cU gamma hsU0 hscale hrate (ht.trans hs.le))).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint).mpr
  have hsupp : Function.support (fun s ↦ (sU s)⁻¹) ∩ Ioi t = Ioi t := by
    apply inter_eq_right.mpr
    intro s hs
    exact (inv_pos.mpr
      (amplitude_scale_pos sU cU gamma hsU0 hscale hrate
        (ht.trans hs.le))).ne'
  rw [hsupp]
  simp

/-- The difference between the lifetime and the accumulated clock obeys the
exponential reconstruction estimate, with integrability derived from the ODE. -/
theorem lifetime_sub_reciprocal_clock_le (hgamma : 0 < gamma) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Ioi (0 : ℝ), (sU s)⁻¹) - (∫ s in (0 : ℝ)..t, (sU s)⁻¹) ≤
      (sU 0)⁻¹ * Real.exp (-gamma * t) / gamma := by
  have hint := integrableOn_reciprocal_amplitude sU cU gamma hsU0 hscale
    hrate hgamma
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hint ht, sub_sub_cancel]
  exact reciprocal_amplitude_tail_le sU cU gamma hsU0 hscale hrate
    hgamma ht

/-- The accumulated reciprocal clock is strictly below its total lifetime. -/
theorem reciprocal_clock_lt_lifetime (hgamma : 0 < gamma) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, (sU s)⁻¹) < ∫ s in Ioi (0 : ℝ), (sU s)⁻¹ := by
  have hint := integrableOn_reciprocal_amplitude sU cU gamma hsU0 hscale
    hrate hgamma
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hint ht]
  exact sub_lt_self _ (reciprocal_amplitude_tail_pos sU cU gamma hsU0 hscale
    hrate hgamma ht)

/-- The scale ODE gives continuity of the reciprocal on the forward time domain. -/
private theorem continuousOn_reciprocal_scale :
    ContinuousOn (fun t ↦ (sU t)⁻¹) (Ici (0 : ℝ)) := by
  intro t ht
  have hcont := (hscale t ht).continuousAt.inv₀
    (amplitude_scale_pos sU cU gamma hsU0 hscale hrate ht).ne'
  exact hcont.continuousWithinAt

/-- A positive clock rate makes accumulated physical time continuous and strictly increasing. -/
theorem reciprocal_clock_continuous_strictMono :
    ContinuousOn (fun t ↦ ∫ s in (0 : ℝ)..t, (sU s)⁻¹) (Ici (0 : ℝ)) ∧
      StrictMonoOn (fun t ↦ ∫ s in (0 : ℝ)..t, (sU s)⁻¹) (Ici (0 : ℝ)) := by
  -- Extending the rate constantly before zero lets us use the FTC.
  -- Every integral below samples only nonnegative rescaled times.
  let rate := fun t : ℝ ↦ (sU (max t 0))⁻¹
  have hrateCont :=
    continuousOn_reciprocal_scale sU cU gamma hsU0 hscale hrate
  have hcont : Continuous rate := hrateCont.comp_continuous
    (continuous_id.max continuous_const) (by
      intro x
      change 0 ≤ max x 0
      exact le_max_right x 0)
  have heq : EqOn (fun t ↦ ∫ s in (0 : ℝ)..t, (sU s)⁻¹)
      (fun t ↦ ∫ s in (0 : ℝ)..t, rate s) (Ici (0 : ℝ)) := by
    intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    simp only [rate, max_eq_left hs.1]
  have hmono := PDE.Analysis.Evolution.ODE.strictMonoOn_physicalTimeIntegral rate hcont
    (fun t _ ↦ inv_pos.mpr (amplitude_scale_pos sU cU gamma hsU0 hscale
      hrate (le_max_right t 0)))
  refine ⟨?_, ?_⟩
  · have hc : Continuous (fun t ↦ ∫ s in (0 : ℝ)..t, rate s) :=
      (intervalIntegral.differentiable_integral_of_continuous hcont).continuous
    exact hc.continuousOn.congr heq
  · intro a ha b hb hab
    rw [heq ha, heq hb]
    exact hmono ha hb hab

/-- The reciprocal clock covers every physical time in `[0,T)`. The scale ODE
is only needed on the forward rescaled-time domain. -/
theorem image_reciprocal_clock_Ici (hgamma : 0 < gamma) :
    (fun t ↦ ∫ s in (0 : ℝ)..t, (sU s)⁻¹) '' Ici (0 : ℝ) =
      Ico 0 (∫ s in Ioi (0 : ℝ), (sU s)⁻¹) := by
  obtain ⟨hcont, hmono⟩ :=
    reciprocal_clock_continuous_strictMono sU cU gamma hsU0 hscale hrate
  simpa using PDE.Analysis.Evolution.ODE.image_Ici_eq_Ico_of_strictMonoOn_tendsto
    (fun t ↦ ∫ s in (0 : ℝ)..t, (sU s)⁻¹) 0 (∫ s in Ioi (0 : ℝ), (sU s)⁻¹)
    hcont hmono (MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_reciprocal_amplitude sU cU gamma hsU0 hscale hrate hgamma) tendsto_id)

end PDE.Analysis.Evolution.ODE
