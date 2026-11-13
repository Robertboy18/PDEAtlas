/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrability from nonnegative integral bounds

Fatou's lemma passes eventual uniform integral bounds to almost-everywhere
limits. Increasing spatial exhaustions pass a common local bound to the whole
space. Both statements prove integrability of the limiting density.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- A uniform eventual bound for nonnegative integrable functions proves
integrability and the same bound for their almost-everywhere limit. The measure
space is arbitrary, including infinite-volume spatial domains. -/
theorem integrable_and_integral_le_of_nonnegative_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {G : α → ℝ} {C : ℝ}
    (hF : ∀ i, Integrable (F i) μ)
    (hpos : ∀ i, ∀ᵐ x ∂μ, 0 ≤ F i x)
    (hb : ∀ᶠ i in atTop, (∫ x, F i x ∂μ) ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) atTop (𝓝 (G x))) :
    Integrable G μ ∧ (∫ x, G x ∂μ) ≤ C := by
  have hnorm (i : ℕ) : (∫ x, ‖F i x‖ ∂μ) = ∫ x, F i x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hpos i] with x hx
    exact Real.norm_of_nonneg hx
  have hb' : ∀ᶠ i in atTop, (∫⁻ x, ‖F i x‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    filter_upwards [hb] with i hi
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF i), hnorm i]
    exact ENNReal.ofReal_le_ofReal hi
  have hinf : liminf (fun i ↦ ∫⁻ x, ‖F i x‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C :=
    liminf_le_of_frequently_le hb'.frequently
  have hfatou : (∫⁻ x, ‖G x‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, liminf (fun i ↦ ‖F i x‖ₑ) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact hx.enorm.liminf_eq.symm
      _ ≤ liminf (fun i ↦ ∫⁻ x, ‖F i x‖ₑ ∂μ) atTop :=
        lintegral_liminf_le' (fun i ↦ (hF i).aestronglyMeasurable.enorm)
      _ ≤ _ := hinf
  have hG : Integrable G μ :=
    ⟨aestronglyMeasurable_of_tendsto_ae _ (fun i ↦ (hF i).aestronglyMeasurable) hlim,
      hfatou.trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨i, hi⟩ := hb.exists
  have hC : 0 ≤ C := (integral_nonneg_of_ae (hpos i)).trans hi
  rw [← ofReal_integral_norm_eq_lintegral_enorm hG] at hfatou
  have hnormG : (∫ x, ‖G x‖ ∂μ) ≤ C := by
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
      ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hfatou
  exact ⟨hG, (le_abs_self _).trans ((norm_integral_le_integral_norm _).trans hnormG)⟩

/-- A common bound on an increasing measurable exhaustion proves global
integrability of a nonnegative density, including on infinite-volume spaces. -/
theorem integrable_and_integral_le_of_exhaustion
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : ℕ → Set α} (hs : Monotone s) (hsU : (⋃ i, s i) = univ)
    {F : α → ℝ} {C : ℝ} (hF : AEStronglyMeasurable F μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ F x)
    (hlocal : ∀ i, Integrable F (μ.restrict (s i)))
    (hb : ∀ i, (∫ x in s i, F x ∂μ) ≤ C) :
    Integrable F μ ∧ (∫ x, F x ∂μ) ≤ C := by
  have hlocalnorm (i : ℕ) : (∫ x in s i, ‖F x‖ ∂μ) = ∫ x in s i, F x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hpos.filter_mono (ae_mono Measure.restrict_le_self)] with x hx
    exact Real.norm_of_nonneg hx
  have hlin : (∫⁻ x, ‖F x‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    rw [← Measure.restrict_univ (μ := μ), ← hsU,
      setLIntegral_iUnion_of_directed _ hs.directed_le]
    apply iSup_le
    intro i
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hlocal i), hlocalnorm i]
    exact ENNReal.ofReal_le_ofReal (hb i)
  have hFi : Integrable F μ := ⟨hF, hlin.trans_lt ENNReal.ofReal_lt_top⟩
  have hC : 0 ≤ C :=
    (integral_nonneg_of_ae (hpos.filter_mono (ae_mono Measure.restrict_le_self))).trans (hb 0)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hFi] at hlin
  have hnorm : (∫ x, ‖F x‖ ∂μ) ≤ C := by
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
      ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  exact ⟨hFi, (le_abs_self _).trans ((norm_integral_le_integral_norm _).trans hnorm)⟩

end MeasureTheory
