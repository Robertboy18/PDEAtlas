/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.MixedSections.CompactSupport
public import PDE.Analysis.MeasureTheory.Lp.MixedSections.Indicator
public import PDE.Common.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Real forcing as complex Bochner sections

A continuous real field with common compact support on a finite interval has
full and sharply restricted complex L1L2 representatives. The restricted
representative has exactly the integral of the actual restricted spatial norms.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace PDE PDE.Common
open scoped ENNReal

namespace MeasureTheory

/-- Continuous real forcing of common compact support has full and sharply restricted
complex Bochner representatives with exactly the physical restricted L1L2 norm. -/
theorem exists_complex_L1_L2_sections_indicator
    {n : ℕ} {a b : ℝ} {F : ℝ × ℝ^n → ℝ} {K : Set (ℝ^n)}
    (hK : IsCompact K) (hF : ContinuousOn F (Icc a b ×ˢ univ))
    (hzero : ∀ t ∈ Icc a b, ∀ x, x ∉ K → F (t, x) = 0)
    {S : Set (ℝ × ℝ^n)} (hS : MeasurableSet S) :
    ∃ f k : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc a b)),
      (∀ᵐ t ∂volume.restrict (Icc a b),
        (f t : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (F (t, x) : ℂ)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        (k t : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ ((S.indicator F (t, x) : ℝ) : ℂ)) ∧
      ‖k‖ = ∫ t in Icc a b, lpNorm (fun x ↦ F (t, x)) 2
        (volume.restrict {x | (t, x) ∈ S}) := by
  classical
  have : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  let C : Set (ℝ × ℝ^n) := Icc a b ×ˢ univ
  have hC : MeasurableSet C := measurableSet_Icc.prod MeasurableSet.univ
  let V : ℝ × ℝ^n → ℂ := fun z ↦ (F z : ℂ)
  have hV : ContinuousOn V C := Complex.continuous_ofReal.comp_continuousOn hF
  obtain ⟨f, hf, _⟩ := exists_L1_L2_sections_of_continuousOn_compact_support
    (ν := (volume : Measure (ℝ^n))) hK
    (hV.mono (prod_mono_right (subset_univ K)))
    (fun t ht x hx ↦ by simp only [V, hzero t ht x hx, Complex.ofReal_zero])
  let U := C.indicator V
  have hU : Measurable U := by
    simpa only [piecewise_eq_indicator] using
      hV.measurable_piecewise continuous_zero.continuousOn hC
  have hUeq (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ^n) : U (t, x) = V (t, x) :=
    indicator_of_mem (show (t, x) ∈ C from ⟨ht, mem_univ x⟩) V
  have hUf : ∀ᵐ t ∂volume.restrict (Icc a b),
      (fun x ↦ U (t, x)) =ᵐ[volume] (f t : ℝ^n → ℂ) := by
    filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with t ht htab
    filter_upwards [ht] with x hx
    exact (hUeq t htab x).trans hx
  obtain ⟨k, hk, hknorm⟩ := exists_L1_sections_indicator (by norm_num) f hU hUf hS
  refine ⟨f, k, hf.mono (fun _ ht ↦ ht.symm), ?_, ?_⟩
  · filter_upwards [hk, ae_restrict_mem measurableSet_Icc] with t ht htab
    filter_upwards [ht] with x hx
    rw [← hx]
    by_cases hxS : (t, x) ∈ S
    · simp only [indicator_of_mem hxS, hUeq t htab x, V]
    · simp only [indicator_of_notMem hxS, Complex.ofReal_zero]
  · rw [hknorm]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hc : Continuous (fun x ↦ F (t, x)) :=
      hF.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x ↦ ⟨ht, mem_univ x⟩)
    unfold lpNorm
    congr 1
    apply eLpNorm_congr_norm_ae
      ((Complex.continuous_ofReal.comp hc).aestronglyMeasurable.congr
        (Eventually.of_forall fun x ↦ (hUeq t ht x).symm))
      hc.aestronglyMeasurable
    filter_upwards with x
    rw [hUeq t ht x]
    exact Complex.norm_real _

end MeasureTheory
