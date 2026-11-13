/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.IntervalL2

/-!
# Restricting circle `L²` convergence to the interval

The covering map identifies a fundamental interval with the Fourier circle.
Changing the normalization of measure and restricting to `(0, 1]` are bounded
linear operations. This gives an interval norm interpretation of circle limits.
-/

@[expose] public section

namespace PDE.Analysis.Fourier.SineSeries

open MeasureTheory MeasureTheory.Lp Set AddCircle
open scoped ENNReal

/-- The standard circle volume is twice normalized Haar measure. -/
theorem circle_volume_le_two_haar :
    (volume : Measure (AddCircle (2 : ℝ))) ≤ (2 : ℝ≥0∞) • haarAddCircle := by
  rw [volume_eq_smul_haarAddCircle]
  norm_num

/-- The positive half interval carries a restriction of fundamental-interval measure. -/
theorem interval_volume_le_fundamental :
    volume.restrict (Ioc (0 : ℝ) 1) ≤
      (1 : ℝ≥0∞) • volume.restrict (Ioc (-1 : ℝ) (-1 + 2)) := by
  rw [one_smul]
  apply Measure.restrict_mono_set
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Restriction from circle `L²` to the positive unit interval is a bounded real
linear map. Its target uses ordinary, unnormalized Lebesgue measure. -/
noncomputable def circleIntervalRestriction :
    Lp ℂ 2 (haarAddCircle (T := (2 : ℝ))) →L[ℝ]
      Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    interval_volume_le_fundamental).comp
    ((Lp.compMeasurePreservingₗᵢ ℝ _
      (AddCircle.measurePreserving_mk (2 : ℝ) (-1))).toContinuousLinearMap.comp
        (LpToLpOfMeasureLeSMul (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
          circle_volume_le_two_haar))

/-- Restriction agrees almost everywhere with evaluation on real representatives. -/
theorem circleIntervalRestriction_coe (f : Lp ℂ 2 (haarAddCircle (T := (2 : ℝ)))) :
    circleIntervalRestriction f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x ↦ f (x : AddCircle (2 : ℝ)) := by
  let F := LpToLpOfMeasureLeSMul (E := ℂ) (p := 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) circle_volume_le_two_haar f
  have hF : F =ᵐ[volume] f := coeFn_LpToLpOfMeasureLeSMul _ _ _
  have hp := AddCircle.measurePreserving_mk (2 : ℝ) (-1)
  have hcomp := (Lp.coeFn_compMeasurePreserving F hp).trans
    (hp.quasiMeasurePreserving.ae_eq_comp hF)
  have hr : Lp.compMeasurePreserving _ hp F =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x ↦ f (x : AddCircle (2 : ℝ)) :=
    hcomp.filter_mono (ae_mono (by simpa only [one_smul]
      using interval_volume_le_fundamental))
  exact (coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    interval_volume_le_fundamental _).trans hr

/-- Equality almost everywhere on the Fourier circle pulls back to the interval. -/
theorem ae_interval_coe_of_ae_circle {F G : AddCircle (2 : ℝ) → ℂ}
    (h : F =ᵐ[haarAddCircle] G) :
    (fun x : ℝ ↦ F (x : AddCircle (2 : ℝ))) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x ↦ G (x : AddCircle (2 : ℝ)) := by
  have hv : F =ᵐ[volume] G :=
    (Measure.absolutelyContinuous_of_le_smul circle_volume_le_two_haar).ae_eq h
  exact ((AddCircle.measurePreserving_mk (2 : ℝ) (-1)).quasiMeasurePreserving.ae_eq_comp
    hv).filter_mono (ae_mono (by simpa only [one_smul]
      using interval_volume_le_fundamental))

/-- Restricting the odd extension recovers the original interval `L²` data. -/
theorem circleIntervalRestriction_oddIntervalL2 {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    circleIntervalRestriction (oddIntervalL2 g hg) = hg.ofReal.toLp (fun x ↦ (g x : ℂ)) := by
  apply Lp.ext
  have hg' : MemLp (fun x ↦ (g x : ℂ)) 2 (volume.restrict (Ioc 0 1)) := hg.ofReal
  filter_upwards [circleIntervalRestriction_coe (oddIntervalL2 g hg),
    ae_interval_coe_of_ae_circle (memLp_oddIntervalFunction hg).coeFn_toLp,
    hg'.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with x hx hodd hgx hmem
  rw [hx]
  dsimp only [oddIntervalL2]
  rw [hodd, hgx]
  change liftIoc 2 (-1) (fun y ↦ (oddZeroExtension g y : ℂ))
    (x : AddCircle (2 : ℝ)) = _
  rw [liftIoc_coe_apply (show x ∈ Ioc (-1 : ℝ) (-1 + 2) from
    ⟨by linarith [hmem.1], by linarith [hmem.2]⟩), oddZeroExtension_of_mem hmem]

end PDE.Analysis.Fourier.SineSeries
