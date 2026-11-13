/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.Slicing.Normal
public import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral
public import PDE.Spaces.Sobolev.Inequalities.Hardy.NormalIncrement
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrated Hardy control of normal increments

Integrating Hardy's normal-increment estimate over tangential slices bounds the weighted
increment by the upper half-space normal partial energy, with constant `(p / (p - 1)) ^ p`.
The nonnegative integral estimate establishes finiteness before passing to real integrals.
The function may take values in any real Banach space.
-/

@[expose] public section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]
  {f : ℝ^(n + 1) → F}

/-- The weighted normal increment is jointly measurable in tangential and normal coordinates. -/
theorem measurable_normal_increment (hf : Continuous f) (p : ℝ) :
    Measurable (fun z : ℝ^n × ℝ ↦
      ‖normalSlice f z.1 z.2 - normalSlice f z.1 0‖ ^ p * z.2 ^ (-p)) := by
  have hslice := normalSlice_product_continuous hf
  have hboundary : Continuous (fun z : ℝ^n × ℝ ↦ normalSlice f z.1 0) :=
    hslice.comp (continuous_fst.prodMk continuous_const)
  exact (hslice.sub hboundary).norm.measurable.pow_const p
      |>.mul (measurable_snd.pow_const (-p))

/-- Integrating the nonnegative weighted increment in the normal variable gives a measurable
function of the tangential coordinate. -/
theorem measurable_lintegral_normal_increment (hf : Continuous f) (p : ℝ) :
    Measurable (fun y : ℝ^n ↦ ∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (‖normalSlice f y t - normalSlice f y 0‖ ^ p * t ^ (-p))) :=
  (ENNReal.measurable_ofReal.comp (measurable_normal_increment hf p)).lintegral_prod_right'

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- The iterated nonnegative integral of the weighted normal increment is finite and controlled
by the physical normal partial derivative on the upper half-space. -/
theorem lintegral_normal_increment_le {p : ℝ} (hp : 1 < p) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    (∫⁻ y : ℝ^n, ∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (‖normalSlice f y t - normalSlice f y 0‖ ^ p * t ^ (-p))) ≤
        ENNReal.ofReal ((p / (p - 1)) ^ p *
          ∫ x in ℝ^(n + 1)₊, ‖(∂[Fin.last n] f) x‖ ^ p) := by
  have henergy : Integrable (fun z : ℝ^n × ℝ ↦ ‖normalDerivativeInSplit f z‖ ^ p)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
    (normalDerivativeInSplit_continuous hf).norm.rpow_const
      (fun _ ↦ Or.inr (zero_lt_one.trans hp).le)
      |>.integrable_of_hasCompactSupport
        ((normalDerivativeInSplit_hasCompactSupport hfc).norm.rpow_const
          (zero_lt_one.trans hp).ne')
  have hslice (y : ℝ^n) :
      (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (‖normalSlice f y t - normalSlice f y 0‖ ^ p * t ^ (-p))) ≤
          ENNReal.ofReal ((p / (p - 1)) ^ p *
            ∫ t, ‖normalDerivativeInSplit f (y, t)‖ ^ p ∂positiveNormalMeasure) := by
    simpa only [deriv_normalSlice hf y] using
      Hardy.lintegral_normal_increment_le hp
        (normalSlice_contDiff hf y) (normalSlice_hasCompactSupport hfc y)
  calc
    _ ≤ ∫⁻ y : ℝ^n, ENNReal.ofReal ((p / (p - 1)) ^ p *
        ∫ t, ‖normalDerivativeInSplit f (y, t)‖ ^ p ∂positiveNormalMeasure) :=
      lintegral_mono hslice
    _ = ENNReal.ofReal (∫ y : ℝ^n, (p / (p - 1)) ^ p *
        ∫ t, ‖normalDerivativeInSplit f (y, t)‖ ^ p ∂positiveNormalMeasure) :=
      (ofReal_integral_eq_lintegral_ofReal
        (henergy.integral_prod_left.const_mul _) (ae_of_all _ fun y ↦
          mul_nonneg (by positivity)
            (integral_nonneg fun t ↦ Real.rpow_nonneg (norm_nonneg _) _))).symm
    _ = ENNReal.ofReal ((p / (p - 1)) ^ p *
        ∫ z, ‖normalDerivativeInSplit f z‖ ^ p
          ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) := by
      rw [integral_const_mul, ← integral_prod _ henergy]
    _ = _ := by
      congr 1
      congr 1
      exact integral_joinTangentialNormal_eq_integral_upper
        (fun x ↦ ‖(∂[Fin.last n] f) x‖ ^ p)

/-- The weighted normal increment is integrable for tangential volume times positive normal
volume, including at the boundary and at infinity. -/
theorem integrable_normal_increment {p : ℝ} (hp : 1 < p) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    Integrable (fun z : ℝ^n × ℝ ↦
      ‖normalSlice f z.1 z.2 - normalSlice f z.1 0‖ ^ p * z.2 ^ (-p))
        ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) := by
  have hmeas := measurable_normal_increment hf.continuous p
  have hnonneg :
      0 ≤ᵐ[(volume : Measure (ℝ^n)).prod positiveNormalMeasure] fun z : ℝ^n × ℝ ↦
        ‖normalSlice f z.1 z.2 - normalSlice f z.1 0‖ ^ p * z.2 ^ (-p) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem measurableSet_Ioi)] with z hz
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hz.le _)
  apply (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable hnonneg).1
  rw [lintegral_prod (μ := volume) (ν := positiveNormalMeasure)
    (fun z : ℝ^n × ℝ ↦ ENNReal.ofReal
      (‖normalSlice f z.1 z.2 - normalSlice f z.1 0‖ ^ p * z.2 ^ (-p)))
    (ENNReal.measurable_ofReal.comp hmeas).aemeasurable]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_normal_increment_le hp hf hfc)

/-- The normal integral of the weighted increment is integrable in the tangential variable. -/
theorem integrable_integral_normal_increment {p : ℝ} (hp : 1 < p)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    Integrable (fun y : ℝ^n ↦
      ∫ t in Ioi (0 : ℝ), ‖normalSlice f y t - normalSlice f y 0‖ ^ p * t ^ (-p)) :=
  (integrable_normal_increment hp hf hfc).integral_prod_left

/-- The iterated real integral of the weighted normal increment is bounded by the upper
normal partial energy with Hardy's constant. -/
theorem integral_normal_increment_le {p : ℝ} (hp : 1 < p) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    (∫ y : ℝ^n, ∫ t in Ioi (0 : ℝ),
      ‖normalSlice f y t - normalSlice f y 0‖ ^ p * t ^ (-p)) ≤
        (p / (p - 1)) ^ p * ∫ x in ℝ^(n + 1)₊, ‖(∂[Fin.last n] f) x‖ ^ p := by
  have hslice (y : ℝ^n) :
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ),
        ‖normalSlice f y t - normalSlice f y 0‖ ^ p * t ^ (-p)) =
          ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (‖normalSlice f y t - normalSlice f y 0‖ ^ p * t ^ (-p)) := by
    apply ofReal_integral_eq_lintegral_ofReal
      (Hardy.integrableOn_normal_increment hp
        (normalSlice_contDiff hf y) (normalSlice_hasCompactSupport hfc y))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg ht.le _)
  have hnonneg (y : ℝ^n) :
      0 ≤ ∫ t in Ioi (0 : ℝ),
        ‖normalSlice f y t - normalSlice f y 0‖ ^ p * t ^ (-p) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg ht.le _)
  have hbound := lintegral_normal_increment_le hp hf hfc
  simp_rw [← hslice] at hbound
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_integral_normal_increment hp hf hfc) (ae_of_all _ hnonneg)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity)
      (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _))).1 hbound

end SobolevSpace.Trace.HalfSpace
