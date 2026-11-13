/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.KernelIntegrability
public import PDE.Analysis.MeasureTheory.Lp.MixedSections
import PDE.Analysis.MeasureTheory.Integral.Minkowski
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Spacetime integration against the exterior Newtonian kernel

Spatial Young and the temporal half-order fractional-integral estimate bound the
spacetime kernel integral from L^(4/3) time/L^(12/11) space to L⁴ time/L¹² space.
Finite input mixed norm implies absolute integrability for almost every output point.
Fubini, addition, and representative independence therefore hold for the Bochner
integral itself. Mixed-section reconstruction supplies a nested Lp output class.

The kernel is the one identified with the zero-velocity wave propagator composed
with the Newtonian potential in `KirchhoffNewton`. The wave-energy TT* operator and
the homogeneous estimate are in `Strichartz.Homogeneous`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace WaveEquation.Strichartz

/-- Positive spacetime integration against the exterior Newtonian kernel. -/
noncomputable def spacetimeNewtonMajorant (F : ℝ × ℝ^3 → ℝ≥0∞) (t : ℝ) (x : ℝ^3) :
    ℝ≥0∞ := ∫⁻ s : ℝ, ∫⁻ y : ℝ^3, ‖exteriorNewtonKernel |t - s| (x - y)‖ₑ * F (s, y)

/-- The positive spacetime integral is jointly measurable in output time and position. -/
theorem measurable_spacetimeNewtonMajorant {F : ℝ × ℝ^3 → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun z : ℝ × ℝ^3 ↦ spacetimeNewtonMajorant F z.1 z.2) := by
  have hK : Measurable (fun z : ((ℝ × ℝ^3) × ℝ) × ℝ^3 ↦
      exteriorNewtonKernel |z.1.1.1 - z.1.2| (z.1.1.2 - z.2)) :=
    measurable_exteriorNewtonKernel_uncurry.comp ((continuous_abs.measurable.comp
        (measurable_fst.fst.fst.sub measurable_fst.snd)).prodMk
        (measurable_fst.fst.snd.sub measurable_snd))
  have h := hK.enorm.mul (hF.comp (measurable_fst.snd.prodMk measurable_snd))
  exact h.lintegral_prod_right'.lintegral_prod_right'

/-- At fixed output time, integral Minkowski and spatial Young give half-order time integration. -/
theorem eLpNorm_spacetimeNewtonMajorant_le {F : ℝ × ℝ^3 → ℝ≥0∞} (hF : Measurable F) (t : ℝ) :
    eLpNorm (spacetimeNewtonMajorant F t) 12 volume ≤
      (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ)) *
        fractionalIntegralHalf (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) t := by
  let A := fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume
  let C := ((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ)
  have hA : Measurable A := hF.eLpNorm_prod_right (by norm_num)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hK : Measurable (fun z : (ℝ^3 × ℝ) × ℝ^3 ↦ exteriorNewtonKernel |t - z.1.2| (z.1.1 - z.2)) :=
    measurable_exteriorNewtonKernel_uncurry.comp
      ((continuous_abs.measurable.comp (measurable_const.sub measurable_fst.snd)).prodMk
        (measurable_fst.fst.sub measurable_snd))
  have hm : Measurable (fun z : ℝ^3 × ℝ ↦ ∫⁻ y : ℝ^3,
      ‖exteriorNewtonKernel |t - z.2| (z.1 - y)‖ₑ * F (z.2, y)) :=
    (hK.enorm.mul (hF.comp (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right'
  calc
    _ ≤ ∫⁻ s : ℝ, eLpNorm
        (fun x : ℝ^3 ↦ ∫⁻ y : ℝ^3, ‖exteriorNewtonKernel |t - s| (x - y)‖ₑ * F (s, y))
        12 volume := by
      change eLpNorm (fun x : ℝ^3 ↦ ∫⁻ s : ℝ, ∫⁻ y : ℝ^3,
        ‖exteriorNewtonKernel |t - s| (x - y)‖ₑ * F (s, y)) 12 volume ≤ _
      simpa only [ENNReal.ofReal_ofNat] using
        ENNReal.eLpNorm_lintegral_le (μ := volume) (ν := volume) (by norm_num : (1 : ℝ) ≤ 12) hm
    _ ≤ ∫⁻ s : ℝ, C * (ENNReal.ofReal (dist s t ^ (-1 / 2 : ℝ)) * A s) := by
      apply lintegral_mono_ae
      filter_upwards [volume.ae_ne t] with s hs
      have hR : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr hs.symm)
      have h := ENNReal.eLpNorm_lintegral_convolution_le volume
        (g := fun y ↦ F (s, y)) (p := 6) (q := 12 / 11) (r := 12)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (measurable_exteriorNewtonKernel |t - s|).enorm (hF.comp measurable_prodMk_left)
      norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 11),
        ENNReal.ofReal_ofNat] at h
      rw [eLpNorm_enorm _ (measurable_exteriorNewtonKernel |t - s|).aestronglyMeasurable,
        eLpNorm_exteriorNewtonKernel hR] at h
      rw [Real.dist_eq, abs_sub_comm s t]
      simpa only [A, C, mul_assoc] using h
    _ = _ := lintegral_const_mul C
      (((measurable_id.dist measurable_const).pow_const (-1 / 2 : ℝ)).ennreal_ofReal.mul hA)

/-- The positive kernel integral maps the dual mixed norm to L⁴ time/L¹² space. -/
theorem mixed_eLpNorm_spacetimeNewtonMajorant_le {F : ℝ × ℝ^3 → ℝ≥0∞} (hF : Measurable F) :
    eLpNorm (fun t ↦ eLpNorm (spacetimeNewtonMajorant F t) 12 volume) 4 volume ≤
      (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ)) *
        (((2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) ^ (4 : ℝ) *
          ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16)) ^ (1 / 4 : ℝ)) *
            eLpNorm (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume := by
  have hm := (measurable_spacetimeNewtonMajorant hF).eLpNorm_prod_right (ν := volume)
    (by norm_num : (12 : ℝ≥0∞) ≠ 0) (by norm_num : (12 : ℝ≥0∞) ≠ ∞)
  have hA := hF.eLpNorm_prod_right (ν := volume) (by norm_num : (12 / 11 : ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num) : (12 / 11 : ℝ≥0∞) ≠ ∞)
  calc
    _ ≤ (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^
        (1 / 6 : ℝ)) * eLpNorm
          (fractionalIntegralHalf (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume))
          4 volume := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 4 hm.aestronglyMeasurable
      exact Eventually.of_forall (eLpNorm_spacetimeNewtonMajorant_le hF)
    _ ≤ _ := by
      have h := eLpNorm_fractionalIntegralHalf_le hA
      simpa only [mul_assoc] using mul_le_mul le_rfl h bot_le bot_le

/-- The positive integral is independent of the input's product-measure representative. -/
theorem spacetimeNewtonMajorant_congr_ae {F G : ℝ × ℝ^3 → ℝ≥0∞}
    (hFG : F =ᵐ[volume.prod volume] G) : spacetimeNewtonMajorant F = spacetimeNewtonMajorant G := by
  funext t x
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hFG] with s hs
  apply lintegral_congr_ae
  filter_upwards [hs] with y hy
  rw [hy]

/-- Real spacetime integration against the exterior Newtonian kernel. -/
noncomputable def spacetimeNewtonIntegral (F : ℝ × ℝ^3 → ℝ) (t : ℝ) (x : ℝ^3) : ℝ :=
  ∫ s : ℝ, ∫ y : ℝ^3, exteriorNewtonKernel |t - s| (x - y) * F (s, y)

/-- The real spacetime integral is jointly measurable. -/
theorem measurable_spacetimeNewtonIntegral {F : ℝ × ℝ^3 → ℝ} (hF : Measurable F) :
    Measurable (fun z : ℝ × ℝ^3 ↦ spacetimeNewtonIntegral F z.1 z.2) := by
  have hK : Measurable (fun z : ((ℝ × ℝ^3) × ℝ) × ℝ^3 ↦
      exteriorNewtonKernel |z.1.1.1 - z.1.2| (z.1.1.2 - z.2)) :=
    measurable_exteriorNewtonKernel_uncurry.comp ((continuous_abs.measurable.comp
        (measurable_fst.fst.fst.sub measurable_fst.snd)).prodMk
        (measurable_fst.fst.snd.sub measurable_snd))
  have h := (hK.mul (hF.comp (measurable_fst.snd.prodMk measurable_snd))).stronglyMeasurable
  exact h.integral_prod_right'.integral_prod_right'.measurable

/-- The Bochner integral is bounded by its positive majorant. -/
theorem enorm_spacetimeNewtonIntegral_le (F : ℝ × ℝ^3 → ℝ) (t : ℝ) (x : ℝ^3) :
    ‖spacetimeNewtonIntegral F t x‖ₑ ≤ spacetimeNewtonMajorant (fun z ↦ ‖F z‖ₑ) t x := by
  apply (enorm_integral_le_lintegral_enorm _).trans
  refine lintegral_mono fun s ↦ ?_
  simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm
    (fun y : ℝ^3 ↦ exteriorNewtonKernel |t - s| (x - y) * F (s, y))

/-- The real kernel integral satisfies the dual mixed-norm estimate. -/
theorem mixed_eLpNorm_spacetimeNewtonIntegral_le {F : ℝ × ℝ^3 → ℝ} (hF : Measurable F) :
    eLpNorm (fun t ↦ eLpNorm (spacetimeNewtonIntegral F t) 12 volume) 4 volume ≤
      (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ)) *
        (((2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) ^ (4 : ℝ) *
          ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16)) ^ (1 / 4 : ℝ)) *
            eLpNorm (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume := by
  have hm := measurable_spacetimeNewtonIntegral hF
  calc
    _ ≤ eLpNorm (fun t ↦ eLpNorm
        (spacetimeNewtonMajorant (fun z ↦ ‖F z‖ₑ) t) 12 volume) 4 volume := by
      apply eLpNorm_mono_enorm
        (hm.eLpNorm_prod_right (by norm_num) (by norm_num)).aestronglyMeasurable
      intro t
      apply eLpNorm_mono_enorm (hm.comp measurable_prodMk_left).aestronglyMeasurable
      exact enorm_spacetimeNewtonIntegral_le F t
    _ ≤ _ := by
      have h := mixed_eLpNorm_spacetimeNewtonMajorant_le hF.enorm
      have heq (s : ℝ) : eLpNorm (fun y ↦ ‖F (s, y)‖ₑ) (12 / 11) volume =
          eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume :=
        eLpNorm_enorm _ (hF.comp measurable_prodMk_left).aestronglyMeasurable
      simpa only [heq] using h

/-- The real integral is independent of the input's product-measure representative. -/
theorem spacetimeNewtonIntegral_congr_ae {F G : ℝ × ℝ^3 → ℝ}
    (hFG : F =ᵐ[volume.prod volume] G) : spacetimeNewtonIntegral F = spacetimeNewtonIntegral G := by
  funext t x
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hFG] with s hs
  apply integral_congr_ae
  filter_upwards [hs] with y hy
  rw [hy]

/-- The product of the spatial Young and temporal fractional-integral constants is finite. -/
theorem spacetime_newton_constant_lt_top :
    (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ)) *
      (((2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) ^ (4 : ℝ) *
        ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16)) ^ (1 / 4 : ℝ)) < ∞ := by
  apply ENNReal.mul_lt_top
  · apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  · apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      finiteness
    · finiteness

/-- Finite input mixed norm implies absolute integrability of the defining spacetime kernel
for almost every output point. This rules out reliance on a totalized Bochner integral. -/
theorem ae_integrable_spacetimeNewtonKernel {F : ℝ × ℝ^3 → ℝ} (hF : Measurable F)
    (hFfin : MemLp (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, Integrable (fun z : ℝ × ℝ^3 ↦
      exteriorNewtonKernel |t - z.1| (x - z.2) * F z) (volume.prod volume) := by
  have hbound := mixed_eLpNorm_spacetimeNewtonMajorant_le hF.enorm
  have hFnorm (s : ℝ) : eLpNorm (fun y ↦ ‖F (s, y)‖ₑ) (12 / 11) volume =
      eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume :=
    eLpNorm_enorm _ (hF.comp measurable_prodMk_left).aestronglyMeasurable
  simp_rw [hFnorm] at hbound
  have hfin : MemLp (fun t ↦ eLpNorm
      (spacetimeNewtonMajorant (fun z ↦ ‖F z‖ₑ) t) 12 volume) 4 volume :=
    hbound.trans_lt (ENNReal.mul_lt_top spacetime_newton_constant_lt_top hFfin)
  filter_upwards [hfin.ae_lt_top (by norm_num) (by norm_num)] with t ht
  change MemLp (spacetimeNewtonMajorant (fun z ↦ ‖F z‖ₑ) t) 12 volume at ht
  filter_upwards [ht.ae_lt_top (by norm_num) (by norm_num)] with x hx
  have hK : Measurable (fun z : ℝ × ℝ^3 ↦
      exteriorNewtonKernel |t - z.1| (x - z.2) * F z) := by
    apply Measurable.mul _ hF
    exact measurable_exteriorNewtonKernel_uncurry.comp
      ((continuous_abs.measurable.comp (measurable_const.sub measurable_fst)).prodMk
        (measurable_const.sub measurable_snd))
  refine ⟨hK.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hK.enorm.aemeasurable]
  simpa only [spacetimeNewtonMajorant, Function.comp_apply, enorm_mul] using hx

/-- Fubini identifies the iterated real operator with integration over input spacetime. -/
theorem spacetimeNewtonIntegral_eq_integral_prod {F : ℝ × ℝ^3 → ℝ} (hF : Measurable F)
    (hFfin : MemLp (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, spacetimeNewtonIntegral F t x = ∫ z : ℝ × ℝ^3,
      exteriorNewtonKernel |t - z.1| (x - z.2) * F z ∂volume.prod volume := by
  filter_upwards [ae_integrable_spacetimeNewtonKernel hF hFfin] with t ht
  filter_upwards [ht] with x hx using (integral_prod _ hx).symm

/-- Additivity holds for the iterated integral on finite mixed-norm data. -/
theorem spacetimeNewtonIntegral_add_ae {F G : ℝ × ℝ^3 → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFfin : MemLp (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume)
    (hGfin : MemLp (fun s ↦ eLpNorm (fun y ↦ G (s, y)) (12 / 11) volume) (4 / 3) volume) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, spacetimeNewtonIntegral (F + G) t x =
      spacetimeNewtonIntegral F t x + spacetimeNewtonIntegral G t x := by
  filter_upwards [ae_integrable_spacetimeNewtonKernel hF hFfin,
    ae_integrable_spacetimeNewtonKernel hG hGfin] with t htF htG
  filter_upwards [htF, htG] with x hxF hxG
  have hadd : Integrable (fun z : ℝ × ℝ^3 ↦
      exteriorNewtonKernel |t - z.1| (x - z.2) * (F + G) z) (volume.prod volume) := by
    convert! hxF.add hxG using 1
    ext z
    simp only [Pi.add_apply, mul_add]
  rw [spacetimeNewtonIntegral, ← integral_prod _ hadd]
  simp only [Pi.add_apply, mul_add]
  rw [integral_add hxF hxG, integral_prod _ hxF, integral_prod _ hxG]
  rfl

/-- Scalar multiplication commutes with the totalized real integral, pointwise. -/
theorem spacetimeNewtonIntegral_smul (c : ℝ) (F : ℝ × ℝ^3 → ℝ) :
    spacetimeNewtonIntegral (c • F) = c • spacetimeNewtonIntegral F := by
  funext t x
  simp only [spacetimeNewtonIntegral, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (exteriorNewtonKernel _ _) c, integral_const_mul]

/-- The Strichartz exponent `12` is at least one. -/
scoped instance fact_one_le_twelve : Fact (1 ≤ (12 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The dual Strichartz exponent `12 / 11` is at least one. -/
scoped instance fact_one_le_twelve_div_eleven : Fact (1 ≤ (12 / 11 : ℝ≥0∞)) := ⟨by
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 11),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 12 / 11)⟩

/-- The dual Strichartz exponent `4 / 3` is at least one. -/
scoped instance fact_one_le_four_div_three : Fact (1 ≤ (4 / 3 : ℝ≥0∞)) := ⟨by
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 4 / 3)⟩

local instance : Fact ((12 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

/-- Finite dual mixed-norm data yield a nested Lp output class with the kernel
integral as its spatial representative almost everywhere. -/
theorem exists_spacetimeNewtonLp {F : ℝ × ℝ^3 → ℝ} (hF : Measurable F)
    (hFfin : MemLp (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume) :
    ∃ u : Lp (Lp ℝ 12 (volume : Measure (ℝ^3))) 4 (volume : Measure ℝ),
      (∀ᵐ t ∂volume, (spacetimeNewtonIntegral F t) =ᵐ[volume] (u t : ℝ^3 → ℝ)) ∧
      ‖u‖ₑ ≤
        (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ)) *
          (((2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) ^ (4 : ℝ) *
            ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16)) ^ (1 / 4 : ℝ)) *
              eLpNorm (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume := by
  have hbound := mixed_eLpNorm_spacetimeNewtonIntegral_le hF
  have hfin : MemLp (fun t ↦ eLpNorm (spacetimeNewtonIntegral F t) 12 volume) 4 volume :=
    hbound.trans_lt (ENNReal.mul_lt_top spacetime_newton_constant_lt_top hFfin)
  obtain ⟨u, hu, hnorm⟩ := exists_mixedLp_sections
    (by norm_num : (12 : ℝ≥0∞) ≠ ∞) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)
    (measurable_spacetimeNewtonIntegral hF) hfin
  exact ⟨u, hu, hnorm.le.trans hbound⟩

end WaveEquation.Strichartz
