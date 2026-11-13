/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.SectionNorm
public import PDE.Analysis.Integration.Convolution.Young
public import PDE.Analysis.Integration.FractionalIntegral.HalfOrder.Estimate
public import PDE.Hyperbolic.Models.Wave.Strichartz.ExteriorKernel
import CAS.ExactTactic
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

/-!
# Spacetime pairing for the exterior Newtonian kernel

Spatial Young and temporal half-order integration bound the positive kernel
pairing by the L^(4/3) time/L^(12/11) space norms. The input functions may
have infinite norms. The zero time difference is discarded only on its null diagonal.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace WaveEquation.Strichartz

/-- The exterior Newtonian kernel defines a bounded positive spatial bilinear form. -/
theorem lintegral_exteriorNewtonKernel_mul_le {R : ℝ} (hR : 0 < R)
    {f g : ℝ^3 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (∫⁻ y, ‖exteriorNewtonKernel R (x - y)‖ₑ * f y) * g x) ≤
      (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^
          (1 / 6 : ℝ) * ENNReal.ofReal (R ^ (-1 / 2 : ℝ))) *
        eLpNorm f (12 / 11) volume * eLpNorm g (12 / 11) volume := by
  let H := fun x ↦ ∫⁻ y, ‖exteriorNewtonKernel R (x - y)‖ₑ * f y
  have hkm : Measurable (fun z : ℝ^3 × ℝ^3 ↦ ‖exteriorNewtonKernel R (z.1 - z.2)‖ₑ * f z.2) :=
    ((measurable_exteriorNewtonKernel R).comp (measurable_fst.sub measurable_snd)).enorm.mul
      (hf.comp measurable_snd)
  have hm : Measurable H := hkm.lintegral_prod_right
  have hpq : (12 : ℝ).HolderConjugate (12 / 11) := by
    rw [Real.holderConjugate_iff]
    constructor <;> cas
  have hholder : (∫⁻ x, H x * g x) ≤
      eLpNorm H 12 volume * eLpNorm g (12 / 11) volume := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hm.aemeasurable hg.aemeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
        (ENNReal.div_ne_top (by norm_num) (by norm_num)) hg.aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_div, enorm_eq_self]
    simpa only [Pi.mul_apply, one_div_div] using h
  have hYoung := ENNReal.eLpNorm_lintegral_convolution_le volume (p := 6) (q := 12 / 11) (r := 12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (measurable_exteriorNewtonKernel R).enorm hf
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 11),
    ENNReal.ofReal_ofNat] at hYoung
  rw [eLpNorm_enorm _ (measurable_exteriorNewtonKernel R).aestronglyMeasurable,
    eLpNorm_exteriorNewtonKernel hR] at hYoung
  apply hholder.trans
  gcongr 1

/-- Temporal half-order integration controls the spacetime exterior-kernel pairing. -/
theorem lintegral_spacetime_exteriorNewtonKernel_mul_le
    {F G : ℝ × ℝ^3 → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ t : ℝ, ∫⁻ s : ℝ, (∫⁻ x : ℝ^3,
      (∫⁻ y : ℝ^3, ‖exteriorNewtonKernel |t - s| (x - y)‖ₑ * F (s, y)) * G (t, x))) ≤
      (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ)) *
        (((2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) ^ (4 : ℝ) *
          ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16)) ^ (1 / 4 : ℝ)) *
          eLpNorm (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume *
          eLpNorm (fun t ↦ eLpNorm (fun x ↦ G (t, x)) (12 / 11) volume) (4 / 3) volume := by
  let A := fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume
  let B := fun t ↦ eLpNorm (fun x ↦ G (t, x)) (12 / 11) volume
  let C := ((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ)
  have hA : Measurable A := hF.eLpNorm_prod_right (by norm_num)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hB : Measurable B := hG.eLpNorm_prod_right (by norm_num)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hpoint (t : ℝ) : (∫⁻ s : ℝ, ∫⁻ x : ℝ^3,
        (∫⁻ y : ℝ^3, ‖exteriorNewtonKernel |t - s| (x - y)‖ₑ * F (s, y)) * G (t, x)) ≤
      C * fractionalIntegralHalf A t * B t := by
    calc
      _ ≤ ∫⁻ s : ℝ, (C * (ENNReal.ofReal (dist s t ^ (-1 / 2 : ℝ)) * A s)) * B t := by
        apply lintegral_mono_ae
        filter_upwards [volume.ae_ne t] with s hs
        have h := lintegral_exteriorNewtonKernel_mul_le
          (f := fun y ↦ F (s, y)) (g := fun x ↦ G (t, x)) (abs_pos.mpr (sub_ne_zero.mpr hs.symm))
          (hF.comp measurable_prodMk_left) (hG.comp measurable_prodMk_left)
        rw [Real.dist_eq, abs_sub_comm s t]
        simpa only [C, A, B, mul_assoc] using h
      _ = C * fractionalIntegralHalf A t * B t := by
        rw [lintegral_mul_const _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
        rfl
  calc
    _ ≤ ∫⁻ t : ℝ, C * fractionalIntegralHalf A t * B t := lintegral_mono hpoint
    _ = C * ∫⁻ t : ℝ, fractionalIntegralHalf A t * B t := by
      simp_rw [mul_assoc]
      exact lintegral_const_mul C ((measurable_fractionalIntegralHalf hA).mul hB)
    _ ≤ _ := by
      have h := lintegral_fractionalIntegralHalf_mul_le hA hB
      simpa only [A, B, C, mul_assoc] using mul_le_mul le_rfl h bot_le bot_le

end WaveEquation.Strichartz
