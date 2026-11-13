/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.FractionalIntegral.HalfOrder.Kernel
public import PDE.Analysis.MeasureTheory.Maximal.Interval.Strong
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# Half-order Hardy–Littlewood–Sobolev inequality

The near/far layer-cake split and a balancing radius give Hedberg's pointwise
estimate. The strong maximal theorem then proves L^(4/3)(ℝ) → L⁴(ℝ), followed by
its bilinear form. Both final bounds assume only measurability and retain infinite
norms. This is the half-order, one-dimensional case of the Hardy–Littlewood–Sobolev
inequality.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- The quarter power of a layer-cake interval length has inverse square-root decay. -/
theorem volume_ball_neg_two_quarter (x : ℝ) {t : ℝ} (ht : 0 < t) :
    volume (ball x (t ^ (-2 : ℝ))) ^ (1 / 4 : ℝ) =
      (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) * ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) := by
  rw [Real.volume_ball, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht _), ← Real.rpow_mul ht.le]
  norm_num

/-- Splitting the layer-cake integral balances the global L^(4/3) norm
against the local maximal average, without any integrability premise. -/
theorem fractionalIntegralHalf_le_split {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (x : ℝ) {L : ℝ} (hL : 0 < L) :
    fractionalIntegralHalf f x ≤
      (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) * (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        ENNReal.ofReal (2 * L ^ (1 / 2 : ℝ)) +
      (2 * centeredMaximal f x) * ENNReal.ofReal L⁻¹ := by
  have hnear : (∫⁻ t in Ioc (0 : ℝ) L, ∫⁻ y in ball x (t ^ (-2 : ℝ)), f y) ≤
      (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) * (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        ENNReal.ofReal (2 * L ^ (1 / 2 : ℝ)) := by
    calc
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) L,
          ((2 : ℝ≥0∞) ^ (1 / 4 : ℝ) * (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ)) *
            ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have h := lintegral_ball_le_volume_quarter_mul hf x (t ^ (-2 : ℝ))
        rw [volume_ball_neg_two_quarter x ht.1] at h
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_Ioc_neg_half hL.le]
  have hfar : (∫⁻ t in Ioi L, ∫⁻ y in ball x (t ^ (-2 : ℝ)), f y) ≤
      (2 * centeredMaximal f x) * ENNReal.ofReal L⁻¹ := by
    calc
      _ ≤ ∫⁻ t in Ioi L, (2 * centeredMaximal f x) * ENNReal.ofReal (t ^ (-2 : ℝ)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have h := lintegral_ball_le_centeredMaximal f x
          (Real.rpow_pos_of_pos (hL.trans ht) (-2))
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at h
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_Ioi_neg_two hL]
  rw [fractionalIntegralHalf_eq_lintegral_ball hf x, ← Ioc_union_Ioi_eq_Ioi hL.le,
    lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  exact add_le_add hnear hfar

/-- The cutoff that balances the two half-order kernel estimates. -/
theorem balanced_fractional_cutoff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * ((b / a) ^ (2 / 3 : ℝ)) ^ (1 / 2 : ℝ) =
        a ^ (2 / 3 : ℝ) * b ^ (1 / 3 : ℝ) ∧
      b * ((b / a) ^ (2 / 3 : ℝ))⁻¹ = a ^ (2 / 3 : ℝ) * b ^ (1 / 3 : ℝ) := by
  constructor <;> cas using [ha, hb]

/-- Pointwise half-order fractional integration, obtained by balancing the proved split. -/
theorem fractionalIntegralHalf_le_hedberg_of_pos {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (x : ℝ) (hF₀ : (∫⁻ y, f y ^ (4 / 3 : ℝ)) ≠ 0)
    (hFtop : (∫⁻ y, f y ^ (4 / 3 : ℝ)) ≠ ⊤)
    (hM₀ : centeredMaximal f x ≠ 0) (hMtop : centeredMaximal f x ≠ ⊤) :
    fractionalIntegralHalf f x ≤ (2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) *
      (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (1 / 2 : ℝ) * centeredMaximal f x ^ (1 / 3 : ℝ) := by
  let A := (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ)
  let M := centeredMaximal f x
  have hA₀ : A ≠ 0 := (ENNReal.rpow_eq_zero_iff_of_pos (by norm_num)).not.mpr hF₀
  have hAtop : A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hFtop
  have ha : 0 < A.toReal := ENNReal.toReal_pos hA₀ hAtop
  have hb : 0 < M.toReal := ENNReal.toReal_pos hM₀ hMtop
  let L := (M.toReal / A.toReal) ^ (2 / 3 : ℝ)
  have hL : 0 < L := Real.rpow_pos_of_pos (div_pos hb ha) _
  obtain ⟨hbal₁, hbal₂⟩ := balanced_fractional_cutoff ha hb
  have hbal₁' : A * ENNReal.ofReal (L ^ (1 / 2 : ℝ)) =
      A ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ) := by
    calc
      _ = ENNReal.ofReal (A.toReal * L ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_toReal hAtop]
      _ = ENNReal.ofReal (A.toReal ^ (2 / 3 : ℝ) * M.toReal ^ (1 / 3 : ℝ)) :=
        congrArg ENNReal.ofReal hbal₁
      _ = _ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),
          ← ENNReal.ofReal_rpow_of_pos ha, ← ENNReal.ofReal_rpow_of_pos hb,
          ENNReal.ofReal_toReal hAtop, ENNReal.ofReal_toReal hMtop]
  have hbal₂' : M * ENNReal.ofReal L⁻¹ = A ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ) := by
    calc
      _ = ENNReal.ofReal (M.toReal * L⁻¹) := by
        rw [ENNReal.ofReal_mul hb.le, ENNReal.ofReal_toReal hMtop]
      _ = ENNReal.ofReal (A.toReal ^ (2 / 3 : ℝ) * M.toReal ^ (1 / 3 : ℝ)) :=
        congrArg ENNReal.ofReal hbal₂
      _ = _ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),
          ← ENNReal.ofReal_rpow_of_pos ha, ← ENNReal.ofReal_rpow_of_pos hb,
          ENNReal.ofReal_toReal hAtop, ENNReal.ofReal_toReal hMtop]
  have hsplit := fractionalIntegralHalf_le_split hf x hL
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at hsplit
  have hA : A ^ (2 / 3 : ℝ) = (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (1 / 2 : ℝ) := by
    dsimp only [A]
    rw [← ENNReal.rpow_mul]
    norm_num
  calc
    _ ≤ _ := hsplit
    _ = (2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ)) * (A * ENNReal.ofReal (L ^ (1 / 2 : ℝ))) +
        2 * (M * ENNReal.ofReal L⁻¹) := by ring
    _ = _ := by rw [hbal₁', hbal₂', hA]; ring

/-- Hedberg's estimate includes zero maximal averages and arbitrary measurable L^(4/3) data. -/
theorem fractionalIntegralHalf_le_hedberg {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hFtop : (∫⁻ y, f y ^ (4 / 3 : ℝ)) ≠ ⊤) (x : ℝ) :
    fractionalIntegralHalf f x ≤ (2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) *
      (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (1 / 2 : ℝ) * centeredMaximal f x ^ (1 / 3 : ℝ) := by
  by_cases hF₀ : (∫⁻ y, f y ^ (4 / 3 : ℝ)) = 0
  · have hz := ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero
      (by norm_num : (0 : ℝ) ≤ 4 / 3) hf.aemeasurable hF₀
    have hI : fractionalIntegralHalf f x = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hz] with y hy
      simp only [Pi.zero_apply] at hy ⊢
      rw [hy, mul_zero]
    rw [hI]
    exact zero_le
  by_cases hM₀ : centeredMaximal f x = 0
  · have hI : fractionalIntegralHalf f x = 0 := by
      rw [fractionalIntegralHalf_eq_lintegral_ball hf x]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hb := lintegral_ball_le_centeredMaximal f x (Real.rpow_pos_of_pos ht (-2))
      rw [hM₀, mul_zero] at hb
      exact le_antisymm hb bot_le
    rw [hI]
    exact zero_le
  by_cases hMtop : centeredMaximal f x = ⊤
  · have hc : (2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) *
        (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (1 / 2 : ℝ) ≠ 0 := by
      apply mul_ne_zero
      · positivity
      · exact (ENNReal.rpow_eq_zero_iff_of_pos (by norm_num)).not.mpr hF₀
    rw [hMtop, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top hc]
    exact le_top
  exact fractionalIntegralHalf_le_hedberg_of_pos hf x hF₀ hFtop hM₀ hMtop

/-- The strong L^(4/3)-to-L^4 fractional-integral estimate on the real line. -/
theorem lintegral_fractionalIntegralHalf_rpow_four_le {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, fractionalIntegralHalf f x ^ (4 : ℝ)) ≤
      (2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) ^ (4 : ℝ) *
        ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16) * (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (3 : ℝ) := by
  let F := ∫⁻ y, f y ^ (4 / 3 : ℝ)
  let C := 2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2
  by_cases hFtop : F = ⊤
  · change _ ≤ C ^ (4 : ℝ) * ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16) * F ^ (3 : ℝ)
    rw [hFtop, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (by dsimp [C]; positivity)]
    exact le_top
  have hpoint (x : ℝ) : fractionalIntegralHalf f x ^ (4 : ℝ) ≤
      C ^ (4 : ℝ) * F ^ (2 : ℝ) * centeredMaximal f x ^ (4 / 3 : ℝ) := by
    have h := ENNReal.rpow_le_rpow (fractionalIntegralHalf_le_hedberg hf hFtop x)
      (by norm_num : (0 : ℝ) ≤ 4)
    change _ ≤ (C * F ^ (1 / 2 : ℝ) * centeredMaximal f x ^ (1 / 3 : ℝ)) ^ (4 : ℝ) at h
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul] at h
    norm_num only [show (1 / 2 : ℝ) * 4 = 2 by norm_num,
      show (1 / 3 : ℝ) * 4 = 4 / 3 by norm_num] at h
    exact h
  have hM := lintegral_intervalMaximal_rpow_le (fun r : Ioi (0 : ℝ) ↦ r.val)
    (fun r ↦ r.property) hf (by norm_num : (1 : ℝ) < 4 / 3)
  norm_num only [show (4 / 3 : ℝ) - 1 = 1 / 3 by norm_num,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_one] at hM
  have hcoef : (4 : ℝ≥0∞) * (4 / 3) / (1 / 3) = 16 := by
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    calc
      _ = 16 * ((3 : ℝ≥0∞)⁻¹ * 3) := by ring
      _ = 16 := by rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  rw [hcoef] at hM
  calc
    _ ≤ ∫⁻ x, (C ^ (4 : ℝ) * F ^ (2 : ℝ)) * centeredMaximal f x ^ (4 / 3 : ℝ) :=
      lintegral_mono hpoint
    _ = (C ^ (4 : ℝ) * F ^ (2 : ℝ)) * ∫⁻ x, centeredMaximal f x ^ (4 / 3 : ℝ) := by
      exact lintegral_const_mul _ ((lowerSemicontinuous_intervalMaximal
        (fun r : Ioi (0 : ℝ) ↦ r.val) (fun r ↦ r.property) hf).measurable.pow_const _)
    _ ≤ (C ^ (4 : ℝ) * F ^ (2 : ℝ)) * (((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16) * F) := by
      gcongr 1
      exact hM
    _ = _ := by
      have hF : F ^ (2 : ℝ) * F = F ^ (3 : ℝ) := by
        calc
          _ = F ^ (2 : ℝ) * F ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
          _ = F ^ (2 + 1 : ℝ) := (ENNReal.rpow_add_of_nonneg 2 1 (by norm_num) (by norm_num)).symm
          _ = _ := by norm_num
      calc
        _ = C ^ (4 : ℝ) * ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16) * (F ^ (2 : ℝ) * F) := by ring
        _ = _ := by rw [hF]

/-- Half-order fractional integration maps L^(4/3)(ℝ) to L⁴(ℝ). -/
theorem eLpNorm_fractionalIntegralHalf_le {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    eLpNorm (fractionalIntegralHalf f) 4 volume ≤
      ((2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) ^ (4 : ℝ) *
        ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16)) ^ (1 / 4 : ℝ) * eLpNorm f (4 / 3) volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (measurable_fractionalIntegralHalf hf).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
      (ENNReal.div_ne_top (by norm_num) (by norm_num)) hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_div, enorm_eq_self]
  have h := ENNReal.rpow_le_rpow (lintegral_fractionalIntegralHalf_rpow_four_le hf)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4),
    ← ENNReal.rpow_mul, show (3 : ℝ) * (1 / 4) = 3 / 4 by norm_num] using h

/-- The bilinear half-order fractional-integral bound on two L^(4/3) functions. -/
theorem lintegral_fractionalIntegralHalf_mul_le {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, fractionalIntegralHalf f x * g x) ≤
      ((2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) ^ (4 : ℝ) *
        ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16)) ^ (1 / 4 : ℝ) *
          eLpNorm f (4 / 3) volume * eLpNorm g (4 / 3) volume := by
  have hconj : (4 : ℝ).HolderConjugate (4 / 3) := by
    rw [Real.holderConjugate_iff]
    constructor <;> cas
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj
    (measurable_fractionalIntegralHalf hf).aemeasurable hg.aemeasurable
  have hnorm : (∫⁻ x, fractionalIntegralHalf f x * g x) ≤
      eLpNorm (fractionalIntegralHalf f) 4 volume * eLpNorm g (4 / 3) volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (measurable_fractionalIntegralHalf hf).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
        (ENNReal.div_ne_top (by norm_num) (by norm_num)) hg.aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_div, enorm_eq_self]
    simpa only [Pi.mul_apply, one_div_div] using h
  apply hnorm.trans
  gcongr 1
  exact eLpNorm_fractionalIntegralHalf_le hf

end MeasureTheory
