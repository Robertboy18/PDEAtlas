/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Maximal.Interval.Weak
public import PDE.Analysis.MeasureTheory.Integral.Layercake
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
# Strong Lp bounds for interval maximal averages

For every p > 1 the p-th power integral of the maximal function is bounded by
`2^p * 4*p/(p-1)` times that of the function. The initial layer-cake argument for
L1 data extends to all measurable nonnegative functions by bounded compact
truncations and monotone convergence.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- The strong maximal bound for integrable data, obtained from truncated weak bounds and layer
cake. -/
theorem lintegral_intervalMaximal_rpow_le_of_lintegral_lt_top {ι : Type*}
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ y, f y) < ⊤) {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, intervalMaximal r f x ^ p) ≤
      (2 : ℝ≥0∞) ^ p * (4 * ENNReal.ofReal p / ENNReal.ofReal (p - 1)) *
        ∫⁻ x, f x ^ p := by
  have hp₀ : 0 < p := lt_trans zero_lt_one hp
  have hfp : ∀ᵐ x, f x < ⊤ := ae_lt_top hf hfin.ne
  have hMm := (lowerSemicontinuous_intervalMaximal r hr hf).measurable
  have hMf := ae_intervalMaximal_lt_top r hr hfin
  have hMhalf : ∀ᵐ x, intervalMaximal r f x / 2 < ⊤ := by
    filter_upwards [hMf] with x hx
    exact ENNReal.div_lt_top hx.ne (by norm_num)
  have hlevel (t : ℝ) :
      {x | ENNReal.ofReal t < intervalMaximal r f x / 2} =
        {x | ENNReal.ofReal (2 * t) < intervalMaximal r f x} := by
    ext x
    change ENNReal.ofReal t < intervalMaximal r f x / 2 ↔
      ENNReal.ofReal (2 * t) < intervalMaximal r f x
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    rw [mul_comm, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  have hpoint (t : ℝ) (ht : 0 < t) :
      volume {x | ENNReal.ofReal t < intervalMaximal r f x / 2} *
          ENNReal.ofReal (t ^ (p - 1)) ≤
        4 * ((∫⁻ x in {x | ENNReal.ofReal t < f x}, f x) *
          ENNReal.ofReal (t ^ (p - 2))) := by
    rw [hlevel]
    have htstep : t ^ (p - 1) = t * t ^ (p - 2) := by
      calc
        _ = t ^ (1 + (p - 2)) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add ht, Real.rpow_one]
    rw [htstep, ENNReal.ofReal_mul ht.le]
    calc
      _ = (ENNReal.ofReal t *
          volume {x | ENNReal.ofReal (2 * t) < intervalMaximal r f x}) *
          ENNReal.ofReal (t ^ (p - 2)) := by ring
      _ ≤ (4 * ∫⁻ x in {x | ENNReal.ofReal t < f x}, f x) *
          ENNReal.ofReal (t ^ (p - 2)) := by
        gcongr 1
        exact mul_measure_intervalMaximal_superlevel_le_truncated r hr f ht
      _ = _ := by ring
  have htail := lintegral_rpow_eq_lintegral_truncated volume hf hfp hp
  have hcoef₀ : ENNReal.ofReal (p - 1) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp))
  have htail' : (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | ENNReal.ofReal t < f x}, f x) * ENNReal.ofReal (t ^ (p - 2))) =
      (∫⁻ x, f x ^ p) / ENNReal.ofReal (p - 1) := by
    rw [htail, mul_comm (ENNReal.ofReal (p - 1)),
      ENNReal.mul_div_cancel_right hcoef₀ ENNReal.ofReal_ne_top]
  have hhalf : (∫⁻ x, (intervalMaximal r f x / 2) ^ p) ≤
      (4 * ENNReal.ofReal p / ENNReal.ofReal (p - 1)) * ∫⁻ x, f x ^ p := by
    rw [lintegral_rpow_eq_lintegral_superlevel volume (hMm.div_const 2) hMhalf hp₀]
    calc
      _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          4 * ((∫⁻ x in {x | ENNReal.ofReal t < f x}, f x) *
            ENNReal.ofReal (t ^ (p - 2))) := by
        gcongr 1
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hpoint t ht
      _ = _ := by
        rw [lintegral_const_mul' 4 _ (by norm_num), htail']
        simp only [div_eq_mul_inv]
        ring
  calc
    _ = (2 : ℝ≥0∞) ^ p * ∫⁻ x, (intervalMaximal r f x / 2) ^ p := by
      rw [← lintegral_const_mul _ ((hMm.div_const 2).pow_const p)]
      apply lintegral_congr
      intro x
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp₀.le,
        ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr

/-- Maximal averages preserve pointwise order. -/
theorem intervalMaximal_mono {ι : Type*} (r : ι → ℝ) {f g : ℝ → ℝ≥0∞}
    (hfg : f ≤ g) : intervalMaximal r f ≤ intervalMaximal r g := by
  intro x
  exact iSup_mono fun _ ↦ ENNReal.div_le_div_right (lintegral_mono hfg) _

/-- Maximal averages commute with increasing countable suprema of measurable functions. -/
theorem intervalMaximal_iSup {ι : Type*} (r : ι → ℝ) {f : ℕ → ℝ → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) (x : ℝ) :
    intervalMaximal r (fun y ↦ ⨆ n, f n y) x = ⨆ n, intervalMaximal r (f n) x := by
  simp only [intervalMaximal]
  simp_rw [lintegral_iSup hf hmono, ENNReal.iSup_div]
  exact iSup_comm

/-- The strong maximal bound holds for all measurable functions, with no L1 premise. -/
theorem lintegral_intervalMaximal_rpow_le {ι : Type*} (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, intervalMaximal r f x ^ p) ≤
      (2 : ℝ≥0∞) ^ p * (4 * ENNReal.ofReal p / ENNReal.ofReal (p - 1)) *
        ∫⁻ x, f x ^ p := by
  classical
  let g : ℕ → ℝ → ℝ≥0∞ := fun n ↦ (ball 0 (n : ℝ)).indicator (fun x ↦ min (f x) n)
  have hgm (n : ℕ) : Measurable (g n) := (hf.inf measurable_const).indicator measurableSet_ball
  have hgle (n : ℕ) : g n ≤ f := by
    intro x
    by_cases hx : x ∈ ball (0 : ℝ) (n : ℝ)
    · simpa only [g, indicator_of_mem hx] using min_le_left (f x) (n : ℝ≥0∞)
    · simp only [g, indicator_of_notMem hx]
      exact zero_le
  have hmono : Monotone g := by
    intro m n hmn x
    by_cases hx : x ∈ ball (0 : ℝ) (m : ℝ)
    · have hxn := ball_subset_ball (Nat.cast_le.mpr hmn) hx
      simp only [g, indicator_of_mem hx, indicator_of_mem hxn]
      exact min_le_min le_rfl (Nat.cast_le.mpr hmn)
    · simp only [g, indicator_of_notMem hx]
      exact zero_le
  have hgfin (n : ℕ) : (∫⁻ x, g n x) < ⊤ := by
    have hbound : (∫⁻ x, g n x) ≤ (n : ℝ≥0∞) * volume (ball (0 : ℝ) n) := by
      calc
        _ ≤ ∫⁻ x, (ball (0 : ℝ) (n : ℝ)).indicator (fun _ ↦ (n : ℝ≥0∞)) x := by
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ ball (0 : ℝ) (n : ℝ)
          · simpa only [g, indicator_of_mem hx] using min_le_right (f x) (n : ℝ≥0∞)
          · simp only [g, indicator_of_notMem hx, le_refl]
        _ = _ := by rw [lintegral_indicator measurableSet_ball]; simp
    apply hbound.trans_lt
    rw [Real.volume_ball]
    exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
  have hsup (x : ℝ) : (⨆ n, g n x) = f x := by
    apply le_antisymm (iSup_le fun n ↦ hgle n x)
    have hmin (n : ℕ) : min (f x) (n : ℝ≥0∞) ≤ ⨆ k, g k x := by
      obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
      have hxm : x ∈ ball (0 : ℝ) (max n k : ℕ) := by
        rw [mem_ball_zero_iff]
        exact hk.trans_le (Nat.cast_le.mpr (le_max_right n k))
      calc
        _ ≤ min (f x) (max n k : ℕ) := min_le_min le_rfl (Nat.cast_le.mpr (le_max_left n k))
        _ = g (max n k) x := by simp only [g, indicator_of_mem hxm]
        _ ≤ _ := le_iSup (fun k ↦ g k x) (max n k)
    have heq : (⨆ n : ℕ, min (f x) (n : ℝ≥0∞)) = f x := by
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    rw [← heq]
    exact iSup_le hmin
  have hMsup (x : ℝ) : intervalMaximal r f x = ⨆ n, intervalMaximal r (g n) x := by
    rw [← intervalMaximal_iSup r hgm hmono]
    simp_rw [hsup]
  have hMmono : Monotone fun n x ↦ intervalMaximal r (g n) x ^ p := by
    intro m n hmn x
    exact ENNReal.rpow_le_rpow (intervalMaximal_mono r (hmono hmn) x)
      (lt_trans zero_lt_one hp).le
  calc
    _ = ∫⁻ x, ⨆ n, intervalMaximal r (g n) x ^ p := by
      apply lintegral_congr
      intro x
      rw [hMsup]
      exact (ENNReal.orderIsoRpow p (lt_trans zero_lt_one hp)).map_iSup _
    _ = ⨆ n, ∫⁻ x, intervalMaximal r (g n) x ^ p :=
      lintegral_iSup (fun n ↦
        (lowerSemicontinuous_intervalMaximal r hr (hgm n)).measurable.pow_const p) hMmono
    _ ≤ _ := by
      apply iSup_le
      intro n
      calc
        _ ≤ _ := lintegral_intervalMaximal_rpow_le_of_lintegral_lt_top r hr (hgm n) (hgfin n) hp
        _ ≤ _ := by
          gcongr with x
          exact hgle n x

end MeasureTheory
