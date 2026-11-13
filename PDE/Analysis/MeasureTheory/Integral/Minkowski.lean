/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Prod
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
# Integral Minkowski inequality

For finite real exponents p ≥ 1, the Lp norm of a parameter integral is at most
the integral of the section Lp norms. The spatial measure is sigma-finite and
the parameter measure is s-finite. Extended norms may be infinite.

The proof uses Hölder power tests followed by monotone finite-measure truncation.
The vector-valued version accepts a.e. strongly measurable families and transports
their representatives through both integrals. Finite integrated section norms
also imply actual section integrability almost everywhere.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace ENNReal

private theorem lintegral_Lp_le_lintegral_Lp_of_le_lintegral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {p q : ℝ} (hpq : p.HolderConjugate q) {f : α × β → ℝ≥0∞}
    (hf : Measurable f) {v : α → ℝ≥0∞} (hv : Measurable v)
    (hvfin : (∫⁻ x, v x ^ p ∂μ) < ∞)
    (hle : ∀ x, v x ≤ ∫⁻ y, f (x, y) ∂ν) :
    (∫⁻ x, v x ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ y, (∫⁻ x, f (x, y) ^ p ∂μ) ^ (1 / p) ∂ν := by
  let J := ∫⁻ x, v x ^ p ∂μ
  have hbound : J ≤ (∫⁻ y, (∫⁻ x, f (x, y) ^ p ∂μ) ^ (1 / p) ∂ν) *
      J ^ (1 / q) := by
    calc
      J ≤ ∫⁻ x, (∫⁻ y, f (x, y) ∂ν) * v x ^ (p - 1) ∂μ := by
        apply lintegral_mono
        intro x
        calc
          v x ^ p = v x * v x ^ (p - 1) := by
            nth_rw 2 [← rpow_one (v x)]
            rw [← rpow_add_of_nonneg 1 (p - 1) zero_le_one hpq.sub_one_pos.le,
              add_sub_cancel]
          _ ≤ _ := mul_le_mul (hle x) le_rfl bot_le bot_le
      _ = ∫⁻ y, ∫⁻ x, f (x, y) * v x ^ (p - 1) ∂μ ∂ν := by
        have heq (x : α) : (∫⁻ y, f (x, y) ∂ν) * v x ^ (p - 1) =
            ∫⁻ y, f (x, y) * v x ^ (p - 1) ∂ν :=
          (lintegral_mul_const _ (hf.comp measurable_prodMk_left)).symm
        simp_rw [heq]
        exact lintegral_lintegral_swap
          ((hf.mul ((hv.comp measurable_fst).pow_const _)).aemeasurable)
      _ ≤ ∫⁻ y, (∫⁻ x, f (x, y) ^ p ∂μ) ^ (1 / p) * J ^ (1 / q) ∂ν := by
        apply lintegral_mono
        intro y
        exact lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq
          (hf.comp measurable_prodMk_right).aemeasurable hv.aemeasurable
      _ = _ := lintegral_mul_const _
        (((hf.comp measurable_swap).pow_const p).lintegral_prod_right'.pow_const _)
  change J ^ (1 / p) ≤ _
  by_cases hJ : J = 0
  · rw [hJ, one_div, zero_rpow_of_pos hpq.inv_pos]
    exact zero_le
  have hJtop : J ≠ ∞ := hvfin.ne
  have hfactor : J ^ (1 / p) * J ^ (1 / q) = J := by
    rw [← rpow_add _ _ hJ hJtop, one_div, one_div, hpq.inv_add_inv_eq_one, rpow_one]
  have hJpow : J ^ (1 / q) ≠ 0 := by simp [hJ, hJtop]
  have hJpowtop : J ^ (1 / q) ≠ ∞ :=
    rpow_ne_top_of_nonneg (by simpa only [one_div] using hpq.symm.inv_nonneg) hJtop
  apply (ENNReal.mul_le_mul_iff_left hJpow hJpowtop).mp
  exact hfactor.le.trans hbound

/-- Integral Minkowski inequality for a nonnegative measurable family on a sigma-finite space. -/
theorem lintegral_Lp_lintegral_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SigmaFinite μ] [SFinite ν] {p : ℝ} (hp : 1 ≤ p) {f : α × β → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, (∫⁻ y, f (x, y) ∂ν) ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ y, (∫⁻ x, f (x, y) ^ p ∂μ) ^ (1 / p) ∂ν := by
  classical
  rcases eq_or_lt_of_le hp with rfl | hp
  · simpa only [one_div_one, rpow_one] using
      (lintegral_lintegral_swap (f := fun x y ↦ f (x, y)) hf.aemeasurable).le
  have hpq := Real.HolderConjugate.conjExponent hp
  let g := fun x ↦ ∫⁻ y, f (x, y) ∂ν
  have hg : Measurable g := hf.lintegral_prod_right'
  let v : ℕ → α → ℝ≥0∞ := fun n ↦
    (spanningSets μ n).indicator (fun x ↦ min (g x) n)
  have hvm (n : ℕ) : Measurable (v n) :=
    (hg.inf measurable_const).indicator (measurableSet_spanningSets μ n)
  have hvle (n : ℕ) (x : α) : v n x ≤ g x := by
    by_cases hx : x ∈ spanningSets μ n
    · simpa only [v, indicator_of_mem hx] using min_le_left (g x) (n : ℝ≥0∞)
    · simp only [v, indicator_of_notMem hx]
      exact bot_le
  have hvmono : Monotone v := by
    intro m n hmn x
    by_cases hx : x ∈ spanningSets μ m
    · have hxn := spanningSets_mono hmn hx
      simp only [v, indicator_of_mem hx, indicator_of_mem hxn]
      exact min_le_min le_rfl (Nat.cast_le.mpr hmn)
    · simp only [v, indicator_of_notMem hx]
      exact bot_le
  have hvfin (n : ℕ) : (∫⁻ x, v n x ^ p ∂μ) < ∞ := by
    have hbound : (∫⁻ x, v n x ^ p ∂μ) ≤
        (n : ℝ≥0∞) ^ p * μ (spanningSets μ n) := by
      calc
        _ ≤ ∫⁻ x, (spanningSets μ n).indicator (fun _ ↦ (n : ℝ≥0∞) ^ p) x ∂μ := by
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ spanningSets μ n
          · simp only [v, indicator_of_mem hx]
            exact rpow_le_rpow (min_le_right (g x) n) hpq.pos.le
          · simp only [v, indicator_of_notMem hx, zero_rpow_of_pos hpq.pos, le_refl]
        _ = _ := by rw [lintegral_indicator (measurableSet_spanningSets μ n)]; simp
    apply hbound.trans_lt
    exact mul_lt_top (rpow_lt_top_of_nonneg hpq.pos.le (by simp))
      (measure_spanningSets_lt_top μ n)
  have hvsup (x : α) : (⨆ n, v n x) = g x := by
    apply le_antisymm (iSup_le fun n ↦ hvle n x)
    obtain ⟨k, hk⟩ := iUnion_eq_univ_iff.mp (iUnion_spanningSets μ) x
    have hmin (n : ℕ) : min (g x) (n : ℝ≥0∞) ≤ ⨆ j, v j x := by
      have hxm := spanningSets_mono (le_max_right n k) hk
      calc
        _ ≤ min (g x) (max n k : ℕ) := min_le_min le_rfl (Nat.cast_le.mpr (le_max_left n k))
        _ = v (max n k) x := by simp only [v, indicator_of_mem hxm]
        _ ≤ _ := le_iSup (fun j ↦ v j x) (max n k)
    have heq : (⨆ n : ℕ, min (g x) (n : ℝ≥0∞)) = g x := by
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    rw [← heq]
    exact iSup_le hmin
  have hpower : (∫⁻ x, g x ^ p ∂μ) ≤
      (∫⁻ y, (∫⁻ x, f (x, y) ^ p ∂μ) ^ (1 / p) ∂ν) ^ p := by
    calc
      _ = ∫⁻ x, ⨆ n, v n x ^ p ∂μ := by
        apply lintegral_congr
        intro x
        rw [← hvsup x]
        exact (ENNReal.orderIsoRpow p hpq.pos).map_iSup _
      _ = ⨆ n, ∫⁻ x, v n x ^ p ∂μ :=
        lintegral_iSup (fun n ↦ (hvm n).pow_const p)
          (fun m n hmn x ↦ rpow_le_rpow (hvmono hmn x) hpq.pos.le)
      _ ≤ _ := by
        apply iSup_le
        intro n
        have h := lintegral_Lp_le_lintegral_Lp_of_le_lintegral hpq hf (hvm n)
          (hvfin n) (hvle n)
        have h' := rpow_le_rpow h hpq.pos.le
        simpa only [← rpow_mul, one_div_mul_cancel hpq.ne_zero, rpow_one] using h'
  have h := rpow_le_rpow hpower hpq.inv_nonneg
  simpa only [one_div, ← rpow_mul, mul_inv_cancel₀ hpq.ne_zero, rpow_one] using h

end ENNReal

/-- Minkowski's integral inequality, stated with Mathlib's extended `eLpNorm`. -/
theorem ENNReal.eLpNorm_lintegral_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SigmaFinite μ] [SFinite ν] {p : ℝ} (hp : 1 ≤ p) {f : α × β → ℝ≥0∞}
    (hf : Measurable f) :
    eLpNorm (fun x ↦ ∫⁻ y, f (x, y) ∂ν) (ENNReal.ofReal p) μ ≤
      ∫⁻ y, eLpNorm (fun x ↦ f (x, y)) (ENNReal.ofReal p) μ ∂ν := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have heq (y : β) : eLpNorm (fun x ↦ f (x, y)) (ENNReal.ofReal p) μ =
      (∫⁻ x, f (x, y) ^ p ∂μ) ^ (1 / p) := by
    have hy : Measurable (fun x ↦ f (x, y)) := hf.comp measurable_prodMk_right
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp₀)) ENNReal.ofReal_ne_top hy.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hp₀.le, enorm_eq_self]
  simp_rw [heq]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp₀)) ENNReal.ofReal_ne_top
    hf.lintegral_prod_right'.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal hp₀.le, enorm_eq_self] using
    ENNReal.lintegral_Lp_lintegral_le hp hf

namespace MeasureTheory

/-- Integral Minkowski for a strongly measurable family of vectors. -/
private theorem eLpNorm_integral_le_lintegral_eLpNorm_of_stronglyMeasurable {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SFinite ν] {p : ℝ}
    (hp : 1 ≤ p) {f : α × β → E} (hf : StronglyMeasurable f) :
    eLpNorm (fun x ↦ ∫ y, f (x, y) ∂ν) (ENNReal.ofReal p) μ ≤
      ∫⁻ y, eLpNorm (fun x ↦ f (x, y)) (ENNReal.ofReal p) μ ∂ν := by
  calc
    _ ≤ eLpNorm (fun x ↦ ∫⁻ y, ‖f (x, y)‖ₑ ∂ν) (ENNReal.ofReal p) μ := by
      apply eLpNorm_mono_enorm hf.integral_prod_right'.aestronglyMeasurable
      intro x
      exact enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, eLpNorm (fun x ↦ ‖f (x, y)‖ₑ) (ENNReal.ofReal p) μ ∂ν :=
      ENNReal.eLpNorm_lintegral_le hp hf.enorm
    _ = _ := by
      apply lintegral_congr
      intro y
      exact eLpNorm_enorm _ (hf.comp_measurable measurable_prodMk_right).aestronglyMeasurable

/-- An integrable family of Lp norms gives integrable sections almost everywhere. -/
private theorem ae_integrable_of_lintegral_eLpNorm_lt_top_of_stronglyMeasurable {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SFinite ν] {p : ℝ}
    (hp : 1 ≤ p) {f : α × β → E} (hf : StronglyMeasurable f)
    (hfin : (∫⁻ y, eLpNorm (fun x ↦ f (x, y)) (ENNReal.ofReal p) μ ∂ν) < ∞) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) ν := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hm := hf.enorm.lintegral_prod_right' (ν := ν)
  have hbound := ENNReal.eLpNorm_lintegral_le (μ := μ) (ν := ν) hp hf.enorm
  have heq (y : β) : eLpNorm (fun x ↦ ‖f (x, y)‖ₑ) (ENNReal.ofReal p) μ =
      eLpNorm (fun x ↦ f (x, y)) (ENNReal.ofReal p) μ :=
    eLpNorm_enorm _ (hf.comp_measurable measurable_prodMk_right).aestronglyMeasurable
  simp_rw [heq] at hbound
  have hpow := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp₀)) ENNReal.ofReal_ne_top (hbound.trans_lt hfin)
  simp only [ENNReal.toReal_ofReal hp₀.le, enorm_eq_self] at hpow
  filter_upwards [ae_lt_top (hm.pow_const p) hpow.ne] with x hx
  refine ⟨(hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  by_contra h
  have heq : (∫⁻ y, ‖f (x, y)‖ₑ ∂ν) = ∞ := top_unique (not_lt.mp h)
  rw [heq, ENNReal.top_rpow_of_pos hp₀] at hx
  exact (lt_irrefl _ hx)

/-- Integral Minkowski for an a.e. strongly measurable vector-valued family.
The product-measure representative is transported through both iterated norms. -/
theorem eLpNorm_integral_le_lintegral_eLpNorm {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SFinite ν] {p : ℝ}
    (hp : 1 ≤ p) {f : α × β → E} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    eLpNorm (fun x ↦ ∫ y, f (x, y) ∂ν) (ENNReal.ofReal p) μ ≤
      ∫⁻ y, eLpNorm (fun x ↦ f (x, y)) (ENNReal.ofReal p) μ ∂ν := by
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk
  have hleft : eLpNorm (fun x ↦ ∫ y, f (x, y) ∂ν) (ENNReal.ofReal p) μ =
      eLpNorm (fun x ↦ ∫ y, hf.mk f (x, y) ∂ν) (ENNReal.ofReal p) μ := by
    apply eLpNorm_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
    exact integral_congr_ae hx
  have hright : (∫⁻ y, eLpNorm (fun x ↦ f (x, y)) (ENNReal.ofReal p) μ ∂ν) =
      ∫⁻ y, eLpNorm (fun x ↦ hf.mk f (x, y)) (ENNReal.ofReal p) μ ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with y hy
    exact eLpNorm_congr_ae hy
  rw [hleft, hright]
  exact eLpNorm_integral_le_lintegral_eLpNorm_of_stronglyMeasurable hp hf.stronglyMeasurable_mk

/-- Finite integrated Lp norms give actual integrable sections for any a.e. representative. -/
theorem ae_integrable_of_lintegral_eLpNorm_lt_top {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SFinite ν] {p : ℝ}
    (hp : 1 ≤ p) {f : α × β → E} (hf : AEStronglyMeasurable f (μ.prod ν))
    (hfin : (∫⁻ y, eLpNorm (fun x ↦ f (x, y)) (ENNReal.ofReal p) μ ∂ν) < ∞) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) ν := by
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk
  have hright : (∫⁻ y, eLpNorm (fun x ↦ f (x, y)) (ENNReal.ofReal p) μ ∂ν) =
      ∫⁻ y, eLpNorm (fun x ↦ hf.mk f (x, y)) (ENNReal.ofReal p) μ ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with y hy
    exact eLpNorm_congr_ae hy
  rw [hright] at hfin
  have h := ae_integrable_of_lintegral_eLpNorm_lt_top_of_stronglyMeasurable hp
    hf.stronglyMeasurable_mk hfin
  filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk, h] with x hx hxi
  exact hxi.congr (EventuallyEq.symm hx)

end MeasureTheory
