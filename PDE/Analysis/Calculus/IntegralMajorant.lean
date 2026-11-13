/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integrals of affine majorants

For a function `q ≥ 0` integrable between `a` and `b` and constants `A, B ≥ 0`, a function
bounded by `A + B q` between `a` and `b` has integral at most `A |b - a| + B |∫ₐᵇ q|`.

## Main results

* `abs_integral_const_add_mul`: `|∫ₐᵇ (A + B q)| = A |b - a| + B |∫ₐᵇ q|`.
* `norm_integral_le_const_add_mul`: a function bounded by `A + B q` between `a` and `b` has
  integral at most `A |b - a| + B |∫ₐᵇ q|`.
* `abs_integral_le_of_mem_uIcc`: `|∫ₐʳ q| ≤ |∫ₐᵇ q|` for every `r` between `a` and `b`.
* `abs_integral_comp_abs`: `|∫₀ᵗ P(|r|) dr| = ∫₀^{|t|} P` for `P ≥ 0`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis

variable {q : ℝ → ℝ} {a b : ℝ}

/-- For `q ≥ 0` integrable between `a` and `b` and `A, B ≥ 0`,
`|∫ₐᵇ (A + B q)| = A |b - a| + B |∫ₐᵇ q|`. -/
theorem abs_integral_const_add_mul (hq : IntervalIntegrable q volume a b)
    (hq0 : ∀ r ∈ uIcc a b, 0 ≤ q r) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |∫ r in a..b, (A + B * q r)| = A * |b - a| + B * |∫ r in a..b, q r| := by
  rw [intervalIntegral.integral_add intervalIntegrable_const (hq.const_mul B),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
  rcases le_total a b with hab | hba
  · have h1 : 0 ≤ ∫ r in a..b, q r := intervalIntegral.integral_nonneg hab fun r hr ↦
      hq0 r (by rw [uIcc_of_le hab]; exact hr)
    have h2 : 0 ≤ b - a := sub_nonneg.mpr hab
    rw [abs_of_nonneg (add_nonneg (mul_nonneg h2 hA) (mul_nonneg hB h1)), abs_of_nonneg h1,
      abs_of_nonneg h2]
    ring
  · have h1 : ∫ r in a..b, q r ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hba fun r hr ↦
        hq0 r (by rw [uIcc_of_ge hba]; exact hr))
    have h2 : b - a ≤ 0 := sub_nonpos.mpr hba
    rw [abs_of_nonpos (add_nonpos (mul_nonpos_of_nonpos_of_nonneg h2 hA)
      (mul_nonpos_of_nonneg_of_nonpos hB h1)), abs_of_nonpos h1, abs_of_nonpos h2]
    ring

/-- A function bounded between `a` and `b` by `A + B q`, with `q ≥ 0` integrable there and
`A, B ≥ 0`, has integral at most `A |b - a| + B |∫ₐᵇ q|`. -/
theorem norm_integral_le_const_add_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hq : IntervalIntegrable q volume a b) (hq0 : ∀ r ∈ uIcc a b, 0 ≤ q r)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : ∀ r ∈ uIcc a b, ‖f r‖ ≤ A + B * q r) :
    ‖∫ r in a..b, f r‖ ≤ A * |b - a| + B * |∫ r in a..b, q r| := by
  rw [← abs_integral_const_add_mul hq hq0 hA hB]
  exact intervalIntegral.norm_integral_le_abs_of_norm_le
    ((ae_restrict_iff' measurableSet_uIoc).mpr
      (Filter.Eventually.of_forall fun r hr ↦ hf r (uIoc_subset_uIcc hr)))
    (intervalIntegrable_const.add (hq.const_mul B))

/-- For `q ≥ 0` integrable between `a` and `b`, `|∫ₐʳ q| ≤ |∫ₐᵇ q|` for every `r` between `a`
and `b`. -/
theorem abs_integral_le_of_mem_uIcc (hq : IntervalIntegrable q volume a b)
    (hq0 : ∀ r ∈ uIcc a b, 0 ≤ q r) {r : ℝ} (hr : r ∈ uIcc a b) :
    |∫ s in a..r, q s| ≤ |∫ s in a..b, q s| := by
  have har : IntervalIntegrable q volume a r := hq.mono_set (uIcc_subset_uIcc_left hr)
  have hrb : IntervalIntegrable q volume r b := hq.mono_set (uIcc_subset_uIcc_right hr)
  rw [← intervalIntegral.integral_add_adjacent_intervals har hrb]
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hr hq0
    have h1 : 0 ≤ ∫ s in a..r, q s := intervalIntegral.integral_nonneg hr.1 fun s hs ↦
      hq0 s ⟨hs.1, hs.2.trans hr.2⟩
    have h2 : 0 ≤ ∫ s in r..b, q s := intervalIntegral.integral_nonneg hr.2 fun s hs ↦
      hq0 s ⟨hr.1.trans hs.1, hs.2⟩
    rw [abs_of_nonneg h1, abs_of_nonneg (add_nonneg h1 h2)]
    linarith
  · rw [uIcc_of_ge hba] at hr hq0
    have h1 : ∫ s in a..r, q s ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hr.2 fun s hs ↦
        hq0 s ⟨hr.1.trans hs.1, hs.2⟩)
    have h2 : ∫ s in r..b, q s ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hr.1 fun s hs ↦
        hq0 s ⟨hs.1, hs.2.trans hr.2⟩)
    rw [abs_of_nonpos h1, abs_of_nonpos (add_nonpos h1 h2)]
    linarith

/-- For `P ≥ 0` on `[0, |t|]`, `|∫₀ᵗ P(|r|) dr| = ∫₀^{|t|} P`. -/
theorem abs_integral_comp_abs {P : ℝ → ℝ} {t : ℝ} (hP : ∀ r ∈ Icc 0 (|t|), 0 ≤ P r) :
    |∫ r in (0 : ℝ)..t, P (|r|)| = ∫ r in (0 : ℝ)..(|t|), P r := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht] at hP ⊢
    have h : ∫ r in (0 : ℝ)..t, P (|r|) = ∫ r in (0 : ℝ)..t, P r :=
      intervalIntegral.integral_congr fun r hr ↦ by
        rw [uIcc_of_le ht] at hr
        simp only [abs_of_nonneg hr.1]
    rw [h, abs_of_nonneg (intervalIntegral.integral_nonneg ht hP)]
  · rw [abs_of_nonpos ht] at hP ⊢
    have h : ∫ r in (0 : ℝ)..t, P (|r|) = ∫ r in (0 : ℝ)..t, P (-r) :=
      intervalIntegral.integral_congr fun r hr ↦ by
        rw [uIcc_of_ge ht] at hr
        simp only [abs_of_nonpos hr.2]
    have hn : 0 ≤ -t := neg_nonneg.mpr ht
    rw [h, intervalIntegral.integral_comp_neg (fun r ↦ P r), neg_zero,
      intervalIntegral.integral_symm, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg hn hP)]

/-- Replacing the integrand of a Grönwall bound by an integrable majorant. -/
theorem le_of_le_integral_majorant {δ e X b r : ℝ} {g m : ℝ → ℝ} (hr : r ∈ Icc 0 b)
    (hg : ContinuousOn g (Icc 0 b)) (hm : IntervalIntegrable m volume 0 r)
    (hgm : ∀ ρ ∈ Icc 0 r, g ρ ≤ m ρ) (he : 0 ≤ e) (hX : X ≤ (δ + ∫ ρ in (0)..r, g ρ) * e) :
    X ≤ (δ + ∫ ρ in (0)..r, m ρ) * e :=
  hX.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl (intervalIntegral.integral_mono_on hr.1
    ((hg.mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc hr.1) hm hgm)) he)

end PDE.Analysis
