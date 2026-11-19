/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Square-integrable kernels on L²

A square-integrable scalar kernel sends L² functions to L² functions. The proof
first establishes integrability along almost every row, then integrates the
Cauchy–Schwarz bound. The output may take values in any real normed space with a
bounded action of the kernel's normed scalar ring.

These statements use Mathlib's totalized Bochner integral. If the codomain is not
complete, that integral is defined to be zero.

The measures are s-finite. All statements concern measurable representatives.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}

/-- Almost every row of a square-integrable kernel is square-integrable.
Only the measure on the row variable needs to be s-finite. -/
theorem MemLp.ae_memLp_prod_right_two
    {F : Type*} [NormedAddCommGroup F] [SFinite ν]
    {K : X × Y → F} (hK : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ K (x, y)) 2 ν := by
  have hsq : Integrable (fun z ↦ ‖K z‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).1 hK
  have hrows :=
    ((integrable_prod_iff hsq.aestronglyMeasurable).1 hsq).1
  filter_upwards [hK.aestronglyMeasurable.prodMk_left, hrows] with x hx hxsq
  exact (memLp_two_iff_integrable_sq_norm hx).2 hxsq

section ScalarAction

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E]
    [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- A square-integrable kernel and an L² input have an integrable product along
almost every row. This is Hölder's inequality with exponents two and two. -/
theorem MemLp.ae_integrable_kernel_smul [SFinite ν]
    {K : X × Y → 𝕜} {f : Y → E}
    (hK : MemLp K 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) • f y) ν := by
  filter_upwards [hK.ae_memLp_prod_right_two] with x hx
  exact memLp_one_iff_integrable.1 (hx.smul hf : MemLp _ 1 ν)

variable [NormedSpace ℝ E]

private theorem integral_kernel_smul_estimate [SFinite μ] [SFinite ν]
    {K : X × Y → 𝕜} {f : Y → E}
    (hK : MemLp K 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    MemLp (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ ∧
      lpNorm (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ ≤
        lpNorm K 2 (μ.prod ν) * lpNorm f 2 ν := by
  have hKsq : Integrable (fun z ↦ ‖K z‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).1 hK
  have hrowSq : Integrable (fun x ↦ ∫ y, ‖K (x, y)‖ ^ 2 ∂ν) μ :=
    hKsq.integral_prod_left
  have hmeas :
      AEStronglyMeasurable (fun x ↦ ∫ y, K (x, y) • f y ∂ν) μ :=
    (hK.aestronglyMeasurable.smul
      hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  have hpoint :
      ∀ᵐ x ∂μ, ‖∫ y, K (x, y) • f y ∂ν‖ ^ 2 ≤
        (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) * (∫ y, ‖f y‖ ^ 2 ∂ν) := by
    filter_upwards [hK.ae_memLp_prod_right_two] with x hx
    have hprod : Integrable (fun y ↦ ‖K (x, y)‖ * ‖f y‖) ν := by
      exact (hx.norm.integrable_mul hf.norm).congr
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    have hcs :
        (∫ y, ‖K (x, y)‖ * ‖f y‖ ∂ν) ≤
          √(∫ y, ‖K (x, y)‖ ^ 2 ∂ν) *
            √(∫ y, ‖f y‖ ^ 2 ∂ν) := by
      have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (f := fun y ↦ ‖K (x, y)‖) (g := fun y ↦ ‖f y‖)
        (by simpa using hx.norm) (by simpa using hf.norm)
      simpa only [norm_norm, Real.rpow_two, ← Real.sqrt_eq_rpow] using h
    have hnorm :
        ‖∫ y, K (x, y) • f y ∂ν‖ ≤
          √(∫ y, ‖K (x, y)‖ ^ 2 ∂ν) *
            √(∫ y, ‖f y‖ ^ 2 ∂ν) :=
      (norm_integral_le_of_norm_le hprod
        (Filter.Eventually.of_forall fun y ↦ norm_smul_le _ _)).trans hcs
    calc
      ‖∫ y, K (x, y) • f y ∂ν‖ ^ 2 ≤
          (√(∫ y, ‖K (x, y)‖ ^ 2 ∂ν) *
            √(∫ y, ‖f y‖ ^ 2 ∂ν)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _))).2 hnorm
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt (integral_nonneg fun y ↦ sq_nonneg _),
          Real.sq_sqrt (integral_nonneg fun y ↦ sq_nonneg _)]
  have hmajorant := hrowSq.mul_const (∫ y, ‖f y‖ ^ 2 ∂ν)
  have houtSq :
      Integrable (fun x ↦ ‖∫ y, K (x, y) • f y ∂ν‖ ^ 2) μ :=
    hmajorant.mono' (hmeas.norm.pow 2) (hpoint.mono fun x hx ↦ by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg ‖∫ y, K (x, y) • f y ∂ν‖)] using hx)
  have hout := (memLp_two_iff_integrable_sq_norm hmeas).2 houtSq
  have hint :
      (∫ x, ‖∫ y, K (x, y) • f y ∂ν‖ ^ 2 ∂μ) ≤
        (∫ z, ‖K z‖ ^ 2 ∂μ.prod ν) * (∫ y, ‖f y‖ ^ 2 ∂ν) := by
    calc
      _ ≤ ∫ x, (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) *
          (∫ y, ‖f y‖ ^ 2 ∂ν) ∂μ :=
        integral_mono_ae houtSq hmajorant hpoint
      _ = _ := by
        rw [integral_mul_const, ← integral_prod (fun z ↦ ‖K z‖ ^ 2) hKsq]
  refine ⟨hout, ?_⟩
  rw [lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top hmeas,
    lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
      hK.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow]
  exact (Real.sqrt_le_sqrt hint).trans_eq
    (Real.sqrt_mul (integral_nonneg fun z ↦ sq_nonneg _) _)

/-- The totalized Bochner integral against an L² scalar kernel has L² output.
The measurability and finite square integral of the output are conclusions.
If `E` is not complete, the integral is zero. -/
theorem MemLp.integral_kernel_smul [SFinite μ] [SFinite ν]
    {K : X × Y → 𝕜} {f : Y → E}
    (hK : MemLp K 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    MemLp (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ :=
  (integral_kernel_smul_estimate hK hf).1

/-- The L² bound is the L² norm of the kernel on the product measure.
The input and kernel membership hypotheses ensure finite norms. For an incomplete
codomain, the output integral is zero by totalization. -/
theorem eLpNorm_integral_kernel_smul_le [SFinite μ] [SFinite ν]
    {K : X × Y → 𝕜} {f : Y → E}
    (hK : MemLp K 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    eLpNorm (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ ≤
      eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν := by
  obtain ⟨hout, hbound⟩ := integral_kernel_smul_estimate hK hf
  rw [← ofReal_lpNorm hout, ← ofReal_lpNorm hK, ← ofReal_lpNorm hf,
    ← ENNReal.ofReal_mul lpNorm_nonneg]
  exact ENNReal.ofReal_le_ofReal hbound

end ScalarAction

section Weighted

/-- Integrable rows of the conjugated kernel recover integrable raw rows when
both weights are positive almost everywhere. No product integrability is needed. -/
theorem ae_integrable_weighted_kernel
    {K : X × Y → ℝ} {wOut : X → ℝ} {wIn f : Y → ℝ}
    (hOut : ∀ᵐ x ∂μ, 0 < wOut x) (hIn : ∀ᵐ y ∂ν, 0 < wIn y)
    (hrows : ∀ᵐ x ∂μ, Integrable (fun y ↦
      (√(wOut x) * K (x, y) / √(wIn y)) •
        (√(wIn y) * f y)) ν) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) * f y) ν := by
  filter_upwards [hrows, hOut] with x hx hox
  have ho : √(wOut x) ≠ 0 := (Real.sqrt_pos.2 hox).ne'
  have hscaled := hx.const_mul (√(wOut x))⁻¹
  apply hscaled.congr
  filter_upwards [hIn] with y hiy
  have hi : √(wIn y) ≠ 0 := (Real.sqrt_pos.2 hiy).ne'
  change (√(wOut x))⁻¹ *
    ((√(wOut x) * K (x, y) / √(wIn y)) *
      (√(wIn y) * f y)) = K (x, y) * f y
  rw [← mul_assoc (√(wOut x) * K (x, y) / √(wIn y))
      (√(wIn y)) (f y),
    div_mul_cancel₀ _ hi, mul_assoc (√(wOut x)) (K (x, y)) (f y),
    inv_mul_cancel_left₀ ho]

omit [MeasurableSpace X] in
/-- Conjugation by the square roots of weights preserves the raw integral.
Only the input weight must be positive for this identity. Raw row integrability
is a separate conclusion of `ae_integrable_weighted_kernel`. -/
theorem integral_weighted_kernel_eq
    {K : X × Y → ℝ} {wOut : X → ℝ} {wIn f : Y → ℝ}
    (hIn : ∀ᵐ y ∂ν, 0 < wIn y) (x : X) :
    (∫ y, (√(wOut x) * K (x, y) / √(wIn y)) •
      (√(wIn y) * f y) ∂ν) =
      √(wOut x) * (∫ y, K (x, y) * f y ∂ν) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hIn] with y hiy
  have hi : √(wIn y) ≠ 0 := (Real.sqrt_pos.2 hiy).ne'
  change (√(wOut x) * K (x, y) / √(wIn y)) *
    (√(wIn y) * f y) = √(wOut x) * (K (x, y) * f y)
  rw [← mul_assoc, div_mul_cancel₀ _ hi, mul_assoc]

variable [SFinite ν]

/-- Conjugating by square roots of positive weights gives a weighted L² estimate.
The conclusion includes raw row integrability and weighted output membership.
Thus the norm bound concerns the raw integral, without using zeros of the
output weight to hide nonintegrable rows. No operator bound is assumed. -/
theorem exists_memLp_weighted_integral_kernel_bound [SFinite μ]
    {K : X × Y → ℝ} {wOut : X → ℝ} {wIn f : Y → ℝ}
    (hOut : ∀ᵐ x ∂μ, 0 < wOut x) (hIn : ∀ᵐ y ∂ν, 0 < wIn y)
    (hK : MemLp (fun z ↦ √(wOut z.1) * K z /
      √(wIn z.2)) 2 (μ.prod ν))
    (hf : MemLp (fun y ↦ √(wIn y) * f y) 2 ν) :
    ∃ hout : MemLp
        (fun x ↦ √(wOut x) * (∫ y, K (x, y) * f y ∂ν)) 2 μ,
      (∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) * f y) ν) ∧
      ‖hout.toLp (fun x ↦ √(wOut x) * (∫ y, K (x, y) * f y ∂ν))‖ ≤
        lpNorm (fun z ↦ √(wOut z.1) * K z /
          √(wIn z.2)) 2 (μ.prod ν) *
            ‖hf.toLp (fun y ↦ √(wIn y) * f y)‖ := by
  have heq :
      (fun x ↦ ∫ y, (√(wOut x) * K (x, y) /
        √(wIn y)) • (√(wIn y) * f y) ∂ν) =ᵐ[μ]
      (fun x ↦ √(wOut x) * (∫ y, K (x, y) * f y ∂ν)) :=
    Filter.Eventually.of_forall (integral_weighted_kernel_eq hIn)
  have hout := MemLp.ae_eq heq (hK.integral_kernel_smul hf)
  refine ⟨hout, ae_integrable_weighted_kernel hOut hIn
    (hK.ae_integrable_kernel_smul hf), ?_⟩
  rw [Lp.norm_toLp, Lp.norm_toLp]
  have hbound := eLpNorm_integral_kernel_smul_le hK hf
  rw [eLpNorm_congr_ae heq] at hbound
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hK.eLpNorm_ne_top hf.eLpNorm_ne_top) hbound
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm] using hreal

end Weighted

end MeasureTheory
