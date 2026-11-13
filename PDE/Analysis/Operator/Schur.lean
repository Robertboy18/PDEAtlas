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
# Schur's estimate with integrability conclusions

Uniform finite bounds on the absolute row and column masses of a kernel give an
L² estimate. The raw integral exists on almost every row, and its output belongs
to L². Neither product integrability nor output integrability is assumed.

Row and column bounds are stated with nonnegative integrals, so an infinite mass
cannot satisfy them through the convention for a nonintegrable Bochner integral.
The measures are s-finite. Zero row or column bounds are allowed.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}

private theorem integrable_norm_and_integral_le_of_lintegral
    {F : Type*} [NormedAddCommGroup F] {g : X → F} {C : ℝ}
    (hg : AEStronglyMeasurable g μ) (hC : 0 ≤ C)
    (h : (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ) ≤ ENNReal.ofReal C) :
    Integrable (fun x ↦ ‖g x‖) μ ∧ (∫ x, ‖g x‖ ∂μ) ≤ C := by
  have hnonneg : 0 ≤ᵐ[μ] fun x ↦ ‖g x‖ :=
    Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hg.norm hnonneg).1
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h), ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hg.norm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal hC)

section ScalarAction

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E]
    [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
    [NormedSpace ℝ E] [CompleteSpace E] [SFinite μ] [SFinite ν]

omit [CompleteSpace E] in
private theorem integral_kernel_smul_schur_estimate
    {K : X × Y → 𝕜} {f : Y → E} {A B : ℝ}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hf : MemLp f 2 ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ᵐ x ∂μ,
      (∫⁻ y, ENNReal.ofReal ‖K (x, y)‖ ∂ν) ≤ ENNReal.ofReal A)
    (hcolumn : ∀ᵐ y ∂ν,
      (∫⁻ x, ENNReal.ofReal ‖K (x, y)‖ ∂μ) ≤ ENNReal.ofReal B) :
    (∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) • f y) ν) ∧
      MemLp (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ ∧
      lpNorm (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ ≤
        √(A * B) * lpNorm f 2 ν := by
  let Q : X × Y → ℝ := fun z ↦ ‖K z‖ * ‖f z.2‖ ^ 2
  have hQnonneg (z : X × Y) : 0 ≤ Q z := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hQmeas : AEStronglyMeasurable Q (μ.prod ν) :=
    hK.norm.mul (hf.aestronglyMeasurable.comp_snd.norm.pow 2)
  have hfsq : Integrable (fun y ↦ ‖f y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hcols : ∀ᵐ y ∂ν,
      Integrable (fun x ↦ ‖K (x, y)‖) μ ∧ (∫ x, ‖K (x, y)‖ ∂μ) ≤ B := by
    filter_upwards [hK.prodMk_right, hcolumn] with y hy hbound
    exact integrable_norm_and_integral_le_of_lintegral hy hB hbound
  have hQcolBound : ∀ᵐ y ∂ν, (∫ x, Q (x, y) ∂μ) ≤ B * ‖f y‖ ^ 2 := by
    filter_upwards [hcols] with y hy
    change (∫ x, ‖K (x, y)‖ * ‖f y‖ ^ 2 ∂μ) ≤ _
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hy.2 (sq_nonneg _)
  have hQ : Integrable Q (μ.prod ν) := by
    refine (integrable_prod_iff' hQmeas).2 ⟨hcols.mono fun y hy ↦ hy.1.mul_const (‖f y‖ ^ 2), ?_⟩
    refine (hfsq.const_mul B).mono_nonneg hQmeas.norm.prod_swap.integral_prod_right'
      (.of_forall fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) ?_
    simpa only [fun z ↦ Real.norm_of_nonneg (hQnonneg z)] using hQcolBound
  have hrows : ∀ᵐ x ∂μ,
      Integrable (fun y ↦ ‖K (x, y)‖) ν ∧ (∫ y, ‖K (x, y)‖ ∂ν) ≤ A := by
    filter_upwards [hK.prodMk_left, hrow] with x hx hbound
    exact integrable_norm_and_integral_le_of_lintegral hx hA hbound
  have hsqrt {g : Y → ℝ} (hg : Integrable g ν) (h0 : ∀ y, 0 ≤ g y) :
      MemLp (fun y ↦ √(g y)) 2 ν :=
    (memLp_two_iff_integrable_sq hg.aemeasurable.sqrt.aestronglyMeasurable).2
      (hg.congr (.of_forall fun y ↦ (Real.sq_sqrt (h0 y)).symm))
  have hpoint : ∀ᵐ x ∂μ,
      Integrable (fun y ↦ K (x, y) • f y) ν ∧
        ‖∫ y, K (x, y) • f y ∂ν‖ ^ 2 ≤ A * (∫ y, Q (x, y) ∂ν) := by
    filter_upwards [hrows, hQ.prod_right_ae, hK.prodMk_left] with x hx hQx hKx
    have hKL := hsqrt hx.1 fun y ↦ norm_nonneg (K (x, y))
    have hQL := hsqrt hQx fun y ↦ hQnonneg (x, y)
    have hfactor (y : Y) : √‖K (x, y)‖ * √(Q (x, y)) = ‖K (x, y)‖ * ‖f y‖ := by
      change √‖K (x, y)‖ * √(‖K (x, y)‖ * ‖f y‖ ^ 2) = _
      rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), ← mul_assoc,
        Real.mul_self_sqrt (norm_nonneg _)]
    have hprod : Integrable (fun y ↦ ‖K (x, y)‖ * ‖f y‖) ν :=
      (hKL.integrable_mul hQL).congr (.of_forall hfactor)
    -- Cauchy-Schwarz for `√‖K‖ · √Q`
    have hcs : (∫ y, ‖K (x, y)‖ * ‖f y‖ ∂ν) ≤
        √(∫ y, ‖K (x, y)‖ ∂ν) * √(∫ y, Q (x, y) ∂ν) := by
      have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        (.of_forall fun _ ↦ Real.sqrt_nonneg _) (.of_forall fun _ ↦ Real.sqrt_nonneg _)
        (by simpa using hKL) (by simpa using hQL)
      simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, fun y ↦ Real.sq_sqrt (norm_nonneg (K (x, y))),
        fun y ↦ Real.sq_sqrt (hQnonneg (x, y)), hfactor] using h
    have hnorm : ‖∫ y, K (x, y) • f y ∂ν‖ ≤ _ := (norm_integral_le_of_norm_le hprod
      (.of_forall fun _ ↦ norm_smul_le _ _)).trans hcs
    have hK0 : 0 ≤ ∫ y, ‖K (x, y)‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
    have hQx0 : 0 ≤ ∫ y, Q (x, y) ∂ν := integral_nonneg fun y ↦ hQnonneg (x, y)
    rw [← Real.sqrt_mul hK0] at hnorm
    exact ⟨hprod.mono' (hKx.smul hf.aestronglyMeasurable) (.of_forall fun _ ↦ norm_smul_le _ _),
      ((Real.le_sqrt (norm_nonneg _) (mul_nonneg hK0 hQx0)).1 hnorm).trans
        (mul_le_mul_of_nonneg_right hx.2 hQx0)⟩
  have hmeas : AEStronglyMeasurable (fun x ↦ ∫ y, K (x, y) • f y ∂ν) μ :=
    (hK.smul hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  have houtSq : Integrable (fun x ↦ ‖∫ y, K (x, y) • f y ∂ν‖ ^ 2) μ :=
    (hQ.integral_prod_left.const_mul A).mono_nonneg (hmeas.norm.pow 2)
      (.of_forall fun _ ↦ sq_nonneg _) (hpoint.mono fun _ hx ↦ hx.2)
  have hint : (∫ x, ‖∫ y, K (x, y) • f y ∂ν‖ ^ 2 ∂μ) ≤ (A * B) * (∫ y, ‖f y‖ ^ 2 ∂ν) :=
    calc
      _ ≤ ∫ x, A * (∫ y, Q (x, y) ∂ν) ∂μ :=
        integral_mono_ae houtSq (hQ.integral_prod_left.const_mul A)
          (hpoint.mono fun _ hx ↦ hx.2)
      _ = A * ∫ y, ∫ x, Q (x, y) ∂μ ∂ν := by
        rw [integral_const_mul, ← integral_prod Q hQ, integral_prod_symm Q hQ]
      _ ≤ A * ∫ y, B * ‖f y‖ ^ 2 ∂ν := mul_le_mul_of_nonneg_left
        (integral_mono_ae hQ.integral_prod_right (hfsq.const_mul B) hQcolBound) hA
      _ = _ := by rw [integral_const_mul, mul_assoc]
  refine ⟨hpoint.mono fun _ hx ↦ hx.1, (memLp_two_iff_integrable_sq_norm hmeas).2 houtSq, ?_⟩
  rw [lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top hmeas,
    lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow]
  exact (Real.sqrt_le_sqrt hint).trans_eq (Real.sqrt_mul (mul_nonneg hA hB) _)

omit [CompleteSpace E] in
/-- Finite absolute row and column masses give an integrable kernel product
on almost every row for each L² input. Neither bound needs to be positive. -/
theorem ae_integrable_kernel_smul_of_schur
    {K : X × Y → 𝕜} {f : Y → E} {A B : ℝ}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hf : MemLp f 2 ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ᵐ x ∂μ,
      (∫⁻ y, ENNReal.ofReal ‖K (x, y)‖ ∂ν) ≤ ENNReal.ofReal A)
    (hcolumn : ∀ᵐ y ∂ν,
      (∫⁻ x, ENNReal.ofReal ‖K (x, y)‖ ∂μ) ≤ ENNReal.ofReal B) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) • f y) ν :=
  (integral_kernel_smul_schur_estimate hK hf hA hB hrow hcolumn).1

omit [CompleteSpace E] in
/-- Schur's row and column bounds imply L² membership of the integral.
Measurability and output square integrability are derived from the kernel and input. -/
theorem MemLp.integral_kernel_smul_of_schur
    {K : X × Y → 𝕜} {f : Y → E} {A B : ℝ}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hf : MemLp f 2 ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ᵐ x ∂μ,
      (∫⁻ y, ENNReal.ofReal ‖K (x, y)‖ ∂ν) ≤ ENNReal.ofReal A)
    (hcolumn : ∀ᵐ y ∂ν,
      (∫⁻ x, ENNReal.ofReal ‖K (x, y)‖ ∂μ) ≤ ENNReal.ofReal B) :
    MemLp (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ :=
  (integral_kernel_smul_schur_estimate hK hf hA hB hrow hcolumn).2.1

omit [CompleteSpace E] in
/-- Schur's L² estimate has constant √(AB), including A=0 or B=0.
The same hypotheses give output membership, so the real norm is not totalized
from an infinite integral. -/
theorem lpNorm_integral_kernel_smul_le_of_schur
    {K : X × Y → 𝕜} {f : Y → E} {A B : ℝ}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hf : MemLp f 2 ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ᵐ x ∂μ,
      (∫⁻ y, ENNReal.ofReal ‖K (x, y)‖ ∂ν) ≤ ENNReal.ofReal A)
    (hcolumn : ∀ᵐ y ∂ν,
      (∫⁻ x, ENNReal.ofReal ‖K (x, y)‖ ∂μ) ≤ ENNReal.ofReal B) :
    lpNorm (fun x ↦ ∫ y, K (x, y) • f y ∂ν) 2 μ ≤
      √(A * B) * lpNorm f 2 ν :=
  (integral_kernel_smul_schur_estimate hK hf hA hB hrow hcolumn).2.2

end ScalarAction

end MeasureTheory
