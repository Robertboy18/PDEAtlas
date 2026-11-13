/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.Domain
import CAS.ExactTactic

/-!
# Cauchy–Schwarz bounds for weighted moments

The reciprocal-weight norm of a kernel controls its moment against a function of
finite weighted energy. A pointwise comparison of the squared kernel with the
weight supplies the kernel domain on a finite measure space.
-/

@[expose] public section

noncomputable section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The reciprocal-weight kernel norm is the exact Cauchy–Schwarz constant
for the moment. Both factors belong to ordinary `L²`. -/
theorem abs_integral_mul_le_weighted_sqrt
    {n f W : α → ℝ} (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hn : MemLp (fun x ↦ n x / √(W x)) 2 μ)
    (hf : MemLp (fun x ↦ f x * √(W x)) 2 μ) :
    |∫ x, n x * f x ∂μ| ≤
      √(∫ x, n x ^ 2 / W x ∂μ) * √(∫ x, f x ^ 2 * W x ∂μ) := by
  have heq : (∫ x, n x * f x ∂μ) =
      ∫ x, (n x / √(W x)) * (f x * √(W x)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hW] with x hx
    have hsqrt : √(W x) ≠ 0 := Real.sqrt_ne_zero'.mpr hx
    cas using hsqrt
  have hnSq : (∫ x, (n x / √(W x)) ^ 2 ∂μ) =
      ∫ x, n x ^ 2 / W x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hW] with x hx
    simp only [div_pow, Real.sq_sqrt hx.le]
  have hfSq : (∫ x, (f x * √(W x)) ^ 2 ∂μ) =
      ∫ x, f x ^ 2 * W x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hW] with x hx
    simp only [mul_pow, Real.sq_sqrt hx.le]
  rw [heq, ← hnSq, ← hfSq]
  exact abs_integral_le_integral_abs.trans (integral_abs_mul_le_sqrt_integral_sq hn hf)

/-- A bounded reciprocal-weight squared kernel is integrable on a finite measure
space. Positivity of the weight is required only almost everywhere. -/
theorem memLp_div_sqrt_of_sq_le_mul [IsFiniteMeasure μ]
    {n W : α → ℝ} {C : ℝ}
    (hn : AEStronglyMeasurable n μ) (hW : AEStronglyMeasurable W μ)
    (hpos : ∀ᵐ x ∂μ, 0 < W x)
    (hbound : ∀ᵐ x ∂μ, n x ^ 2 ≤ C * W x) :
    MemLp (fun x ↦ n x / √(W x)) 2 μ := by
  have hm : AEStronglyMeasurable (fun x ↦ n x / √(W x)) μ :=
    hn.div₀ (Real.continuous_sqrt.comp_aestronglyMeasurable hW)
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrable_const C).mono_nonneg (hm.pow 2)
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
  filter_upwards [hpos, hbound] with x hx hnx
  change (n x / √(W x)) ^ 2 ≤ C
  simp only [div_pow, Real.sq_sqrt hx.le]
  exact (div_le_iff₀ hx).mpr hnx

/-- Cancel a known kernel singularity against a lower bound for the weight.
The multiplier `r` may vanish off the measure's support. -/
theorem memLp_div_sqrt_of_mul_bound [IsFiniteMeasure μ]
    {n r W : α → ℝ} {a B : ℝ}
    (hn : AEStronglyMeasurable n μ) (hW : AEStronglyMeasurable W μ)
    (ha : 0 < a) (hr : ∀ᵐ x ∂μ, r x ≠ 0)
    (hfloor : ∀ᵐ x ∂μ, a / r x ^ 2 ≤ W x)
    (hbound : ∀ᵐ x ∂μ, |n x * r x| ≤ B) :
    MemLp (fun x ↦ n x / √(W x)) 2 μ := by
  have hpos : ∀ᵐ x ∂μ, 0 < W x := by
    filter_upwards [hr, hfloor] with x hx hfx
    exact (div_pos ha (sq_pos_of_ne_zero hx)).trans_le hfx
  apply memLp_div_sqrt_of_sq_le_mul hn hW hpos (C := B ^ 2 / a)
  filter_upwards [hr, hfloor, hbound] with x hx hfx hnx
  have hsq : (n x * r x) ^ 2 ≤ B ^ 2 :=
    (sq_abs (n x * r x)).symm.trans_le
      ((sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hnx)).mpr hnx)
  have hf := (div_le_iff₀ (sq_pos_of_ne_zero hx)).mp hfx
  have hmul := mul_le_mul_of_nonneg_left hf (sq_nonneg (n x))
  have hdivide : n x ^ 2 * a ≤ B ^ 2 * W x := by
    calc
      n x ^ 2 * a ≤ n x ^ 2 * (W x * r x ^ 2) := hmul
      _ = (n x * r x) ^ 2 * W x := by ring
      _ ≤ B ^ 2 * W x :=
        mul_le_mul_of_nonneg_right hsq ((div_pos ha (sq_pos_of_ne_zero hx)).trans_le hfx).le
  calc
    n x ^ 2 ≤ (B ^ 2 * W x) / a := (le_div_iff₀ ha).mpr hdivide
    _ = (B ^ 2 / a) * W x := by ring

end MeasureTheory
