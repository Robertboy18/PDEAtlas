/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.FluxNormalization
import PDE.FDeriv.Euclidean.Distance
import PDE.FDeriv.Euclidean.Norm

/-!
# Differences of the fundamental-solution gradient

The radial derivative of the canonical kernel gives its full gradient in every
ambient dimension at least two, including the logarithmic planar case. Comparing
inverse powers of the two radii controls a gradient difference using only endpoint
separation from the pole. The segment between the points may pass through the pole.
-/

@[expose] public noncomputable section

namespace PotentialTheory

open PDE.Analysis
open scoped Gradient

variable {n : ℕ} [Fact (0 < n)]

/-- The gradient of the canonical Laplace kernel away from its pole. -/
theorem gradient_fundamentalSolution (hn : 2 ≤ n) {x : ℝ^n} (hx : x ≠ 0) :
    ∇ (fundamentalSolution n) x =
      (-1 / (unitSphereArea n * ‖x‖ ^ n)) • x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let ω : Metric.sphere (0 : ℝ^n) 1 :=
    ⟨‖x‖⁻¹ • x, by simp [norm_smul, hr.ne']⟩
  have hω : ‖(ω : ℝ^n)‖ = 1 := by simp
  have hω0 : (ω : ℝ^n) ≠ 0 := by intro h; simp [h] at hω
  have hlin : DifferentiableAt ℝ (fun r : ℝ ↦ r • (ω : ℝ^n)) ‖x‖ :=
    differentiableAt_id.smul_const _
  have hΦ : DifferentiableAt ℝ (fundamentalSolution n) (‖x‖ • (ω : ℝ^n)) :=
    (contDiffAt_fundamentalSolution n _ (smul_ne_zero hr.ne' hω0)).differentiableAt
      (by simp)
  have hF : DifferentiableAt ℝ
      (fun r : ℝ ↦ fundamentalSolution n (r • (ω : ℝ^n))) ‖x‖ := by
    simpa only [Function.comp_def] using hΦ.comp ‖x‖ hlin
  have hFD := hF.hasDerivAt
  rw [deriv_fundamentalSolution_smul hn ω hr] at hFD
  have h := hFD.comp_hasFDerivAt x (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx)
  have hkernel : (fun y : ℝ^n ↦ fundamentalSolution n (‖y‖ • (ω : ℝ^n))) =
      fundamentalSolution n := by
    funext y
    apply fundamentalSolution_eq_of_norm_eq
    simp [norm_smul, hω]
  simp only [Function.comp_def] at h
  rw [hkernel] at h
  apply (InnerProductSpace.toDual ℝ (ℝ^n)).injective
  rw [toDual_gradient, h.fderiv]
  ext v
  simp only [smul_apply, innerSL_apply_apply,
    real_inner_smul_left, InnerProductSpace.toDual_apply_apply]
  have hp : ‖x‖ ^ n = ‖x‖ ^ (n - 1) * ‖x‖ := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [hp]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem abs_inv_pow_sub_inv_pow_le (k : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    |(a ^ k)⁻¹ - (b ^ k)⁻¹| ≤ (k : ℝ) * (a ^ (k + 1))⁻¹ * |a - b| := by
  have hf (z : ℝ) (hz : z ∈ Set.Ici a) :
      DifferentiableAt ℝ (fun r : ℝ ↦ (dist r 0 ^ k)⁻¹) z :=
    (EuclideanDistance.hasFDerivAt_inv_dist_pow (k := k)
      (ne_of_gt (ha.trans_le hz))).differentiableAt
  have hbnd (z : ℝ) (hz : z ∈ Set.Ici a) :
      ‖fderiv ℝ (fun r : ℝ ↦ (dist r 0 ^ k)⁻¹) z‖ ≤
        (k : ℝ) * (a ^ (k + 1))⁻¹ := by
    rw [(EuclideanDistance.hasFDerivAt_inv_dist_pow (k := k)
      (ne_of_gt (ha.trans_le hz))).fderiv]
    apply EuclideanDistance.norm_invDistPowFDerivFormula_le_of_le_dist k ha
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (ha.trans_le hz),
      Set.mem_Ici] using hz
  have h := (convex_Ici a).norm_image_sub_le_of_norm_fderiv_le hf hbnd
    (le_refl a) hab
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos ha,
    abs_of_pos (ha.trans_le hab), abs_sub_comm] using h

omit [Fact (0 < n)] in
private theorem norm_inv_norm_pow_smul_sub_le_of_norm_le {a b : ℝ^n}
    (ha : 0 < ‖a‖) (hab : ‖a‖ ≤ ‖b‖) :
    ‖(‖a‖ ^ n)⁻¹ • a - (‖b‖ ^ n)⁻¹ • b‖ ≤
      ((n : ℝ) + 1) * ‖a - b‖ / ‖a‖ ^ n := by
  have hi : (‖b‖ ^ n)⁻¹ ≤ (‖a‖ ^ n)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (pow_pos ha n) (pow_le_pow_left₀ ha.le hab n)
  have hrad := abs_inv_pow_sub_inv_pow_le n ha hab
  have hdist := abs_norm_sub_norm_le a b
  have hscalar : |(‖a‖ ^ n)⁻¹ - (‖b‖ ^ n)⁻¹| * ‖a‖ ≤
      (n : ℝ) * (‖a‖ ^ n)⁻¹ * ‖a - b‖ := by
    calc
      _ ≤ ((n : ℝ) * (‖a‖ ^ (n + 1))⁻¹ * |‖a‖ - ‖b‖|) * ‖a‖ :=
        mul_le_mul_of_nonneg_right hrad (norm_nonneg a)
      _ ≤ ((n : ℝ) * (‖a‖ ^ (n + 1))⁻¹ * ‖a - b‖) * ‖a‖ := by
        gcongr
      _ = (n : ℝ) * (‖a‖ ^ n)⁻¹ * ‖a - b‖ := by
        rw [pow_succ]
        field_simp
  have hsplit : (‖a‖ ^ n)⁻¹ • a - (‖b‖ ^ n)⁻¹ • b =
      (‖b‖ ^ n)⁻¹ • (a - b) + ((‖a‖ ^ n)⁻¹ - (‖b‖ ^ n)⁻¹) • a := by
    simp only [smul_sub, sub_smul]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖(‖b‖ ^ n)⁻¹ • (a - b)‖ +
        ‖((‖a‖ ^ n)⁻¹ - (‖b‖ ^ n)⁻¹) • a‖ := norm_add_le _ _
    _ = (‖b‖ ^ n)⁻¹ * ‖a - b‖ + |(‖a‖ ^ n)⁻¹ - (‖b‖ ^ n)⁻¹| * ‖a‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg b) n))]
    _ ≤ (‖a‖ ^ n)⁻¹ * ‖a - b‖ + (n : ℝ) * (‖a‖ ^ n)⁻¹ * ‖a - b‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hi (norm_nonneg _)) hscalar
    _ = ((n : ℝ) + 1) * ‖a - b‖ / ‖a‖ ^ n := by ring

/-- Endpoint separation controls a gradient difference even when the segment
between the points passes through the pole. -/
theorem norm_gradient_fundamentalSolution_sub_le (hn : 2 ≤ n)
    {a b : ℝ^n} {ρ : ℝ} (hρ : 0 < ρ) (ha : ρ ≤ ‖a‖) (hb : ρ ≤ ‖b‖) :
    ‖∇ (fundamentalSolution n) a - ∇ (fundamentalSolution n) b‖ ≤
      (((n : ℝ) + 1) / unitSphereArea n) * ‖a - b‖ / ρ ^ n := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (hρ.trans_le ha)
  have hb0 : b ≠ 0 := norm_pos_iff.mp (hρ.trans_le hb)
  have hraw : ‖(‖a‖ ^ n)⁻¹ • a - (‖b‖ ^ n)⁻¹ • b‖ ≤
      ((n : ℝ) + 1) * ‖a - b‖ / ρ ^ n := by
    rcases le_total ‖a‖ ‖b‖ with hab | hba
    · exact (norm_inv_norm_pow_smul_sub_le_of_norm_le (hρ.trans_le ha) hab).trans
        (div_le_div_of_nonneg_left (by positivity) (pow_pos hρ n)
          (pow_le_pow_left₀ hρ.le ha n))
    · rw [norm_sub_rev]
      have h := norm_inv_norm_pow_smul_sub_le_of_norm_le (hρ.trans_le hb) hba
      rw [norm_sub_rev b a] at h
      exact h.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hρ n)
        (pow_le_pow_left₀ hρ.le hb n))
  rw [gradient_fundamentalSolution hn ha0, gradient_fundamentalSolution hn hb0]
  have hsplit : (-1 / (unitSphereArea n * ‖a‖ ^ n)) • a -
      (-1 / (unitSphereArea n * ‖b‖ ^ n)) • b =
      (-1 / unitSphereArea n) • ((‖a‖ ^ n)⁻¹ • a - (‖b‖ ^ n)⁻¹ • b) := by
    simp only [div_eq_mul_inv, mul_inv_rev, smul_sub, smul_smul]
    congr 1 <;> congr 1 <;> ring
  rw [hsplit, norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_one,
    abs_of_pos (unitSphereArea_pos (n := n))]
  calc
    _ ≤ (1 / unitSphereArea n) * (((n : ℝ) + 1) * ‖a - b‖ / ρ ^ n) :=
      mul_le_mul_of_nonneg_left hraw
        (div_nonneg zero_le_one (unitSphereArea_pos (n := n)).le)
    _ = (((n : ℝ) + 1) / unitSphereArea n) * ‖a - b‖ / ρ ^ n := by ring

/-- The paired fundamental-gradient kernel has one factor of the normal
height under explicit separation of its two poles from the integration point. -/
theorem norm_paired_gradient_fundamentalSolution_le (hn : 2 ≤ n)
    {x y ν : ℝ^n} (hν : ‖ν‖ = 1) {t : ℝ} (ht : 0 < t)
    (hminus : (t + ‖x - y‖) / 2 ≤ ‖x - t • ν - y‖)
    (hplus : (t + ‖x - y‖) / 2 ≤ ‖x + t • ν - y‖) :
    ‖∇ (fundamentalSolution n) (x - t • ν - y) -
        ∇ (fundamentalSolution n) (x + t • ν - y)‖ ≤
      (2 ^ (n + 1) * ((n : ℝ) + 1) / unitSphereArea n) * t /
        (t + ‖x - y‖) ^ n := by
  have hden : 0 < t + ‖x - y‖ := add_pos_of_pos_of_nonneg ht (norm_nonneg _)
  have h := norm_gradient_fundamentalSolution_sub_le hn
    (div_pos hden (by norm_num)) hminus hplus
  have hdiff : x - t • ν - y - (x + t • ν - y) = (-(2 * t)) • ν := by
    rw [neg_smul, mul_smul, two_smul]
    abel
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity : 0 < 2 * t),
    hν, mul_one] at h
  refine h.trans_eq ?_
  rw [div_pow, pow_succ (2 : ℝ) n]
  field_simp

end PotentialTheory
