/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.WeightedDerivative

/-!
# Scalar multiplication and finite sums of weighted radial profiles

The weighted transform commutes with scalar multiplication without a
differentiability hypothesis, by the corresponding rule for the totalized
real derivative. It commutes with finite sums at the finite regularity
needed to define its successive derivatives. This includes the origin, where
the recurrence removes division by the radius.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

/-- A constant scalar commutes with the radial transform, including when
the totalized derivative is zero at a nondifferentiable point. -/
theorem oddRadialTransform_const_mul (k : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    oddRadialTransform k (fun r ↦ c * f r) =
      fun r ↦ c * oddRadialTransform k f r := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [oddRadialTransform_succ', ih, oddRadialTransform_succ']
      funext r
      simp only [evansRadialDerivative, deriv_const_mul_field, mul_div_assoc]

/-- Weighted radial transforms commute with finite sums of `C^k` profiles. -/
theorem oddRadialTransform_pow_mul_sum
    {ι : Type*} (k : ℕ) (a : Finset ι) {φ : ι → ℝ → ℝ}
    (hφ : ∀ i ∈ a, ContDiff ℝ k (φ i)) (r : ℝ) :
    oddRadialTransform k (fun s ↦ s ^ (2 * k + 1) * ∑ i ∈ a, φ i s) r =
      ∑ i ∈ a, oddRadialTransform k (fun s ↦ s ^ (2 * k + 1) * φ i s) r := by
  induction k generalizing φ with
  | zero => simp [Finset.mul_sum]
  | succ k ih =>
      let ψ : ι → ℝ → ℝ := fun i s ↦
        (2 * k + 3 : ℝ) * φ i s + s * deriv (φ i) s
      have hφ₁ (i : ι) (hi : i ∈ a) : ContDiff ℝ 1 (φ i) :=
        (hφ i hi).of_le (by norm_cast; omega)
      have hψ (i : ι) (hi : i ∈ a) : ContDiff ℝ k (ψ i) :=
        (contDiff_const.mul ((hφ i hi).of_le (by norm_cast; omega))).add
          (contDiff_id.mul ((hφ i hi).deriv'))
      have hsum : ContDiff ℝ 1 (fun s ↦ ∑ i ∈ a, φ i s) :=
        ContDiff.sum hφ₁
      have he : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [he, oddRadialTransform_step k hsum]
      have hsumψ :
          (fun s ↦ s ^ (2 * k + 1) *
            ((2 * k + 3 : ℝ) * ∑ i ∈ a, φ i s +
              s * deriv (fun t ↦ ∑ i ∈ a, φ i t) s)) =
          (fun s ↦ s ^ (2 * k + 1) * ∑ i ∈ a, ψ i s) := by
        funext s
        rw [deriv_fun_sum (fun i hi ↦ (hφ₁ i hi).differentiable one_ne_zero s)]
        simp only [ψ, Finset.sum_add_distrib, Finset.mul_sum]
      rw [hsumψ, ih hψ]
      apply Finset.sum_congr rfl
      intro i hi
      exact (congrFun (oddRadialTransform_step k (hφ₁ i hi)) r).symm

end PDE.Analysis
