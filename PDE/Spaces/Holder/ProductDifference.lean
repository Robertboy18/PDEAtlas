/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.DirectionalQuotient

/-!
# Differences of products at two points

Bookkeeping for two-point estimates of products, following Chen and Hou (Part I, (5.38) and the
nonlinear Hölder estimates of Section 5.9.3; Supplementary material I, (8.17), (8.27) and (8.49)).
For a finite sum of products in the plane, both the rectangular path estimate `boxBound` and the sum
of the endpoint values bound the actual difference of each product; the minimum is taken product by
product.

## Main results

* `abs_mul_sub_mul_le_add`: `|a₁ b₁ - a₂ b₂| ≤ |a₁ - a₂| |b₂| + |a₁| |b₁ - b₂|`, the splitting
  with the coefficient of `δb` at the first point (Supplementary material I, (8.27)).
* `abs_mul_sub_mul_le_max_add_min`:
  `|a₁ b₁ - a₂ b₂| ≤ max(|a₁|, |a₂|) |b₁ - b₂| + |a₁ - a₂| min(|b₁|, |b₂|)`, the splitting that
  puts `δa` against the smaller endpoint value of `b` (Supplementary material I, Section 8.5.2,
  (8.49)).
* `abs_sum_mul_sub_le`: the difference of a finite sum of products at two points is at most the
  sum over the products of the smaller of `boxBound` and the sum of the endpoint values.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, (5.38) and Section 5.9.3;
  Supplementary material I (in the same PDF), (8.17), (8.27) and Section 8.5.2, (8.49).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Finset

namespace HolderSpace

/-- The splitting `a₁ b₁ - a₂ b₂ = (a₁ - a₂) b₂ + a₁ (b₁ - b₂)` in absolute value. -/
theorem abs_mul_sub_mul_le_add (a₁ a₂ b₁ b₂ : ℝ) :
    |a₁ * b₁ - a₂ * b₂| ≤ |a₁ - a₂| * |b₂| + |a₁| * |b₁ - b₂| := by
  calc |a₁ * b₁ - a₂ * b₂| = |(a₁ - a₂) * b₂ + a₁ * (b₁ - b₂)| := by ring_nf
    _ ≤ |(a₁ - a₂) * b₂| + |a₁ * (b₁ - b₂)| := abs_add_le _ _
    _ = |a₁ - a₂| * |b₂| + |a₁| * |b₁ - b₂| := by rw [abs_mul, abs_mul]

/-- **The smaller-endpoint splitting**: `|a₁ b₁ - a₂ b₂| ≤ max(|a₁|, |a₂|) |b₁ - b₂| +
|a₁ - a₂| min(|b₁|, |b₂|)`. -/
theorem abs_mul_sub_mul_le_max_add_min (a₁ a₂ b₁ b₂ : ℝ) :
    |a₁ * b₁ - a₂ * b₂| ≤ max |a₁| |a₂| * |b₁ - b₂| + |a₁ - a₂| * min |b₁| |b₂| := by
  rcases le_total |b₂| |b₁| with h | h
  · rw [min_eq_right h]
    calc |a₁ * b₁ - a₂ * b₂| ≤ |a₁ - a₂| * |b₂| + |a₁| * |b₁ - b₂| :=
          abs_mul_sub_mul_le_add a₁ a₂ b₁ b₂
      _ ≤ max |a₁| |a₂| * |b₁ - b₂| + |a₁ - a₂| * |b₂| := by
          rw [add_comm]
          gcongr
          exact le_max_left _ _
  · rw [min_eq_left h]
    calc |a₁ * b₁ - a₂ * b₂| = |a₂ * b₂ - a₁ * b₁| := abs_sub_comm _ _
      _ ≤ |a₂ - a₁| * |b₁| + |a₂| * |b₂ - b₁| := abs_mul_sub_mul_le_add a₂ a₁ b₂ b₁
      _ ≤ max |a₁| |a₂| * |b₁ - b₂| + |a₁ - a₂| * |b₁| := by
          rw [add_comm, abs_sub_comm a₂, abs_sub_comm b₂]
          gcongr
          exact le_max_right _ _

/-- **Differences of a sum of products** in the plane: for any finite family of products
`p_m q_m`, the difference at two points is at most `∑ₘ min(δ_□(p_m, q_m, x, z, x - z),
|p_m(x) q_m(x)| + |p_m(z) q_m(z)|)`. -/
theorem abs_sum_mul_sub_le {ι : Type*} (s : Finset ι) (α : ℝ) (p q : ι → ℝ^2 → ℝ)
    (x z : ℝ^2) :
    |∑ m ∈ s, p m x * q m x - ∑ m ∈ s, p m z * q m z| ≤
      ∑ m ∈ s, min (boxBound α (p m) (q m) x z (x - z))
        (|p m x * q m x| + |p m z * q m z|) := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ ↦ le_min ?_ ?_)
  · exact abs_mul_sub_le_boxBound
  · exact abs_sub _ _

end HolderSpace
