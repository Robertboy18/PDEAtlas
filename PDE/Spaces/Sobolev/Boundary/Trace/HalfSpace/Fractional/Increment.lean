/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Operator

/-!
# Splitting a boundary increment through the upper half-space

Join two boundary points to points above them at a common height. Their boundary
increment is the sum of two normal increments and one tangential increment at
that height. For `p ≥ 1`, finite-sum convexity bounds its `p`-energy by
`3 ^ (p - 1)` times the sum of the three increment energies.

The distance height `‖x - y‖` puts the intermediate points in the open upper
half-space when `x ≠ y`. No regularity or support assumption is needed for this
pointwise step for functions into any normed additive commutative group. In
dimension zero, all boundary points coincide and the estimate still applies.
-/

@[expose] public section

namespace SobolevSpace.Trace.HalfSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

private theorem add_three_rpow_le (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {p : ℝ} (hp : 1 ≤ p) :
    (a + b + c) ^ p ≤ (3 : ℝ) ^ (p - 1) * (a ^ p + b ^ p + c ^ p) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ
    (f := ![a, b, c]) hp (by intro i _; fin_cases i <;> simp [ha, hb, hc])
  simpa [Fin.sum_univ_three] using h

/-- A boundary difference telescopes through the two points at a common height. -/
theorem smoothBoundaryValue_sub_eq_normal_add_tangential_add_normal
    (f : ℝ^(n + 1) → F) (x y : ℝ^n) (t : ℝ) :
    smoothBoundaryValue f x - smoothBoundaryValue f y =
      (smoothBoundaryValue f x - normalSlice f x t) +
        (normalSlice f x t - normalSlice f y t) +
        (normalSlice f y t - smoothBoundaryValue f y) := by
  rw [sub_add_sub_cancel, sub_add_sub_cancel]

/-- Boundary `p`-increments are controlled by two normal increments and the
tangential increment at the same height. No sign restriction on the height is needed. -/
theorem smoothBoundaryValue_sub_rpow_le_normal_tangential
    (f : ℝ^(n + 1) → F) (x y : ℝ^n) (t : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    ‖smoothBoundaryValue f x - smoothBoundaryValue f y‖ ^ p ≤
      (3 : ℝ) ^ (p - 1) *
        (‖normalSlice f x t - smoothBoundaryValue f x‖ ^ p +
          ‖normalSlice f x t - normalSlice f y t‖ ^ p +
          ‖normalSlice f y t - smoothBoundaryValue f y‖ ^ p) := by
  have htriangle : ‖smoothBoundaryValue f x - smoothBoundaryValue f y‖ ≤
      ‖normalSlice f x t - smoothBoundaryValue f x‖ +
        ‖normalSlice f x t - normalSlice f y t‖ +
        ‖normalSlice f y t - smoothBoundaryValue f y‖ := by
    calc
      _ = ‖(smoothBoundaryValue f x - normalSlice f x t) +
          (normalSlice f x t - normalSlice f y t) +
          (normalSlice f y t - smoothBoundaryValue f y)‖ := by
        rw [← smoothBoundaryValue_sub_eq_normal_add_tangential_add_normal]
      _ ≤ ‖(smoothBoundaryValue f x - normalSlice f x t) +
          (normalSlice f x t - normalSlice f y t)‖ +
          ‖normalSlice f y t - smoothBoundaryValue f y‖ := norm_add_le _ _
      _ ≤ (‖smoothBoundaryValue f x - normalSlice f x t‖ +
          ‖normalSlice f x t - normalSlice f y t‖) +
          ‖normalSlice f y t - smoothBoundaryValue f y‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by rw [norm_sub_rev (smoothBoundaryValue f x)]
  exact (Real.rpow_le_rpow (norm_nonneg _) htriangle (zero_le_one.trans hp)).trans
    (add_three_rpow_le _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hp)

/-- Above distinct boundary points, the distance height is strictly inside the
upper half-space. The tangential base point `z` may be either endpoint. -/
theorem joinTangentialNormal_norm_sub_mem_upper
    {x y : ℝ^n} (hxy : x ≠ y) (z : ℝ^n) :
    joinTangentialNormal (z, ‖x - y‖) ∈ HalfSpace.upper (n + 1) := by
  change 0 < joinTangentialNormal (z, ‖x - y‖) (Fin.last n)
  simpa using norm_pos_iff.mpr (sub_ne_zero.mpr hxy)

end SobolevSpace.Trace.HalfSpace
