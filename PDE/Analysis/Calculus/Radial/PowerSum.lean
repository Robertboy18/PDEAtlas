/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.RealPower

/-!
# Finite sums of real powers of the radius near the origin

A weight `ρ(x) = ∑ₖ cₖ ‖x‖^{eₖ}` with every exponent `eₖ ≥ -a` is bounded on the punctured ball
`0 < ‖x‖ ≤ R` by `(∑ₖ |cₖ| R^{eₖ + a}) ‖x‖^{-a}`, and its derivative by
`(∑ₖ |cₖ| |eₖ| R^{eₖ + a}) ‖x‖^{-a-1}`: the most singular power dominates near the origin.

## Main results

* `PDE.Analysis.Radial.abs_sum_mul_norm_rpow_le`: the value bound.
* `PDE.Analysis.Radial.hasFDerivAt_sum_mul_norm_rpow`: the derivative off the origin.
* `PDE.Analysis.Radial.norm_fderiv_sum_mul_norm_rpow_le`: the derivative bound.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Radial

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} (s : Finset ι) (c e : ι → ℝ)

/-- One power of the radius below a more singular one: `‖x‖^e ≤ R^{e + a} ‖x‖^{-a}` for
`0 < ‖x‖ ≤ R` and `e ≥ -a`. -/
theorem norm_rpow_le_mul_rpow_neg {a R b : ℝ} (hb : -a ≤ b) {x : E} (hx : x ≠ 0)
    (hxR : ‖x‖ ≤ R) : ‖x‖ ^ b ≤ R ^ (b + a) * ‖x‖ ^ (-a) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  calc ‖x‖ ^ b = ‖x‖ ^ (b + a) * ‖x‖ ^ (-a) := by
        rw [← Real.rpow_add hx0]; ring_nf
    _ ≤ R ^ (b + a) * ‖x‖ ^ (-a) := by
      gcongr
      · linarith

/-- **Value bound for radial power sums.** If `eₖ ≥ -a` for `k ∈ s` and `0 < ‖x‖ ≤ R`, then
`|∑ₖ cₖ ‖x‖^{eₖ}| ≤ (∑ₖ |cₖ| R^{eₖ + a}) ‖x‖^{-a}`. -/
theorem abs_sum_mul_norm_rpow_le {a R : ℝ} (he : ∀ k ∈ s, -a ≤ e k) {x : E} (hx : x ≠ 0)
    (hxR : ‖x‖ ≤ R) :
    |∑ k ∈ s, c k * ‖x‖ ^ e k| ≤ (∑ k ∈ s, |c k| * R ^ (e k + a)) * ‖x‖ ^ (-a) := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_rpow_le_mul_rpow_neg (he k hk) hx hxR) (abs_nonneg _)

variable [InnerProductSpace ℝ E]

/-- The derivative of a radial power sum off the origin:
`D(∑ₖ cₖ ‖x‖^{eₖ}) = ∑ₖ cₖ eₖ ‖x‖^{eₖ - 2} ⟨x, ·⟩`. -/
theorem hasFDerivAt_sum_mul_norm_rpow {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ∑ k ∈ s, c k * ‖y‖ ^ e k)
      (∑ k ∈ s, (c k * (e k * ‖x‖ ^ (e k - 2))) • innerSL ℝ x) x := by
  refine HasFDerivAt.fun_sum fun k _ ↦ ?_
  exact (hasFDerivAt_norm_rpow_of_ne_zero (e k) hx).const_mul (c k) |>.congr_fderiv
    (by rw [smul_smul])

/-- **Derivative bound for radial power sums.** If `eₖ ≥ -a` for `k ∈ s` and `0 < ‖x‖ ≤ R`, then
`‖D(∑ₖ cₖ ‖x‖^{eₖ})‖ ≤ (∑ₖ |cₖ| |eₖ| R^{eₖ + a}) ‖x‖^{-a-1}`. -/
theorem norm_fderiv_sum_mul_norm_rpow_le {a R : ℝ} (he : ∀ k ∈ s, -a ≤ e k) {x : E}
    (hx : x ≠ 0) (hxR : ‖x‖ ≤ R) :
    ‖fderiv ℝ (fun y : E ↦ ∑ k ∈ s, c k * ‖y‖ ^ e k) x‖ ≤
      (∑ k ∈ s, |c k| * |e k| * R ^ (e k + a)) * ‖x‖ ^ (-a - 1) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [(hasFDerivAt_sum_mul_norm_rpow s c e hx).fderiv, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  have hpow : ‖x‖ ^ (e k - 2) * ‖x‖ = ‖x‖ ^ (e k - 1) := by
    rw [← Real.rpow_add_one hx0.ne']; ring_nf
  have hb : -(a + 1) ≤ e k - 1 := by linarith [he k hk]
  have := norm_rpow_le_mul_rpow_neg hb hx hxR
  calc |c k| * (|e k| * ‖x‖ ^ (e k - 2)) * ‖x‖ = |c k| * |e k| * ‖x‖ ^ (e k - 1) := by
        rw [← hpow]; ring
    _ ≤ |c k| * |e k| * (R ^ (e k - 1 + (a + 1)) * ‖x‖ ^ (-(a + 1))) := by gcongr
    _ = |c k| * |e k| * R ^ (e k + a) * ‖x‖ ^ (-a - 1) := by ring_nf

end PDE.Analysis.Radial
