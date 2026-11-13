/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.PowerSum

/-!
# Finite sums of real powers of the radius away from the origin

A weight `ρ(x) = ∑ₖ cₖ ‖x‖^{eₖ}` with every exponent `eₖ ≤ b` is bounded for `‖x‖ ≥ 1` by
`(∑ₖ |cₖ|) ‖x‖^b`, and its derivative by `(∑ₖ |cₖ| |eₖ|) ‖x‖^{b-1}`: the least decaying power
dominates in the far field. These complement the near-origin bounds of `PowerSum.lean`.

## Main results

* `PDE.Analysis.Radial.abs_sum_mul_norm_rpow_le_of_one_le`: the value bound.
* `PDE.Analysis.Radial.norm_fderiv_sum_mul_norm_rpow_le_of_one_le`: the derivative bound.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Radial

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} (s : Finset ι) (c e : ι → ℝ)

/-- **Value bound for radial power sums in the far field.** If `eₖ ≤ b` for `k ∈ s` and
`‖x‖ ≥ 1`, then `|∑ₖ cₖ ‖x‖^{eₖ}| ≤ (∑ₖ |cₖ|) ‖x‖^b`. -/
theorem abs_sum_mul_norm_rpow_le_of_one_le {b : ℝ} (he : ∀ k ∈ s, e k ≤ b) {x : E}
    (hx : 1 ≤ ‖x‖) :
    |∑ k ∈ s, c k * ‖x‖ ^ e k| ≤ (∑ k ∈ s, |c k|) * ‖x‖ ^ b := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (he k hk))
    (abs_nonneg _)

variable [InnerProductSpace ℝ E]

/-- **Derivative bound for radial power sums in the far field.** If `eₖ ≤ b` for `k ∈ s` and
`‖x‖ ≥ 1`, then `‖D(∑ₖ cₖ ‖x‖^{eₖ})‖ ≤ (∑ₖ |cₖ| |eₖ|) ‖x‖^{b-1}`. -/
theorem norm_fderiv_sum_mul_norm_rpow_le_of_one_le {b : ℝ} (he : ∀ k ∈ s, e k ≤ b) {x : E}
    (hx : 1 ≤ ‖x‖) :
    ‖fderiv ℝ (fun y : E ↦ ∑ k ∈ s, c k * ‖y‖ ^ e k) x‖ ≤
      (∑ k ∈ s, |c k| * |e k|) * ‖x‖ ^ (b - 1) := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx
  have hxne : x ≠ 0 := norm_pos_iff.1 hx0
  rw [(hasFDerivAt_sum_mul_norm_rpow s c e hxne).fderiv, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  have hpow : ‖x‖ ^ (e k - 2) * ‖x‖ = ‖x‖ ^ (e k - 1) := by
    rw [← Real.rpow_add_one hx0.ne']; ring_nf
  have hle : ‖x‖ ^ (e k - 1) ≤ ‖x‖ ^ (b - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [he k hk])
  calc |c k| * (|e k| * ‖x‖ ^ (e k - 2)) * ‖x‖ = |c k| * |e k| * ‖x‖ ^ (e k - 1) := by
        rw [← hpow]; ring
    _ ≤ |c k| * |e k| * ‖x‖ ^ (b - 1) := by gcongr

end PDE.Analysis.Radial
