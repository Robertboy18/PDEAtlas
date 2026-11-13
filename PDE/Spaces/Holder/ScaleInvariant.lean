/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.Directional
public import PDE.Spaces.Holder.Homogeneous

/-!
# Weighted Hölder seminorms from homogeneous bounds

A function on a convex set with `‖H y‖ ≤ A |y|^α` and `‖DH(y)‖ ≤ K |y|^{α - 1}` is `α`-Hölder with
constant `2 · 3^α A + K` (`HolderSpace.norm_sub_le_of_rpow_bounds`). Both bounds are invariant
under dilations, so they cover functions that are singular or growing at the origin, such as
weighted perturbations near a corner. A weight `g` with `g(h) |h|^α ≤ c` then bounds the weighted
seminorm `[H]_{C_g(S)}`.

## Main results

* `weightedSeminorm_le_of_rpow_bounds`: `[H]_{C_g(S)} ≤ (2 · 3^α A + K) c` when
  `g(h) |h|^α ≤ c`.
* `rpow_le_rpow_neg_add_rpow`: `r^p ≤ r^{-a} + r^b` for `r > 0` and `-a ≤ p ≤ b`, used to
  dominate sums of powers by a two-term weight.
-/

@[expose] public section

noncomputable section

open Set
open scoped ENNReal

namespace HolderSpace

/-- `r^p ≤ r^{-a} + r^b` for `r > 0` and `-a ≤ p ≤ b`. -/
theorem rpow_le_rpow_neg_add_rpow {r a b p : ℝ} (hr : 0 < r) (hpa : -a ≤ p) (hpb : p ≤ b) :
    r ^ p ≤ r ^ (-a) + r ^ b := by
  rcases le_total r 1 with h1 | h1
  · exact (Real.rpow_le_rpow_of_exponent_ge hr h1 hpa).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hr.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hpb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hr.le _))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Weighted seminorm from homogeneous bounds.** If a weight satisfies `g h |h|^α ≤ c` for
`h ≠ 0`, the bounds of `norm_sub_le_of_rpow_bounds` give `[H]_{C_g(S)} ≤ (2 · 3^α A + K) c`. -/
theorem weightedSeminorm_le_of_rpow_bounds {H : E → F} {S : Set E} (hS : Convex ℝ S)
    {α A K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ y ∈ S, DifferentiableAt ℝ H y) (hH : ∀ y ∈ S, ‖H y‖ ≤ A * ‖y‖ ^ α)
    (hH' : ∀ y ∈ S, y ≠ 0 → ‖fderiv ℝ H y‖ ≤ K * ‖y‖ ^ (α - 1))
    {g : E → ℝ} {c : ℝ} (hg : ∀ h : E, h ≠ 0 → g h * ‖h‖ ^ α ≤ c) :
    weightedSeminorm g S H ≤ ENNReal.ofReal ((2 * 3 ^ α * A + K) * c) := by
  refine weightedSeminorm_le_iff.2 fun x hx z hz ↦ ?_
  rcases eq_or_ne x z with rfl | hne
  · simp
  have hh : x - z ≠ 0 := sub_ne_zero.2 hne
  -- the constants are nonnegative: one of the two distinct points is nonzero
  obtain ⟨y, hyS, hy0⟩ : ∃ y ∈ S, y ≠ 0 := by
    by_cases hx0 : x = 0
    · exact ⟨z, hz, fun hz0 ↦ hne (hx0.trans hz0.symm)⟩
    · exact ⟨x, hx, hx0⟩
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hH y hyS))
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hy0) α)
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hH' y hyS hy0))
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hy0) (α - 1))
  rw [edist_eq_enorm_sub, ← ofReal_norm]
  rcases le_or_gt (g (x - z)) 0 with hg0 | hg0
  · rw [ENNReal.ofReal_of_nonpos hg0, mul_zero]
    exact bot_le
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖H x - H z‖ * g (x - z) ≤ (2 * 3 ^ α * A + K) * ‖x - z‖ ^ α * g (x - z) :=
        mul_le_mul_of_nonneg_right
          (norm_sub_le_of_rpow_bounds hS hα hα1 hd hH hH' hx hz) hg0.le
    _ = (2 * 3 ^ α * A + K) * (g (x - z) * ‖x - z‖ ^ α) := by ring
    _ ≤ (2 * 3 ^ α * A + K) * c := by
        gcongr
        exact hg (x - z) hh

end HolderSpace
