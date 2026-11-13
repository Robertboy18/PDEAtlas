/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Translation of power-growth fluxes

Translating the argument of a flux preserves its power growth and coercive pairing
bound, with a smaller positive coercivity constant. The error depends on the shift
through its `p`-th power and the product of its norm with the growth offset.
For an `Lᵖ` shift and a conjugate-`Lq` offset, these errors are integrable.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace PDE.Analysis.Operator

/-- The real-valued form of Mathlib's nonnegative power-sum estimate. -/
private theorem add_rpow_bound {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hr : 0 ≤ r) :
    (x + y) ^ r ≤ 2 ^ r * (x ^ r + y ^ r) := by
  have hxfinite := ENNReal.rpow_ne_top_of_nonneg hr
    (ENNReal.ofReal_ne_top : ENNReal.ofReal x ≠ ∞)
  have hyfinite := ENNReal.rpow_ne_top_of_nonneg hr
    (ENNReal.ofReal_ne_top : ENNReal.ofReal y ≠ ∞)
  have htwo := ENNReal.rpow_ne_top_of_nonneg hr (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top htwo (ENNReal.add_ne_top.mpr ⟨hxfinite, hyfinite⟩))
    (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      (ENNReal.ofReal x) (ENNReal.ofReal y) hr)
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hxfinite hyfinite, ENNReal.toReal_ofReal hx,
    ENNReal.toReal_ofReal hy, ENNReal.toReal_ofNat] using h

/-- A mixed power of two nonnegative numbers can be absorbed into any positive
multiple of the higher power of the first. The remaining constant is uniform in
both numbers. -/
private theorem exists_rpow_absorption {r ε : ℝ} (hr : 1 < r) (hε : 0 < ε)
    (C : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      |C| * x ^ (r - 1) * y ≤ ε * x ^ r + K * y ^ r := by
  let L : ℝ := |C| / ε + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hLC : |C| ≤ ε * L := by
    dsimp [L]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hε.ne']
    exact le_add_of_nonneg_right hε.le
  let K : ℝ := |C| * L ^ (r - 1)
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hL.le _)
  refine ⟨K, hK, fun x y hx hy ↦ ?_⟩
  have hxpow : x ^ (r - 1) * x = x ^ r := by
    simpa only [sub_add_cancel] using
      (Real.rpow_add_one' hx (by linarith : r - 1 + 1 ≠ 0)).symm
  have hypow : y ^ (r - 1) * y = y ^ r := by
    simpa only [sub_add_cancel] using
      (Real.rpow_add_one' hy (by linarith : r - 1 + 1 ≠ 0)).symm
  by_cases hxy : x ≤ L * y
  · have hpow := Real.rpow_le_rpow hx hxy (sub_pos.mpr hr).le
    have hsmall : |C| * x ^ (r - 1) * y ≤ K * y ^ r := by
      calc
        _ ≤ |C| * (L * y) ^ (r - 1) * y :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (abs_nonneg C)) hy
        _ = K * y ^ r := by
          rw [Real.mul_rpow hL.le hy]
          simp only [K, mul_assoc, hypow]
    exact hsmall.trans (le_add_of_nonneg_left
      (mul_nonneg hε.le (Real.rpow_nonneg hx _)))
  · have hlarge : |C| * y ≤ ε * x :=
      (mul_le_mul_of_nonneg_right hLC hy).trans
        (by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (le_of_not_ge hxy) hε.le)
    have hbound := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hx (r - 1))
    have hmain : |C| * x ^ (r - 1) * y ≤ ε * x ^ r := by
      calc
        _ = x ^ (r - 1) * (|C| * y) := by rw [mul_assoc, mul_left_comm]
        _ ≤ x ^ (r - 1) * (ε * x) := hbound
        _ = ε * x ^ r := by rw [mul_left_comm, hxpow]
    exact hmain.trans (le_add_of_nonneg_right
      (mul_nonneg hK (Real.rpow_nonneg hy _)))

/-- Translating a flux with `r`-power growth changes its offset by a constant
multiple of the shift's `r`-th power. No inner product structure is needed. -/
theorem norm_flux_translate_le_rpow
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (a : E → F) {h C r : ℝ}
    (hr : 0 ≤ r) (hgrowth : ∀ z, ‖a z‖ ≤ h + C * ‖z‖ ^ r) (v z : E) :
    ‖a (v + z)‖ ≤
      (‖h‖ + (|C| * 2 ^ r) * ‖v‖ ^ r) + (|C| * 2 ^ r) * ‖z‖ ^ r := by
  have hpow := (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le v z) hr).trans
    (add_rpow_bound (norm_nonneg v) (norm_nonneg z) hr)
  calc
    ‖a (v + z)‖ ≤ h + C * ‖v + z‖ ^ r := hgrowth _
    _ ≤ ‖h‖ + |C| * ‖v + z‖ ^ r :=
      add_le_add (Real.le_norm_self h)
        (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (norm_nonneg _) _))
    _ ≤ ‖h‖ + |C| * (2 ^ r * (‖v‖ ^ r + ‖z‖ ^ r)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hpow (abs_nonneg C)) _
    _ = _ := by rw [← mul_assoc, mul_add, add_assoc]

/-- For `p > 1`, translating a coercive power-growth flux preserves a positive
`p`-power lower bound. The constants depend only on `p`, the original coercivity
constant, and the growth coefficient, so the same constants work at every spatial
point. The shift error is `b + ‖h‖ ‖v‖ + K ‖v‖^p`. -/
theorem exists_pos_rpow_lower_bound_flux_translate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p c : ℝ} (hp : 1 < p) (hc : 0 < c) (C : ℝ) :
    ∃ c' K : ℝ, 0 < c' ∧ 0 ≤ K ∧
      ∀ (a : E → E) (h b : ℝ),
        (∀ z, ‖a z‖ ≤ h + C * ‖z‖ ^ (p - 1)) →
        (∀ z, c * ‖z‖ ^ p - b ≤ inner ℝ (a z) z) →
        ∀ v z, c' * ‖z‖ ^ p - (b + ‖h‖ * ‖v‖ + K * ‖v‖ ^ p) ≤
          inner ℝ (a (v + z)) z := by
  obtain ⟨K, hK, hcross⟩ := exists_rpow_absorption hp (half_pos hc) C
  have htwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  let c' : ℝ := (c / 2) / 2 ^ p
  have hc' : 0 < c' := div_pos (half_pos hc) htwo
  refine ⟨c', c / 2 + K, hc', add_nonneg (half_pos hc).le hK, ?_⟩
  intro a h b hgrowth hlower v z
  have hshift : ‖z‖ ≤ ‖v + z‖ + ‖v‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (v + z) v
  have hpow := (Real.rpow_le_rpow
      (norm_nonneg z) hshift (zero_lt_one.trans hp).le).trans
    (add_rpow_bound (norm_nonneg (v + z)) (norm_nonneg v)
      (zero_lt_one.trans hp).le)
  have hscaled : c' * ‖z‖ ^ p ≤ (c / 2) * (‖v + z‖ ^ p + ‖v‖ ^ p) := by
    have h := mul_le_mul_of_nonneg_left hpow hc'.le
    simpa only [c', ← mul_assoc, div_mul_cancel₀ _ htwo.ne'] using h
  have hcross' := hcross ‖v + z‖ ‖v‖ (norm_nonneg _) (norm_nonneg _)
  have hnorm : ‖a (v + z)‖ ≤ ‖h‖ + |C| * ‖v + z‖ ^ (p - 1) :=
    (hgrowth _).trans
      (add_le_add (Real.le_norm_self h)
        (mul_le_mul_of_nonneg_right (le_abs_self C)
          (Real.rpow_nonneg (norm_nonneg _) _)))
  have hpair : inner ℝ (a (v + z)) v ≤
      ‖h‖ * ‖v‖ + |C| * ‖v + z‖ ^ (p - 1) * ‖v‖ := by
    calc
      _ ≤ ‖a (v + z)‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ (‖h‖ + |C| * ‖v + z‖ ^ (p - 1)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = _ := add_mul _ _ _
  have hl := hlower (v + z)
  rw [inner_add_right] at hl
  nlinarith

end PDE.Analysis.Operator
