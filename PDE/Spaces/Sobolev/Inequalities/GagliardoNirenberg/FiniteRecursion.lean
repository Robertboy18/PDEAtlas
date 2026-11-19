/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Finite adjacent-order interpolation

A finite nonnegative sequence whose squared interior terms are bounded by the
product of their neighbors is bounded by its two endpoints. The constant depends
only on the length and the coefficient in the adjacent-order inequalities.
This additive estimate suffices for uniform bounds on smooth approximations.
-/

@[expose] public section

namespace SobolevSpace.GagliardoNirenberg

private theorem le_endpoints_of_sq_le {x a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (h : x ^ 2 ≤ d * (a + x) * b) :
    x ≤ (2 * d + 1) * (a + b) := by
  by_contra! hx
  have ha' : a ≤ (2 * d + 1) * (a + b) := by
    nlinarith [mul_nonneg hd (add_nonneg ha hb)]
  have hax : a ≤ x := ha'.trans hx.le
  have hxpos : 0 < x := lt_of_le_of_lt (ha.trans ha') hx
  have hsq : x * x ≤ (2 * d * b) * x := by
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show a + x ≤ 2 * x by linarith) hd) hb
    nlinarith
  have hx' := (mul_le_mul_iff_left₀ hxpos).mp hsq
  have hdb : 2 * d * b ≤ (2 * d + 1) * (a + b) := by
    nlinarith [mul_nonneg hd ha]
  exact (not_lt_of_ge (hx'.trans hdb)) hx

/-- Adjacent product inequalities control every term of a finite nonnegative
sequence by the sum of its endpoints. The constant is independent of the sequence. -/
theorem exists_constant_of_adjacent_sq_le {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ X : ℕ → ℝ,
      (∀ j ≤ k, 0 ≤ X j) →
      (∀ j, 0 < j → j < k → X j ^ 2 ≤ C * X (j - 1) * X (j + 1)) →
      ∀ j ≤ k, X j ≤ A * (X 0 + X k) := by
  induction k with
  | zero =>
    refine ⟨1, le_rfl, ?_⟩
    intro X hX _ j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa only [one_mul] using le_add_of_nonneg_right (hX 0 le_rfl)
  | succ k ih =>
    obtain ⟨A, hA, hrec⟩ := ih
    have hA0 : 0 ≤ A := le_trans zero_le_one hA
    by_cases hk : k = 0
    · subst k
      refine ⟨1, le_rfl, ?_⟩
      intro X hX _ j hj
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · simpa only [one_mul] using le_add_of_nonneg_right (hX 1 le_rfl)
      · simpa only [one_mul] using le_add_of_nonneg_left (hX 0 (by omega))
    · let d := C * A
      have hd : 0 ≤ d := mul_nonneg hC hA0
      have hfactor : 1 ≤ 2 * d + 2 := by linarith
      have hconst : 1 ≤ A * (2 * d + 2) :=
        hfactor.trans (le_mul_of_one_le_left (by linarith) hA)
      refine ⟨A * (2 * d + 2), hconst, ?_⟩
      intro X hX hadj j hj
      have hlow : ∀ i ≤ k, X i ≤ A * (X 0 + X k) :=
        hrec X (fun i hi ↦ hX i (by omega))
          (fun i hi hik ↦ hadj i hi (by omega))
      have hlast : X k ^ 2 ≤ d * (X 0 + X k) * X (k + 1) := by
        calc
          X k ^ 2 ≤ C * X (k - 1) * X (k + 1) := hadj k (by omega) (by omega)
          _ ≤ C * (A * (X 0 + X k)) * X (k + 1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hlow (k - 1) (by omega)) hC)
              (hX (k + 1) le_rfl)
          _ = _ := by dsimp only [d]; ring
      have hkbound := le_endpoints_of_sq_le (hX 0 (by omega))
        (hX (k + 1) le_rfl) hd hlast
      have hsum : 0 ≤ X 0 + X (k + 1) :=
        add_nonneg (hX 0 (by omega)) (hX (k + 1) le_rfl)
      by_cases hjk : j ≤ k
      · calc
          X j ≤ A * (X 0 + X k) := hlow j hjk
          _ ≤ A * ((2 * d + 2) * (X 0 + X (k + 1))) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hX (k + 1) le_rfl]) hA0
          _ = _ := by ring
      · have hj' : j = k + 1 := by omega
        subst j
        calc
          X (k + 1) ≤ X 0 + X (k + 1) := le_add_of_nonneg_left (hX 0 (by omega))
          _ ≤ A * (2 * d + 2) * (X 0 + X (k + 1)) :=
            le_mul_of_one_le_left hsum hconst

end SobolevSpace.GagliardoNirenberg
