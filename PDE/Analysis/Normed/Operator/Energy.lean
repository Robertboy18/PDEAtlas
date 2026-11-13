/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Tactic.Positivity.Finset

/-!
# A uniform bound for the energy of a composed variation

Along an affine variation, a bounded Lipschitz family of linear maps produces
an energy whose Lipschitz constant grows quadratically in the original vector
and its variation. This is the bound needed to differentiate a Sobolev energy
under the integral: square-integrable weak derivatives give an integrable
bound, even when those derivatives are unbounded.
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

variable {F : Type*} [NormedAddCommGroup F]

private theorem abs_half_norm_sq_sub_le (x y : F) :
    |‖x‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2| ≤
      (‖x‖ + ‖y‖) / 2 * ‖x - y‖ := by
  have heq : ‖x‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2 =
      (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) / 2 := by ring
  rw [heq, abs_div, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le x y)
    (add_nonneg (norm_nonneg x) (norm_nonneg y))
  nlinarith

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- On `[-1,1]`, the energy of a bounded Lipschitz operator family applied to
an affine vector has a quadratic Lipschitz bound. This estimate does not
require either vector to be nonzero. -/
theorem lipschitzOnWith_half_norm_sq_apply_affine
    {T : E → E →L[ℝ] F} {C K : ℝ≥0}
    (hbound : ∀ z, ‖T z‖ ≤ C) (hLip : LipschitzWith K T)
    (u v a b : E) :
    LipschitzOnWith
      (C * (K * ‖v‖₊ + C) * (‖a‖₊ + ‖b‖₊) ^ 2)
      (fun t : ℝ ↦ ‖T (u + t • v) (a + t • b)‖ ^ 2 / 2) (Icc (-1) 1) := by
  let B : ℝ := ‖a‖ + ‖b‖
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hvector (t : ℝ) (ht : t ∈ Icc (-1) 1) : ‖a + t • b‖ ≤ B := by
    calc
      ‖a + t • b‖ ≤ ‖a‖ + ‖t • b‖ := norm_add_le _ _
      _ = ‖a‖ + |t| * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ B := by
        have ht' : |t| ≤ 1 := abs_le.mpr ht
        dsimp [B]
        nlinarith [norm_nonneg b]
  have hnorm (t : ℝ) (ht : t ∈ Icc (-1) 1) :
      ‖T (u + t • v) (a + t • b)‖ ≤ C * B :=
    ((T _).le_opNorm _).trans
      (mul_le_mul (hbound _) (hvector t ht) (norm_nonneg _) C.property)
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro t ht s hs
  have hdiff : ‖T (u + t • v) (a + t • b) - T (u + s • v) (a + s • b)‖ ≤
      ((K : ℝ) * ‖v‖ + C) * B * |t - s| := by
    have hid :
        T (u + t • v) (a + t • b) - T (u + s • v) (a + s • b) =
          T (u + t • v) ((t - s) • b) +
            (T (u + t • v) - T (u + s • v)) (a + s • b) := by
      rw [show (t - s) • b = (a + t • b) - (a + s • b) by module]
      rw [map_sub, sub_apply]
      abel
    rw [hid]
    calc
      ‖T (u + t • v) ((t - s) • b) +
          (T (u + t • v) - T (u + s • v)) (a + s • b)‖
          ≤ ‖T (u + t • v) ((t - s) • b)‖ +
            ‖(T (u + t • v) - T (u + s • v)) (a + s • b)‖ := norm_add_le _ _
      _ ≤ C * (|t - s| * ‖b‖) +
          ((K : ℝ) * (|t - s| * ‖v‖)) * B := by
        apply add_le_add
        · simpa [norm_smul, Real.norm_eq_abs] using
            (T (u + t • v)).le_of_opNorm_le (hbound _) ((t - s) • b)
        · have hT : ‖T (u + t • v) - T (u + s • v)‖ ≤
              (K : ℝ) * (|t - s| * ‖v‖) := by
            simpa [← sub_smul, norm_smul, Real.norm_eq_abs] using
              hLip.norm_sub_le (u + t • v) (u + s • v)
          exact ((T _ - T _).le_opNorm _).trans
            (mul_le_mul hT (hvector s hs) (norm_nonneg _)
              (mul_nonneg K.property (mul_nonneg (abs_nonneg _) (norm_nonneg _))))
      _ ≤ ((K : ℝ) * ‖v‖ + C) * B * |t - s| := by
        have hb : ‖b‖ ≤ B := le_add_of_nonneg_left (norm_nonneg a)
        calc
          _ ≤ C * (|t - s| * B) +
              ((K : ℝ) * (|t - s| * ‖v‖)) * B :=
            add_le_add (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) C.property) le_rfl
          _ = _ := by ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  change _ ≤ (C : ℝ) * ((K : ℝ) * ‖v‖ + C) * B ^ 2 * |t - s|
  calc
    _ ≤ (‖T (u + t • v) (a + t • b)‖ +
          ‖T (u + s • v) (a + s • b)‖) / 2 *
          ‖T (u + t • v) (a + t • b) - T (u + s • v) (a + s • b)‖ :=
      abs_half_norm_sq_sub_le _ _
    _ ≤ ((C : ℝ) * B) * (((K : ℝ) * ‖v‖ + C) * B * |t - s|) := by
      apply mul_le_mul
      · linarith [hnorm t ht, hnorm s hs]
      · exact hdiff
      · exact norm_nonneg _
      · exact mul_nonneg C.property hB
    _ = _ := by ring

end ContinuousLinearMap
