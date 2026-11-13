/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Gated.Basic

/-!
# Scalar bounds for the reflected gated flux

The positive left plateau of `C` separates the activity of `C'` from its
reflection. Only one feedback derivative contributes to the middle speed at
each state, giving the bound `361/4000` and strict gaps from the fast speeds.

The prescribed second derivatives give an exact decomposition of the middle
curvature. Four nonnegative pulse terms accompany the strictly positive clock
density.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.GatedFlux

private theorem abs_cutoff_feedback_le {d v : ℝ}
    (hd : -(1 / 100) ≤ d ∧ d ≤ 0) (hv : -4 ≤ v ∧ v ≤ 1) :
    |d * v| ≤ 1 / 25 := by
  have hdabs : |d| ≤ 1 / 100 :=
    abs_le.mpr ⟨hd.1, hd.2.trans (by norm_num)⟩
  have hvabs : |v| ≤ 4 := abs_le.mpr ⟨hv.1, hv.2.trans (by norm_num)⟩
  rw [abs_mul]
  calc
    |d| * |v| ≤ (1 / 100 : ℝ) * 4 :=
      mul_le_mul hdabs hvabs (abs_nonneg v) (by norm_num)
    _ = 1 / 25 := by norm_num

/-- Reflection-disjoint cutoff derivatives give the sharp stated clock-plus-feedback bound. -/
theorem abs_middleSpeed_le {g C φ : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hplateau : ∀ s, s ≤ a → C s = 1)
    (hg : ∀ s, |deriv g s| ≤ 201 / 4000) (hC : ∀ s, -(1 / 100) ≤ deriv C s ∧ deriv C s ≤ 0)
    (hφ : ∀ s, -4 ≤ φ s ∧ φ s ≤ 1) (q : ℝ^3) :
    |middleSpeed g C φ q| ≤ 361 / 4000 := by
  have hg_bounds := abs_le.mp (hg (q 1))
  have hx_bounds := abs_le.mp (abs_cutoff_feedback_le (hC (q 1)) (hφ (q 0)))
  have hz_bounds := abs_le.mp (abs_cutoff_feedback_le (hC (-q 1)) (hφ (q 2)))
  rcases mul_eq_zero.mp (deriv_cutoff_mul_deriv_reflection_eq_zero ha hplateau (q 1)) with hy | hny
  · rw [middleSpeed, hy, zero_mul, add_zero, abs_le]
    constructor <;> linarith [hg_bounds.1, hg_bounds.2, hz_bounds.1, hz_bounds.2]
  · rw [middleSpeed, hny, zero_mul, sub_zero, abs_le]
    constructor <;> linarith [hg_bounds.1, hg_bounds.2, hx_bounds.1, hx_bounds.2]

/-- The gap from the negative fast diagonal to the middle diagonal exceeds `5/4`.
Only the lower fast-slope bound is needed. -/
theorem five_fourths_lt_left_gap {k g C φ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hplateau : ∀ s, s ≤ a → C s = 1) (hg : ∀ s, |deriv g s| ≤ 201 / 4000)
    (hC : ∀ s, -(1 / 100) ≤ deriv C s ∧ deriv C s ≤ 0) (hφ : ∀ s, -4 ≤ φ s ∧ φ s ≤ 1)
    (hk : ∀ s, 7 / 4 < deriv k s) (q : ℝ^3) :
    5 / 4 < middleSpeed g C φ q - (-deriv k (q 0)) := by
  have hm := (abs_le.mp (abs_middleSpeed_le ha hplateau hg hC hφ q)).1
  linarith [hk (q 0)]

/-- The gap from the middle diagonal to the positive fast diagonal exceeds `5/4`. -/
theorem five_fourths_lt_right_gap {k g C φ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hplateau : ∀ s, s ≤ a → C s = 1) (hg : ∀ s, |deriv g s| ≤ 201 / 4000)
    (hC : ∀ s, -(1 / 100) ≤ deriv C s ∧ deriv C s ≤ 0) (hφ : ∀ s, -4 ≤ φ s ∧ φ s ≤ 1)
    (hk : ∀ s, 7 / 4 < deriv k s) (q : ℝ^3) :
    5 / 4 < deriv k (q 2) - middleSpeed g C φ q := by
  have hm := (abs_le.mp (abs_middleSpeed_le ha hplateau hg hC hφ q)).2
  linarith [hk (q 2)]

/-- The second-derivative formulas expose the pulse weights `1-φ` and `4+φ`. -/
theorem middleCurvature_eq_decomposition {g C φ qMinus qPlus ρ : ℝ → ℝ}
    (hC2 : ∀ y, deriv (deriv C) y = (qPlus y - qMinus y) / 100)
    (hg2 : ∀ y, deriv (deriv g) y = (qMinus y + 4 * qPlus y + qMinus (-y) + 4 * qPlus (-y)) / 100 +
      (1 / 1000000 : ℝ) * ρ (y / 100))
    (q : ℝ^3) :
    middleCurvature g C φ q = (1 / 1000000 : ℝ) * ρ (q 1 / 100) +
      (qMinus (q 1) * (1 - φ (q 0)) + qPlus (q 1) * (4 + φ (q 0)) +
        qMinus (-q 1) * (1 - φ (q 2)) + qPlus (-q 1) * (4 + φ (q 2))) / 100 := by
  rw [middleCurvature, hg2 (q 1), hC2 (-q 1), hC2 (q 1)]
  ring

/-- Nonnegative pulse densities and a positive clock density force positive middle curvature.
The cutoff and clock hypotheses are the scalar construction identities, not a curvature sign. -/
theorem middleCurvature_pos {g C φ qMinus qPlus ρ : ℝ → ℝ}
    (hC2 : ∀ y, deriv (deriv C) y = (qPlus y - qMinus y) / 100)
    (hg2 : ∀ y, deriv (deriv g) y = (qMinus y + 4 * qPlus y + qMinus (-y) + 4 * qPlus (-y)) / 100 +
      (1 / 1000000 : ℝ) * ρ (y / 100))
    (hqMinus : ∀ y, 0 ≤ qMinus y) (hqPlus : ∀ y, 0 ≤ qPlus y) (hρ : ∀ y, 0 < ρ y)
    (hφ : ∀ s, -4 ≤ φ s ∧ φ s ≤ 1) (q : ℝ^3) :
    0 < middleCurvature g C φ q := by
  rw [middleCurvature_eq_decomposition hC2 hg2 q]
  have hminus (y x : ℝ) : 0 ≤ qMinus y * (1 - φ x) :=
    mul_nonneg (hqMinus y) (sub_nonneg.mpr (hφ x).2)
  have hplus (y x : ℝ) : 0 ≤ qPlus y * (4 + φ x) :=
    mul_nonneg (hqPlus y) (by linarith [(hφ x).1])
  have hsum : 0 ≤ (qMinus (q 1) * (1 - φ (q 0)) + qPlus (q 1) * (4 + φ (q 0)) +
        qMinus (-q 1) * (1 - φ (q 2)) + qPlus (-q 1) * (4 + φ (q 2))) / 100 := div_nonneg
      (add_nonneg (add_nonneg (add_nonneg (hminus (q 1) (q 0)) (hplus (q 1) (q 0)))
          (hminus (-q 1) (q 2)))
        (hplus (-q 1) (q 2))) (by norm_num)
  have hclock : 0 < (1 / 1000000 : ℝ) * ρ (q 1 / 100) :=
    mul_pos (by norm_num) (hρ (q 1 / 100))
  linarith

end PDE.Hyperbolic.ConservationLaw.System.GatedFlux
