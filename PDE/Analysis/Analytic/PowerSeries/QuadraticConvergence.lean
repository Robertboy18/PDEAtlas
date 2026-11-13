/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Catalan
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Convergence of a scalar quadratic recursion

For `w = a + X (b w + c w²)`, induction bounds the coefficients by a scaled
Catalan sequence. The resulting exponential bound proves convergence without
assuming an analytic solution or a convergence estimate.
-/

@[expose] public section

open scoped BigOperators NNReal ENNReal

namespace PowerSeries

/-- A quadratic coefficient recursion is bounded by a scaled Catalan sequence. -/
theorem norm_coeff_le_catalan_of_quadratic (w : PowerSeries ℝ) {a b c M Q : ℝ}
    (hw : w = C a + X * (C b * w + C c * w ^ 2))
    (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (hQ : 0 ≤ Q) (hbc : ‖b‖ + ‖c‖ * M ≤ Q) :
    ∀ n, ‖coeff n w‖ ≤ M * Q ^ n * (catalan n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have hz := congrArg constantCoeff hw
      simp only [map_add, map_mul, constantCoeff_C, constantCoeff_X, zero_mul,
        add_zero] at hz
      simpa [coeff_zero_eq_constantCoeff, hz] using ha
    | succ n =>
      have heq := congrArg (coeff (n + 1)) hw
      simp only [map_add, coeff_C, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ite_false, coeff_succ_X_mul, coeff_C_mul, zero_add] at heq
      have hcat : (catalan (n + 1) : ℝ) =
          ∑ ij ∈ Finset.antidiagonal n, (catalan ij.1 : ℝ) * (catalan ij.2 : ℝ) := by
        exact_mod_cast catalan_succ' n
      have hcat_le : (catalan n : ℝ) ≤ (catalan (n + 1) : ℝ) := by
        rw [hcat]
        simpa using Finset.single_le_sum
          (f := fun ij : ℕ × ℕ ↦ (catalan ij.1 : ℝ) * (catalan ij.2 : ℝ))
          (fun ij hij ↦ by positivity)
          (show (0, n) ∈ Finset.antidiagonal n by simp)
      have hsquare : ‖coeff n (w ^ 2)‖ ≤ M ^ 2 * Q ^ n * (catalan (n + 1) : ℝ) := by
        rw [pow_two, coeff_mul]
        apply (norm_sum_le _ _).trans
        calc
          ∑ ij ∈ Finset.antidiagonal n, ‖coeff ij.1 w * coeff ij.2 w‖ ≤
              ∑ ij ∈ Finset.antidiagonal n,
                (M * Q ^ ij.1 * (catalan ij.1 : ℝ)) *
                  (M * Q ^ ij.2 * (catalan ij.2 : ℝ)) := by
            apply Finset.sum_le_sum
            intro ij hij
            have hij' := Finset.mem_antidiagonal.mp hij
            rw [norm_mul]
            exact mul_le_mul (ih ij.1 (by omega)) (ih ij.2 (by omega))
              (norm_nonneg _) (by positivity)
          _ = ∑ ij ∈ Finset.antidiagonal n,
              (M ^ 2 * Q ^ n) * ((catalan ij.1 : ℝ) * (catalan ij.2 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro ij hij
            have hij' := Finset.mem_antidiagonal.mp hij
            calc
              _ = M ^ 2 * (Q ^ ij.1 * Q ^ ij.2) *
                  ((catalan ij.1 : ℝ) * (catalan ij.2 : ℝ)) := by ring
              _ = _ := by rw [← pow_add, hij']
          _ = M ^ 2 * Q ^ n * (catalan (n + 1) : ℝ) := by
            rw [← Finset.mul_sum, ← hcat]
      rw [heq]
      calc
        ‖b * coeff n w + c * coeff n (w ^ 2)‖ ≤
            ‖b‖ * ‖coeff n w‖ + ‖c‖ * ‖coeff n (w ^ 2)‖ := by
          simpa only [norm_mul] using norm_add_le (b * coeff n w) (c * coeff n (w ^ 2))
        _ ≤ ‖b‖ * (M * Q ^ n * (catalan n : ℝ)) +
            ‖c‖ * (M ^ 2 * Q ^ n * (catalan (n + 1) : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left (ih n (by omega)) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hsquare (norm_nonneg _))
        _ ≤ ‖b‖ * (M * Q ^ n * (catalan (n + 1) : ℝ)) +
            ‖c‖ * (M ^ 2 * Q ^ n * (catalan (n + 1) : ℝ)) := by
          gcongr
        _ = (‖b‖ + ‖c‖ * M) * (M * Q ^ n * (catalan (n + 1) : ℝ)) := by ring
        _ ≤ Q * (M * Q ^ n * (catalan (n + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hbc (by positivity)
        _ = M * Q ^ (n + 1) * (catalan (n + 1) : ℝ) := by rw [pow_succ]; ring

/-- The scalar quadratic recursion has a positive native analytic radius. -/
theorem radius_pos_of_quadratic (w : PowerSeries ℝ) {a b c : ℝ}
    (hw : w = C a + X * (C b * w + C c * w ^ 2)) :
    0 < (FormalMultilinearSeries.ofScalars ℝ (fun n ↦ coeff n w)).radius := by
  let M := ‖a‖ + 1
  let Q := ‖b‖ + ‖c‖ * M + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hbound := norm_coeff_le_catalan_of_quadratic w hw hM.le
    (show ‖a‖ ≤ M by dsimp [M]; linarith) hQ.le
    (show ‖b‖ + ‖c‖ * M ≤ Q by dsimp [Q]; linarith)
  let r : ℝ≥0 := ⟨(4 * Q)⁻¹, by positivity⟩
  have hr : 0 < (r : ℝ≥0∞) :=
    ENNReal.coe_pos.mpr (show (0 : ℝ) < (4 * Q)⁻¹ by positivity)
  apply hr.trans_le
  apply (FormalMultilinearSeries.ofScalars ℝ (fun n ↦ coeff n w)).le_radius_of_bound M
    (r := r)
  intro n
  have hcat : (catalan n : ℝ) ≤ (4 : ℝ) ^ n := by
    have hn : catalan n ≤ 4 ^ n := by
      rw [catalan_eq_centralBinom_div]
      exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow n)
    exact_mod_cast hn
  calc
    ‖FormalMultilinearSeries.ofScalars ℝ (fun n ↦ coeff n w) n‖ * (r : ℝ) ^ n ≤
        (M * (4 * Q) ^ n) * (r : ℝ) ^ n := by
      rw [FormalMultilinearSeries.ofScalars_norm]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        ‖coeff n w‖ ≤ M * Q ^ n * (catalan n : ℝ) := hbound n
        _ ≤ M * Q ^ n * (4 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left hcat (by positivity)
        _ = M * (4 * Q) ^ n := by rw [mul_pow]; ring
    _ = M := by
      change (M * (4 * Q) ^ n) * ((4 * Q)⁻¹) ^ n = M
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (by positivity), one_pow, mul_one]

/-- Multiplication by the formal variable preserves a positive analytic radius. -/
theorem radius_pos_X_mul (w : PowerSeries ℝ)
    (hw : 0 < (FormalMultilinearSeries.ofScalars ℝ (fun n ↦ coeff n w)).radius) :
    0 < (FormalMultilinearSeries.ofScalars ℝ (fun n ↦ coeff n (X * w))).radius := by
  let p := FormalMultilinearSeries.ofScalars ℝ (fun n ↦ coeff n (X * w))
  let q := FormalMultilinearSeries.ofScalars ℝ (fun n ↦ coeff n w)
  have hr : q.radius ≤ p.shift.radius := by
    apply FormalMultilinearSeries.radius_le_of_le
    intro n
    change ‖(p (n + 1)).curryRight‖ ≤ ‖q n‖
    simp only [ContinuousMultilinearMap.curryRight_norm, p, q,
      FormalMultilinearSeries.ofScalars_norm, coeff_succ_X_mul, le_refl]
  simpa only [FormalMultilinearSeries.radius_shift] using hw.trans_le hr

/-- A zero-constant quadratic branch with a nonzero linear coefficient converges.
Factoring its zero constant term reduces it to a recursion whose coefficients
at each step depend only on earlier degrees. -/
theorem radius_pos_of_zero_constant_quadratic (v : PowerSeries ℝ) {ρ α β κ : ℝ}
    (hρ : ρ ≠ 0) (hv₀ : constantCoeff v = 0)
    (hv : (C ρ - C β * X) * v = C α * X + C κ * v ^ 2) :
    0 < (FormalMultilinearSeries.ofScalars ℝ (fun n ↦ coeff n v)).radius := by
  let w : PowerSeries ℝ := mk fun n ↦ coeff (n + 1) v
  have hvw : v = X * w := by simpa [hv₀, w] using eq_X_mul_shift_add_const v
  have heq : C ρ * w = C α + X * (C β * w + C κ * w ^ 2) := by
    apply X_mul_injective
    calc
      X * (C ρ * w) = (C ρ - C β * X) * (X * w) + C β * X * (X * w) := by ring
      _ = C α * X + C κ * (X * w) ^ 2 + C β * X * (X * w) := by
        rw [← hvw, hv]
      _ = X * (C α + X * (C β * w + C κ * w ^ 2)) := by ring
  have hw : w = C (α / ρ) + X * (C (β / ρ) * w + C (κ / ρ) * w ^ 2) := by
    calc
      w = C ρ⁻¹ * (C ρ * w) := by rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hρ]; simp
      _ = C ρ⁻¹ * (C α + X * (C β * w + C κ * w ^ 2)) := congrArg (C ρ⁻¹ * ·) heq
      _ = C (α / ρ) + X * (C (β / ρ) * w + C (κ / ρ) * w ^ 2) := by
        simp only [div_eq_mul_inv, map_mul]
        ring
  rw [hvw]
  exact radius_pos_X_mul w (radius_pos_of_quadratic w hw)

end PowerSeries
