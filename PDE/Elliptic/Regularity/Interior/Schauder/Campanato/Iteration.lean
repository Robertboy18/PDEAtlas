/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Scale iteration for mean-square oscillation

A quadratic homogeneous decay term can be absorbed at one fixed radius ratio
for every exponent strictly below two. Iterating that ratio and using the
volume-ratio restriction bound gives decay at all intermediate radii. These
scalar estimates retain explicit dependence on the forcing coefficient and
the initial energy.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Campanato

/-- A sufficiently small radius ratio, below any prescribed positive cap,
absorbs quadratic decay into a strictly smaller power. -/
theorem exists_quadratic_decay_scale_le {β A η : ℝ}
    (hβ : β < 2) (hA : 0 < A) (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ η ∧ A * τ ^ 2 ≤ τ ^ β / 2 := by
  let δ : ℝ := ((2 * A)⁻¹) ^ (2 - β)⁻¹
  let τ : ℝ := min η δ
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  have hτ : 0 < τ := lt_min hη hδ
  refine ⟨τ, hτ, min_le_left _ _, ?_⟩
  have hp : τ ^ (2 - β) ≤ (2 * A)⁻¹ := by
    calc
      _ ≤ δ ^ (2 - β) :=
        Real.rpow_le_rpow hτ.le (min_le_right _ _) (by linarith)
      _ = _ := Real.rpow_inv_rpow (by positivity) (by linarith)
  have hsplit : τ ^ 2 = τ ^ (2 - β) * τ ^ β := by
    rw [← Real.rpow_add hτ]
    norm_num
  rw [hsplit]
  calc
    _ ≤ A * ((2 * A)⁻¹ * τ ^ β) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      exact mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hτ.le _)
    _ = _ := by field_simp

/-- A sufficiently small radius ratio absorbs quadratic decay into any
strictly smaller power. The ratio depends only on the constant and exponent. -/
theorem exists_quadratic_decay_scale {β A : ℝ} (hβ : β < 2) (hA : 0 < A) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ A * τ ^ 2 ≤ τ ^ β / 2 :=
  exists_quadratic_decay_scale_le hβ hA (by norm_num)

private theorem sequence_decay
    {a q b : ℝ} (ha : 0 ≤ a) (hq : 0 < q) (hb : 0 ≤ b) (haq : a ≤ q / 2)
    (u : ℕ → ℝ) (hu0 : 0 ≤ u 0)
    (hstep : ∀ k, u (k + 1) ≤ a * u k + b * q ^ k) (k : ℕ) :
    u k ≤ q ^ k * (u 0 + 2 * b / q) := by
  let L := u 0 + 2 * b / q
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbL : b ≤ q / 2 * L := by
    dsimp [L]
    have hcancel : q * (2 * b / q) = 2 * b := by field_simp
    nlinarith [mul_nonneg hq.le hu0]
  induction k with
  | zero =>
    simp only [pow_zero, one_mul]
    exact le_add_of_nonneg_right (by positivity)
  | succ k ih =>
    calc
      _ ≤ a * (q ^ k * L) + b * q ^ k :=
        (hstep k).trans (add_le_add (mul_le_mul_of_nonneg_left ih ha) le_rfl)
      _ ≤ q / 2 * (q ^ k * L) + (q / 2 * L) * q ^ k :=
        add_le_add (mul_le_mul_of_nonneg_right haq (mul_nonneg (pow_nonneg hq.le _) hL))
          (mul_le_mul_of_nonneg_right hbL (pow_nonneg hq.le _))
      _ = _ := by rw [pow_succ]; ring

/-- Fixed-ratio decay and the volume-ratio bound imply power decay at every
radius. The forcing contributes additively inside the initial energy factor. -/
theorem decay_at_all_radii
    {β τ a b R : ℝ} (hβ : 0 ≤ β) (hτ : 0 < τ) (hτ1 : τ < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haq : a ≤ τ ^ β / 2)
    (n : ℕ) (Φ : ℝ → ℝ) (hΦ : 0 ≤ Φ R)
    (hmono : ∀ r s, 0 < r → r ≤ s → s ≤ R → Φ r ≤ (s / r) ^ n * Φ s)
    (hstep : ∀ s, 0 < s → s ≤ R → Φ (τ * s) ≤ a * Φ s + b * s ^ β)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    Φ r ≤ (τ⁻¹ ^ n / τ ^ β) * (r / R) ^ β *
      (Φ R + 2 * b * R ^ β / τ ^ β) := by
  have hR : 0 < R := by linarith
  let q := τ ^ β
  have hq : 0 < q := Real.rpow_pos_of_pos hτ _
  have hpower (k : ℕ) : (τ ^ k * R) ^ β = q ^ k * R ^ β := by
    rw [Real.mul_rpow (pow_nonneg hτ.le _) hR.le,
      ← Real.rpow_natCast_mul hτ.le, mul_comm (k : ℝ) β,
      Real.rpow_mul_natCast hτ.le]
  have hseq (k : ℕ) :
      Φ (τ ^ k * R) ≤ q ^ k * (Φ R + 2 * b * R ^ β / q) := by
    have h0 : 0 ≤ Φ (τ ^ 0 * R) := by simpa using hΦ
    have hs (j : ℕ) :
        Φ (τ ^ (j + 1) * R) ≤
          a * Φ (τ ^ j * R) + (b * R ^ β) * q ^ j := by
      have hsj : τ ^ j * R ≤ R :=
        (mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.le hτ1.le) hR.le).trans_eq
          (one_mul R)
      have h := hstep (τ ^ j * R) (mul_pos (pow_pos hτ _) hR) hsj
      rw [hpower] at h
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
    simpa only [pow_zero, one_mul, mul_div_assoc, mul_assoc] using
      sequence_decay ha hq (mul_nonneg hb (Real.rpow_nonneg hR.le _)) haq
        (fun j ↦ Φ (τ ^ j * R)) h0 hs k
  obtain ⟨k, hklt, hkle⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hR) ((div_le_one hR).mpr hrR) hτ hτ1
  have hsk : 0 < τ ^ k * R := mul_pos (pow_pos hτ _) hR
  have hrsk : r ≤ τ ^ k * R := (div_le_iff₀ hR).mp hkle
  have hskR : τ ^ k * R ≤ R :=
    (mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.le hτ1.le) hR.le).trans_eq (one_mul R)
  have hratio : (τ ^ k * R / r) ^ n ≤ τ⁻¹ ^ n := by
    apply pow_le_pow_left₀ (div_nonneg hsk.le hr.le) _ n
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hr hτ).mpr
    have hkr := (lt_div_iff₀ hR).mp hklt
    rw [pow_succ] at hkr
    nlinarith
  have hqk : q ^ k ≤ (r / R) ^ β / q := by
    apply (le_div_iff₀ hq).mpr
    have h := Real.rpow_le_rpow (pow_nonneg hτ.le _) hklt.le hβ
    rw [← Real.rpow_natCast_mul hτ.le, mul_comm (↑(k + 1) : ℝ) β,
      Real.rpow_mul_natCast hτ.le, pow_succ] at h
    exact h
  have hL : 0 ≤ Φ R + 2 * b * R ^ β / q := by positivity
  calc
    _ ≤ (τ ^ k * R / r) ^ n * Φ (τ ^ k * R) := hmono r _ hr hrsk hskR
    _ ≤ (τ ^ k * R / r) ^ n * (q ^ k * (Φ R + 2 * b * R ^ β / q)) :=
      mul_le_mul_of_nonneg_left (hseq k) (pow_nonneg (div_nonneg hsk.le hr.le) _)
    _ ≤ τ⁻¹ ^ n * ((r / R) ^ β / q * (Φ R + 2 * b * R ^ β / q)) :=
      mul_le_mul hratio (mul_le_mul_of_nonneg_right hqk hL)
        (mul_nonneg (pow_nonneg hq.le _) hL) (pow_nonneg (inv_nonneg.mpr hτ.le) _)
    _ = _ := by dsimp only [q]; ring

end PDE.Elliptic.Regularity.Campanato
