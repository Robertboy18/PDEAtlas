/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Cells

/-!
# Sums of squared tables on a cover of the quadrant by rows of cells

The quadrant `[0, π/2]²` is covered by the cells between the `β` rows `pos r · π / (2 Nβ)`,
`r ≤ R`, each row of cells cut in `θ` at the multiples of `cst r · π / (2 Nθ)`. If the sum of the
squared tables is at most `m` minus the cell error at the vertices of every cell, it is at most
`m` on the quadrant (`sum_sq_le_of_rowCover`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset Set

variable {Mβ Mθ : ℕ}

/-- The cell error of the cell row `r`. -/
def rowCellError (A C : ℝ) (pos cst : ℕ → ℕ) (Nβ Nθ r : ℕ) : ℝ :=
  A * (((pos (r + 1) : ℝ) - pos r) * (Real.pi / (2 * Nβ))) ^ 2 / 8 +
    C * ((cst r : ℝ) * (Real.pi / (2 * Nθ))) ^ 2 / 8

private theorem pos_le_pos {R : ℕ} (pos : ℕ → ℕ) (hmono : ∀ r < R, pos r < pos (r + 1))
    {s t : ℕ} (hst : s ≤ t) (htR : t ≤ R) : pos s ≤ pos t := by
  induction t with
  | zero => rw [Nat.le_zero.mp hst]
  | succ t ih =>
    rcases hst.lt_or_eq with h | h
    · exact (ih (by omega) (by omega)).trans (hmono t (by omega)).le
    · rw [h]

private theorem exists_row {R : ℕ} (pos : ℕ → ℕ) (hR : 0 < R) (hpos0 : pos 0 = 0)
    (hmono : ∀ r < R, pos r < pos (r + 1)) {y : ℝ} (hy0 : 0 ≤ y) (hyR : y ≤ pos R) :
    ∃ r < R, (pos r : ℝ) ≤ y ∧ y ≤ pos (r + 1) := by
  classical
  set r := Nat.findGreatest (fun r ↦ (pos r : ℝ) ≤ y) R
  have hr : (pos r : ℝ) ≤ y := by
    have := Nat.findGreatest_spec (P := fun r ↦ (pos r : ℝ) ≤ y) (m := 0) (Nat.zero_le R)
      (by simp [hpos0, hy0])
    exact this
  have hrR : r ≤ R := Nat.findGreatest_le R
  rcases hrR.lt_or_eq with hlt | heq
  · refine ⟨r, hlt, hr, ?_⟩
    by_contra hc
    have hc' := (not_le.mp hc).le
    have := Nat.le_findGreatest (P := fun r ↦ (pos r : ℝ) ≤ y) (Nat.succ_le_of_lt hlt) hc'
    omega
  · refine ⟨R - 1, by omega, ?_, ?_⟩
    · have h1 : (pos (R - 1) : ℝ) ≤ pos R := by
        exact_mod_cast pos_le_pos pos hmono (by omega : R - 1 ≤ R) le_rfl
      rw [← heq] at h1 ⊢
      exact h1.trans hr
    · rw [show R - 1 + 1 = R by omega]; exact hyR

private theorem exists_cell {N c : ℕ} (hc : 0 < c) (hcN : N % c = 0) (hN : 0 < N) {y : ℝ}
    (hy0 : 0 ≤ y) (hyN : y ≤ N) :
    ∃ n : ℕ, (n * c : ℝ) ≤ y ∧ y ≤ ((n + 1) * c : ℝ) ∧ (n + 1) * c ≤ N := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hNc : c ≤ N := Nat.le_of_dvd hN (Nat.dvd_of_mod_eq_zero hcN)
  set q := N / c
  have hq : q * c = N := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hcN)
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff hc).mpr hNc
  set f := ⌊y / c⌋₊
  have hf : (f : ℝ) ≤ y / c := Nat.floor_le (div_nonneg hy0 hc'.le)
  have hf' : y / c < f + 1 := Nat.lt_floor_add_one _
  by_cases hfq : f + 1 ≤ q
  · refine ⟨f, ?_, ?_, by nlinarith⟩
    · rw [le_div_iff₀ hc'] at hf; linarith
    · rw [div_lt_iff₀ hc'] at hf'; linarith
  · refine ⟨q - 1, ?_, ?_, ?_⟩
    · have : (((q - 1 : ℕ) : ℝ)) ≤ f := by exact_mod_cast (by omega : q - 1 ≤ f)
      rw [le_div_iff₀ hc'] at hf
      nlinarith
    · have hqN : ((q : ℝ)) * c = N := by exact_mod_cast hq
      rw [show (((q - 1 : ℕ) : ℝ) + 1) = q by rw [Nat.cast_sub hq1]; ring]
      linarith
    · rw [show q - 1 + 1 = q by omega, hq]

/-- **Sums of squares on a cover by rows of cells.** -/
theorem sum_sq_le_of_rowCover {ι : Type*} [Fintype ι] (T : ι → TrigPoly2 Mβ Mθ ℝ)
    {m A C : ℝ} (hA : sqSumβBound T ≤ A) (hC : sqSumθBound T ≤ C) {R Nβ Nθ : ℕ}
    (pos cst : ℕ → ℕ) (hR : 0 < R) (hNθ : 0 < Nθ) (hpos0 : pos 0 = 0) (hposR : pos R = Nβ)
    (hmono : ∀ r < R, pos r < pos (r + 1)) (hcst : ∀ r < R, 0 < cst r ∧ Nθ % cst r = 0)
    (hv : ∀ r < R, ∀ x ∈ ({pos r, pos (r + 1)} : Set ℕ), ∀ b ≤ Nθ, b % cst r = 0 →
      ∑ i, (T i).eval (x * (Real.pi / (2 * Nβ))) (b * (Real.pi / (2 * Nθ))) ^ 2 ≤
        m - rowCellError A C pos cst Nβ Nθ r)
    {β θ : ℝ} (hβ : β ∈ Icc 0 (Real.pi / 2)) (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    ∑ i, (T i).eval β θ ^ 2 ≤ m := by
  have hNβ : 0 < Nβ := hposR ▸ (Nat.zero_le _).trans_lt
    (by have := hmono 0 hR; rw [hpos0] at this; exact (this.trans_le
      (pos_le_pos pos hmono (by omega) le_rfl)))
  set hb := Real.pi / (2 * Nβ)
  set ht := Real.pi / (2 * Nθ)
  have hb0 : 0 < hb := by positivity
  have ht0 : 0 < ht := by positivity
  obtain ⟨r, hr, hra, hrb⟩ := exists_row pos hR hpos0 hmono (y := β / hb)
    (div_nonneg hβ.1 hb0.le) (by
      rw [div_le_iff₀ hb0, hposR]
      have : (Nβ : ℝ) * hb = Real.pi / 2 := by simp only [hb]; field_simp
      rw [this]; exact hβ.2)
  obtain ⟨hc0, hcN⟩ := hcst r hr
  obtain ⟨n, hna, hnb, hnN⟩ := exists_cell hc0 hcN hNθ (y := θ / ht)
    (div_nonneg hθ.1 ht0.le) (by
      rw [div_le_iff₀ ht0]
      have : (Nθ : ℝ) * ht = Real.pi / 2 := by simp only [ht]; field_simp
      rw [this]; exact hθ.2)
  have hab : (pos r : ℝ) * hb < pos (r + 1) * hb := by
    have := hmono r hr
    exact mul_lt_mul_of_pos_right (by exact_mod_cast this) hb0
  have hce : (n * cst r : ℝ) * ht < ((n + 1) * cst r : ℝ) * ht := by
    have : (0 : ℝ) < cst r := by exact_mod_cast hc0
    exact mul_lt_mul_of_pos_right (by nlinarith) ht0
  have hvert : ∀ x ∈ ({pos r, pos (r + 1)} : Set ℕ), ∀ b : ℕ, b ≤ Nθ → b % cst r = 0 →
      ∑ i, (T i).eval ((x : ℝ) * hb) ((b : ℝ) * ht) ^ 2 ≤
        m - rowCellError A C pos cst Nβ Nθ r := hv r hr
  have hn1 : n * cst r ≤ Nθ := by nlinarith
  have hcell := sum_sq_eval_le_of_cell T hab hce
    (m := m - rowCellError A C pos cst Nβ Nθ r)
    (by simpa using hvert (pos r) (by simp) (n * cst r) hn1 (by simp))
    (by simpa using hvert (pos r) (by simp) ((n + 1) * cst r) hnN (by simp))
    (by simpa using hvert (pos (r + 1)) (by simp) (n * cst r) hn1 (by simp))
    (by simpa using hvert (pos (r + 1)) (by simp) ((n + 1) * cst r) hnN (by simp))
    (x := β) (y := θ)
    ⟨by rw [le_div_iff₀ hb0] at hra; linarith, by rw [div_le_iff₀ hb0] at hrb; linarith⟩
    ⟨by rw [le_div_iff₀ ht0] at hna; linarith, by rw [div_le_iff₀ ht0] at hnb; linarith⟩
  refine hcell.trans ?_
  have e1 : (pos (r + 1) : ℝ) * hb - pos r * hb = ((pos (r + 1) : ℝ) - pos r) * hb := by ring
  have e2 : ((n + 1) * cst r : ℝ) * ht - (n * cst r) * ht = (cst r : ℝ) * ht := by ring
  rw [e1, e2]
  unfold rowCellError
  have h1 : sqSumβBound T * (((pos (r + 1) : ℝ) - pos r) * hb) ^ 2 / 8 ≤
      A * (((pos (r + 1) : ℝ) - pos r) * hb) ^ 2 / 8 := by gcongr
  have h2 : sqSumθBound T * ((cst r : ℝ) * ht) ^ 2 / 8 ≤ C * ((cst r : ℝ) * ht) ^ 2 / 8 := by
    gcongr
  linarith

end PDE.Analysis.TrigPoly2
