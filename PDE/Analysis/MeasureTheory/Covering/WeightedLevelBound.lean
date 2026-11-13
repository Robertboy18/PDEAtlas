/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Weighted bounds from geometric level decay

Choosing an integer weight exponent makes the decay beat the growth of the
levels. The resulting weighted bound uses only natural-number powers.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- A sufficiently large integer exponent makes geometric decay dominate
the dimension-dependent level growth. -/
theorem exists_nat_weight_exponent
    {M δ : ℝ} (hM : 1 < M) (hδ : 0 ≤ δ) (hδ₁ : δ < 1) (n : ℕ) :
    ∃ β : ℕ, 0 < β ∧ M ^ n * δ ^ β ≤ 1 := by
  have hMn : 0 < M ^ n := pow_pos (zero_lt_one.trans hM) n
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hMn) hδ₁
  refine ⟨k + 1, Nat.succ_pos _, ?_⟩
  have hpow : δ ^ (k + 1) ≤ δ ^ k := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hδ k) hδ₁.le
  have h := mul_le_mul_of_nonneg_left (hpow.trans hk.le) hMn.le
  simpa only [mul_inv_cancel₀ hMn.ne'] using h

/-- A power-law radius lower bound, compared with geometric level decay,
uniformly bounds the weighted height. -/
theorem exists_weighted_height_bound
    {M δ : ℝ} (hM : 1 < M) (hδ : 0 ≤ δ)
    {n β : ℕ} (hn : 0 < n) (hdecay : M ^ n * δ ^ β ≤ 1)
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ h d : ℝ, 0 < h → 0 < d → d ≤ 1 →
      (∀ k : ℕ, 4 * M ^ k ≤ h → c * d ^ n ≤ δ ^ k) →
      h * d ^ β ≤ C := by
  let C₀ := (4 * M) ^ n * (c⁻¹) ^ β
  refine ⟨max 4 (max 1 C₀), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro h d hh hd hd₁ hlevels
  by_cases hh₄ : h < 4
  · have hpow : d ^ β ≤ 1 := pow_le_one₀ hd.le hd₁
    exact ((mul_le_of_le_one_right hh.le hpow).trans hh₄.le).trans (le_max_left _ _)
  · have hh₄' : 1 ≤ h / 4 := by rw [le_div_iff₀ (by norm_num)]; linarith
    obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near hh₄' hM
    have hlow : 4 * M ^ k ≤ h := by linarith [(le_div_iff₀ (by norm_num)).mp hklo]
    have hhigh : h ≤ 4 * M ^ (k + 1) := by
      have h := (div_lt_iff₀ (by norm_num)).mp hkhi
      linarith
    have hdensity : d ^ n ≤ c⁻¹ * δ ^ k := by
      have h := hlevels k hlow
      exact (le_inv_mul_iff₀ hc).mpr h
    have hp := pow_le_pow_left₀ (pow_nonneg hd.le n) hdensity β
    have hhp := pow_le_pow_left₀ hh.le hhigh n
    have hcombined := mul_le_mul hhp hp (pow_nonneg (pow_nonneg hd.le n) β)
      (pow_nonneg (by positivity) n)
    have halgebra :
        (4 * M ^ (k + 1)) ^ n * (c⁻¹ * δ ^ k) ^ β =
          C₀ * (M ^ n * δ ^ β) ^ k := by
      dsimp [C₀]
      simp only [pow_succ, mul_pow, ← pow_mul]
      rw [Nat.mul_comm k n, Nat.mul_comm k β]
      ring
    have hHpower : (h * d ^ β) ^ n ≤ C₀ := by
      calc
        (h * d ^ β) ^ n = h ^ n * (d ^ n) ^ β := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm β n]
        _ ≤ (4 * M ^ (k + 1)) ^ n * (c⁻¹ * δ ^ k) ^ β := hcombined
        _ = C₀ * (M ^ n * δ ^ β) ^ k := halgebra
        _ ≤ C₀ := mul_le_of_le_one_right (by dsimp [C₀]; positivity)
          (pow_le_one₀ (mul_nonneg (pow_nonneg (zero_lt_one.trans hM).le n)
            (pow_nonneg hδ β)) hdecay)
    have hbound : h * d ^ β ≤ max 1 C₀ := by
      by_cases hlarge : 1 ≤ h * d ^ β
      · exact ((le_self_pow₀ hlarge hn.ne').trans hHpower).trans (le_max_right _ _)
      · exact (le_of_not_ge hlarge).trans (le_max_left _ _)
    exact hbound.trans (le_max_right _ _)

end PDE.Analysis
