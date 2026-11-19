/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Real.Sqrt
import CAS.ExactTactic

/-!
# Equal time steps at parabolic scales

A spatial segment of length at most `R` can be subdivided into equal steps
shorter than the parabolic radius for any prescribed positive elapsed time.
The same subdivision keeps the radius bounded and leaves a prescribed
positive margin behind each time step.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

/-- Choose the number of equal time steps before any field is considered.
The bound `R / N ≤ r` controls spatial travel, while `2 r² < η` preserves
an earlier temporal margin. -/
theorem exists_parabolic_equal_time_steps
    {κ Δ R η : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hR : 0 < R) (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ R / (N : ℝ) ≤ r ∧
      2 * r ^ 2 < η ∧ (N : ℝ) * (κ * r ^ 2) = Δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max 0 (max (Δ / (κ * R ^ 2))
      (max (κ * R ^ 2 / Δ) (2 * Δ / (κ * η)))))
  have hNpos : 0 < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hcap : Δ / (κ * R ^ 2) < (N : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hN
  have htravel : κ * R ^ 2 / Δ < (N : ℝ) :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt hN
  have hmargin : 2 * Δ / (κ * η) < (N : ℝ) :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt hN
  have hden : 0 < κ * (N : ℝ) := mul_pos hκ hNpos
  let r := √(Δ / (κ * (N : ℝ)))
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hΔ hden)
  have hr₂ : r ^ 2 = Δ / (κ * (N : ℝ)) := Real.sq_sqrt (div_nonneg hΔ.le hden.le)
  have hcap' : Δ < (N : ℝ) * (κ * R ^ 2) :=
    (div_lt_iff₀ (mul_pos hκ (sq_pos_of_pos hR))).mp hcap
  have htravel' : κ * R ^ 2 < (N : ℝ) * Δ := (div_lt_iff₀ hΔ).mp htravel
  have hmargin' : 2 * Δ < (N : ℝ) * (κ * η) :=
    (div_lt_iff₀ (mul_pos hκ hη)).mp hmargin
  have hrR : r ≤ R := by
    have hsq : r ^ 2 ≤ R ^ 2 := by
      rw [hr₂]
      apply (div_le_iff₀ hden).mpr
      nlinarith
    nlinarith
  have hstep : R / (N : ℝ) ≤ r := by
    have hfrac : R ^ 2 / (N : ℝ) ≤ Δ / κ :=
      (div_le_div_iff₀ hNpos hκ).mpr (by nlinarith)
    have hsq : (R / (N : ℝ)) ^ 2 ≤ r ^ 2 := by
      calc
        (R / (N : ℝ)) ^ 2 = (R ^ 2 / (N : ℝ)) / (N : ℝ) := by cas
        _ ≤ (Δ / κ) / (N : ℝ) := div_le_div_of_nonneg_right hfrac hNpos.le
        _ = r ^ 2 := by rw [hr₂]; cas
    have hfracpos := div_pos hR hNpos
    nlinarith
  have htime : 2 * r ^ 2 < η := by
    have hhalf : r ^ 2 < η / 2 := by
      rw [hr₂]
      apply (div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).mpr
      nlinarith
    linarith
  refine ⟨N, hNnat, r, hr, hrR, hstep, htime, ?_⟩
  have heq := (eq_div_iff hden.ne').mp hr₂
  nlinarith

end PDE.Analysis
