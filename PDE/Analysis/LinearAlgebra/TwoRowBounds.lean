/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Positivity

/-!
# Bounds for a system with two separated rows

For equations `Aᵢ • (x₀ + rᵢ • x₁) = dᵢ`, lower bounds on `|Aᵢ|` and
`|r₀ - r₁|` control the solution. The unknowns and data can be vectors in any
real normed space. Subtraction of the normalized rows gives the estimate for
`x₁`; substitution in the first row gives the estimate for `x₀`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_normalized_row_le {k A : ℝ} {y d : E}
    (hk : 0 < k) (hA : k ≤ |A|) (h : A • y = d) :
    ‖y‖ ≤ ‖d‖ / k := by
  apply (le_div_iff₀ hk).mpr
  calc
    ‖y‖ * k ≤ |A| * ‖y‖ := by nlinarith [norm_nonneg y]
    _ = ‖d‖ := by rw [← Real.norm_eq_abs, ← norm_smul, h]

/-- The separated row slopes control the second unknown. The row amplitudes can have
either sign; no upper bound on the separation is needed. -/
theorem norm_snd_le_of_two_rows
    {k δ A₀ A₁ r₀ r₁ : ℝ} {x₀ x₁ d₀ d₁ : E}
    (hk : 0 < k) (hδ : 0 < δ) (hA₀ : k ≤ |A₀|) (hA₁ : k ≤ |A₁|)
    (hgap : δ ≤ |r₀ - r₁|)
    (h₀ : A₀ • (x₀ + r₀ • x₁) = d₀)
    (h₁ : A₁ • (x₀ + r₁ • x₁) = d₁) :
    ‖x₁‖ ≤ (‖d₀‖ + ‖d₁‖) / (k * δ) := by
  have hrow₀ := norm_normalized_row_le hk hA₀ h₀
  have hrow₁ := norm_normalized_row_le hk hA₁ h₁
  have hdiff : (r₀ - r₁) • x₁ = (x₀ + r₀ • x₁) - (x₀ + r₁ • x₁) := by
    simp only [sub_smul, add_sub_add_left_eq_sub]
  have hnorm : |r₀ - r₁| * ‖x₁‖ ≤ (‖d₀‖ + ‖d₁‖) / k := by
    calc
      |r₀ - r₁| * ‖x₁‖ = ‖(r₀ - r₁) • x₁‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖x₀ + r₀ • x₁‖ + ‖x₀ + r₁ • x₁‖ := by
        rw [hdiff]
        exact norm_sub_le _ _
      _ ≤ (‖d₀‖ + ‖d₁‖) / k := by rw [add_div]; exact add_le_add hrow₀ hrow₁
  rw [← div_div, le_div_iff₀ hδ]
  nlinarith [norm_nonneg x₁]

/-- Substitution in the first row bounds the first unknown, keeping the separate
contribution of the first datum and the size of the first slope. -/
theorem norm_fst_le_of_two_rows
    {k δ A₀ A₁ r₀ r₁ : ℝ} {x₀ x₁ d₀ d₁ : E}
    (hk : 0 < k) (hδ : 0 < δ) (hA₀ : k ≤ |A₀|) (hA₁ : k ≤ |A₁|)
    (hgap : δ ≤ |r₀ - r₁|)
    (h₀ : A₀ • (x₀ + r₀ • x₁) = d₀)
    (h₁ : A₁ • (x₀ + r₁ • x₁) = d₁) :
    ‖x₀‖ ≤ ‖d₀‖ / k + |r₀| * ((‖d₀‖ + ‖d₁‖) / (k * δ)) := by
  calc
    ‖x₀‖ = ‖(x₀ + r₀ • x₁) - r₀ • x₁‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖x₀ + r₀ • x₁‖ + |r₀| * ‖x₁‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using
        norm_sub_le (x₀ + r₀ • x₁) (r₀ • x₁)
    _ ≤ _ := add_le_add (norm_normalized_row_le hk hA₀ h₀)
      (mul_le_mul_of_nonneg_left
        (norm_snd_le_of_two_rows hk hδ hA₀ hA₁ hgap h₀ h₁) (abs_nonneg r₀))

end PDE.Analysis
