/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.EnergyGrowth

/-!
# Oscillation decay without bounded mean energy

A perturbative mean-energy estimate first gives an arbitrarily small power
loss. Inserting that bound into quadratic oscillation decay yields a positive
Campanato exponent. This argument does not require the mean energy to remain
bounded as the radius tends to zero.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Campanato

/-- Coupled mean-energy and quadratic oscillation estimates imply positive
power decay on a uniformly small ball. Only finite initial energies occur
in the conclusion; boundedness at smaller scales is derived. -/
theorem exists_perturbative_oscillation_decay
    (n : ℕ) {A B D H γ R : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hD : 0 < D) (hH : 0 ≤ H)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ R ∧ 0 < C ∧
      ∀ E Φ : ℝ → ℝ,
        (∀ s, 0 < s → s ≤ ρ → 0 ≤ E s) →
        (∀ s, 0 < s → s ≤ ρ → 0 ≤ Φ s) →
        (∀ r s, 0 < r → r ≤ s → s ≤ ρ → E r ≤ (s / r) ^ n * E s) →
        (∀ r s, 0 < r → r ≤ s → s ≤ ρ → Φ r ≤ (s / r) ^ n * Φ s) →
        (∀ r s, 0 < r → r ≤ s / 4 → s ≤ ρ →
          E r ≤ A * E s + B * (s / r) ^ n * s ^ (2 * γ) * (1 + E s)) →
        (∀ r s, 0 < r → r ≤ s / 8 → s ≤ ρ →
          Φ r ≤ D * (r / s) ^ 2 * Φ s +
            H * (s / r) ^ n * s ^ (2 * γ) * (1 + E s)) →
        ∀ r, 0 < r → r ≤ ρ →
          Φ r ≤ C * (r / ρ) ^ γ * (Φ ρ + E ρ + 1) := by
  obtain ⟨ρ, L, hρ, hρR, hL, henergy⟩ :=
    exists_perturbative_energy_growth n hA hB (by positivity : 0 < 2 * γ) hγ hR
  obtain ⟨τ, hτ, hτ8, hscale⟩ :=
    exists_quadratic_decay_scale_le hγ2 hD (by norm_num : (0 : ℝ) < 1 / 8)
  let Q := τ ^ γ
  let T := τ⁻¹ ^ n / Q
  let J := H * τ⁻¹ ^ n * (1 + L) * ρ ^ γ
  let N := 2 * J * ρ ^ γ / Q
  have hQ : 0 < Q := Real.rpow_pos_of_pos hτ _
  have hT : 0 < T := by dsimp [T]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨ρ, T * (1 + N), hρ, hρR, by positivity, ?_⟩
  intro E Φ hE hΦ hEmono hΦmono hEstep hΦstep r hr hrρ
  have hEg := henergy E hE hEmono hEstep
  have herror (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ) :
      s ^ (2 * γ) * (1 + E s) ≤
        (1 + L) * ρ ^ γ * (E ρ + 1) * s ^ γ := by
    have hp : s ^ (2 * γ) = s ^ γ * s ^ γ := by rw [two_mul, Real.rpow_add hs]
    have he := mul_le_mul_of_nonneg_left (hEg s hs hsρ)
      (Real.rpow_nonneg hs.le (2 * γ))
    have hc : s ^ (2 * γ) * (L * (ρ / s) ^ γ * (E ρ + 1)) =
        L * ρ ^ γ * (E ρ + 1) * s ^ γ := by
      rw [Real.div_rpow hρ.le hs.le, hp]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hs γ)]
    rw [hc] at he
    have hsbound : s ^ (2 * γ) ≤ ρ ^ γ * (E ρ + 1) * s ^ γ := by
      rw [hp]
      gcongr
      exact (Real.rpow_le_rpow hs.le hsρ hγ.le).trans
        (le_mul_of_one_le_right (by positivity) (by linarith [hE ρ hρ le_rfl]))
    nlinarith only [he, hsbound]
  have hstep (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ) :
      Φ (τ * s) ≤ (D * τ ^ 2) * Φ s + (J * (E ρ + 1)) * s ^ γ := by
    have he := hΦstep (τ * s) s (mul_pos hτ hs) (by nlinarith) hsρ
    rw [mul_div_cancel_right₀ τ hs.ne', show s / (τ * s) = τ⁻¹ by field_simp] at he
    refine he.trans ?_
    have hb := mul_le_mul_of_nonneg_left (herror s hs hsρ)
      (mul_nonneg hH (pow_nonneg (inv_nonneg.mpr hτ.le) n))
    dsimp only [J]
    nlinarith only [hb]
  have hd := decay_at_all_radii hγ.le hτ (by linarith : τ < 1)
    (mul_nonneg hD.le (sq_nonneg τ)) (mul_nonneg hJ (by linarith [hE ρ hρ le_rfl]))
    hscale n Φ (hΦ ρ hρ le_rfl) hΦmono hstep hr hrρ
  have houter : Φ ρ + 2 * (J * (E ρ + 1)) * ρ ^ γ / Q ≤
      (1 + N) * (Φ ρ + E ρ + 1) := by
    have he : 0 ≤ E ρ + 1 := by linarith [hE ρ hρ le_rfl]
    have hp := mul_nonneg hN (hΦ ρ hρ le_rfl)
    dsimp only [N] at hp ⊢
    simp only [div_eq_mul_inv] at hp ⊢
    nlinarith only [he, hp]
  calc
    _ ≤ _ := hd
    _ ≤ T * (r / ρ) ^ γ * ((1 + N) * (Φ ρ + E ρ + 1)) := by gcongr
    _ = _ := by ring

end PDE.Elliptic.Regularity.Campanato
