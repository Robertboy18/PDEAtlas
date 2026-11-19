/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Iteration

/-!
# Absorption of a vanishing energy perturbation

A volume-order comparison estimate with an error of order `s^θ` gives mean
energy growth at most `r^(-δ)` for every positive loss `δ`, after restricting
the outer radius. Multiplying the mean energy by `r^δ` reduces the argument
to the scale iteration. The initial mean energy is finite but need
not be bounded uniformly as the radius decreases.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Campanato

/-- A vanishing perturbation of volume-order energy decay allows an arbitrarily
small power loss. The radius and constant are uniform over all energies
satisfying the comparison and restriction estimates. -/
theorem exists_perturbative_energy_growth
    (n : ℕ) {A B θ δ R : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hθ : 0 < θ) (hδ : 0 < δ) (hR : 0 < R) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ R ∧ 0 < C ∧
      ∀ Φ : ℝ → ℝ,
        (∀ s, 0 < s → s ≤ ρ → 0 ≤ Φ s) →
        (∀ r s, 0 < r → r ≤ s → s ≤ ρ → Φ r ≤ (s / r) ^ n * Φ s) →
        (∀ r s, 0 < r → r ≤ s / 4 → s ≤ ρ →
          Φ r ≤ A * Φ s + B * (s / r) ^ n * s ^ θ * (1 + Φ s)) →
        ∀ r, 0 < r → r ≤ ρ →
          Φ r ≤ C * (ρ / r) ^ δ * (Φ ρ + 1) := by
  let t := ((2 * (A + 1))⁻¹) ^ δ⁻¹
  let τ := min (1 / 4) t
  have ht : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  have hτ : 0 < τ := lt_min (by norm_num) ht
  have hτ1 : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have habsorb : τ ^ δ * (A + 1) ≤ 1 / 2 := by
    have : τ ^ δ ≤ (2 * (A + 1))⁻¹ := (Real.rpow_le_rpow hτ.le (min_le_right _ _) hδ.le).trans_eq
      (Real.rpow_inv_rpow (by positivity) hδ.ne')
    calc _ ≤ (2 * (A + 1))⁻¹ * (A + 1) := by gcongr
      _ = _ := by field_simp
  let b := B * τ⁻¹ ^ n
  have hb : 0 ≤ b := by positivity
  let ρ := min R (((b + 1)⁻¹) ^ θ⁻¹)
  have hρ : 0 < ρ := lt_min hR (Real.rpow_pos_of_pos (by positivity) _)
  have hsmall : b * ρ ^ θ ≤ 1 := by
    have : ρ ^ θ ≤ (b + 1)⁻¹ := (Real.rpow_le_rpow hρ.le (min_le_right _ _) hθ.le).trans_eq
      (Real.rpow_inv_rpow (by positivity) hθ.ne')
    calc _ ≤ (b + 1) * (b + 1)⁻¹ := by gcongr; linarith
      _ = 1 := mul_inv_cancel₀ (by positivity)
  refine ⟨ρ, 2 * τ⁻¹ ^ n, hρ, min_le_left _ _, by positivity, ?_⟩
  intro Φ hΦ hmono hstep r hr hrρ
  let Ψ := fun s : ℝ ↦ s ^ δ * Φ s
  have hΨmono (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) (hsρ : s ≤ ρ) :
      Ψ r ≤ (s / r) ^ n * Ψ s := by
    calc r ^ δ * Φ r ≤ s ^ δ * ((s / r) ^ n * Φ s) :=
          mul_le_mul (Real.rpow_le_rpow hr.le hrs hδ.le) (hmono r s hr hrs hsρ)
            (hΦ r hr (hrs.trans hsρ)) (Real.rpow_nonneg (hr.le.trans hrs) δ)
      _ = _ := by ring
  have hΨstep (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ) :
      Ψ (τ * s) ≤ (τ ^ δ * (A + 1)) * Ψ s + τ ^ δ * b * ρ ^ (δ + θ) := by
    have hbsmall : b * s ^ θ ≤ 1 := le_trans (by gcongr) hsmall
    have he := hstep (τ * s) s (mul_pos hτ hs)
      ((mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le).trans_eq (by ring)) hsρ
    rw [show s / (τ * s) = τ⁻¹ by field_simp] at he
    have he' : Φ (τ * s) ≤ (A + 1) * Φ s + b * s ^ θ := by
      have hbΦ := mul_le_mul_of_nonneg_right hbsmall (hΦ s hs hsρ)
      dsimp only [b] at hbΦ
      nlinarith only [he, hbΦ]
    dsimp only [Ψ]
    calc _ ≤ (τ * s) ^ δ * ((A + 1) * Φ s + b * s ^ θ) := by gcongr
      _ = (τ ^ δ * (A + 1)) * (s ^ δ * Φ s) + τ ^ δ * b * s ^ (δ + θ) := by
        rw [Real.mul_rpow hτ.le hs.le, Real.rpow_add hs]
        ring
      _ ≤ _ := by gcongr
  have hdecay := decay_at_all_radii (β := 0) (by norm_num) hτ hτ1
    (show 0 ≤ τ ^ δ * (A + 1) by positivity)
    (show 0 ≤ τ ^ δ * b * ρ ^ (δ + θ) by positivity)
    (by simpa only [Real.rpow_zero] using habsorb) n Ψ
    (mul_nonneg (Real.rpow_nonneg hρ.le δ) (hΦ ρ hρ le_rfl)) hΨmono
    (fun s hs hsρ ↦ by simpa only [Real.rpow_zero, mul_one] using hΨstep s hs hsρ)
    hr hrρ
  simp only [Real.rpow_zero, div_one, mul_one] at hdecay
  have hsource : τ ^ δ * b * ρ ^ (δ + θ) ≤ ρ ^ δ := by
    calc _ = ρ ^ δ * (τ ^ δ * (b * ρ ^ θ)) := by rw [Real.rpow_add hρ]; ring
      _ ≤ ρ ^ δ * (1 * 1) := by gcongr; exact Real.rpow_le_one hτ.le hτ1.le hδ.le
      _ = _ := by ring
  have hΦρ := hΦ ρ hρ le_rfl
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hr δ)).mp
  calc
    _ ≤ τ⁻¹ ^ n * (ρ ^ δ * Φ ρ + 2 * (τ ^ δ * b * ρ ^ (δ + θ))) := by
      simpa only [mul_assoc] using hdecay
    _ ≤ τ⁻¹ ^ n * (2 * ρ ^ δ * (Φ ρ + 1)) := by
      gcongr τ⁻¹ ^ n * ?_
      nlinarith only [hsource, mul_nonneg (Real.rpow_nonneg hρ.le δ) hΦρ]
    _ = _ := by
      rw [Real.div_rpow hρ.le hr.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hr δ)]

end PDE.Elliptic.Regularity.Campanato
