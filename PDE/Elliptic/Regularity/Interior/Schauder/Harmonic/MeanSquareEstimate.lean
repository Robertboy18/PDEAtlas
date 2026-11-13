/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Harmonic.LocalDecay
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.BallEnergy
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Iteration

/-!
# Interior mean-square Schauder estimate for weak Poisson solutions

The harmonic comparison estimate is iterated on interior balls. For Hölder
divergence forcing of exponent `γ < 1`, the gradient oscillation decays as
`r^(2γ)`. The initial state is only `H¹`, and the constant depends solely on
dimension and exponent. The weak equation supplies every step of the iteration.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev InnerProductSpace NNReal

namespace SobolevSpace.GraphSpace

open PDE.Elliptic.Regularity.Campanato

variable {n : ℕ} [Fact (0 < n)]

/-- Quantitative mean-square gradient decay for a weak `H¹` solution
of `Δu = div F` with Hölder forcing. The dimension and exponent determine one
constant valid for every open domain, solution, interior ball, and coordinate. -/
theorem exists_meanSquare_gradient_estimate {γ : ℝ≥0} (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Set ℝ^n}, IsOpen Ω → ∀ (U : H¹(Ω))
      (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ) (M : ℝ≥0),
      (∀ j, HolderOnWith M γ (f j) Ω) →
      (∀ j, (F j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f j) →
      (∀ t : H¹₀(Ω),
        (∑ j, ⟪wkpCoordinateCLM (singleDerivIndex n j) U, derivCoordCLM j t⟫_ℝ) =
          ∑ j, ⟪F j, derivCoordCLM j t⟫_ℝ) →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R → ball z R ⊆ Ω →
      ∀ r, 0 < r → r ≤ R → ∀ i : Fin n,
      (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
        ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2) ≤
        C * (r / R) ^ (2 * (γ : ℝ)) *
          ((⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
            ⨍ y in ball z R, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2) +
              (M * R ^ (γ : ℝ)) ^ 2) := by
  let L : ℝ := (2 : ℝ) ^ (2 * n + 3) * n
  have hL : 0 < L := mul_pos (pow_pos (by norm_num) _) (Nat.cast_pos.mpr Fact.out)
  have hγr : (γ : ℝ) < 1 := by exact_mod_cast hγ
  obtain ⟨τ, hτ, hτhalf, hscale⟩ :=
    exists_quadratic_decay_scale (A := 4 * L ^ 2) (β := 2 * (γ : ℝ))
      (by linarith) (by positivity)
  let a := 4 * (L * τ) ^ 2
  let B := (2 * τ⁻¹ ^ n + a) * n
  let q := τ ^ (2 * (γ : ℝ))
  let D := τ⁻¹ ^ n / q
  have hq : 0 < q := Real.rpow_pos_of_pos hτ _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have haq : a ≤ q / 2 := by
    dsimp only [a, q]
    nlinarith only [hscale]
  refine ⟨D * (1 + 2 * B / q), by positivity, ?_⟩
  intro Ω hΩ U F f M hf hF hweak z R hR hsub r hr hrR i
  let Φ (s : ℝ) := ⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
    ⨍ y in ball z s, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2
  have hΦ : 0 ≤ Φ R := average_nonneg (fun _ ↦ sq_nonneg _)
  have hmem (s : ℝ) (hs : s ≤ R) :
      MemLp (wkpCoordinateCLM (singleDerivIndex n i) U) 2 (volume.restrict (ball z s)) :=
    (Lp.memLp _).mono_measure (domainMeasure_le ((ball_subset_ball hs).trans hsub))
  have hmono (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ R) :
      Φ s ≤ (t / s) ^ n * Φ t :=
    setAverage_oscillation_sq_le_of_radius_le hs hst (hmem t ht)
  have hp (s : ℝ) (hs : 0 < s) :
      (M * s ^ (γ : ℝ)) ^ 2 = (M : ℝ) ^ 2 * s ^ (2 * (γ : ℝ)) := by
    rw [mul_pow, mul_comm (2 : ℝ), Real.rpow_mul hs.le, Real.rpow_two]
  have hstep (s : ℝ) (hs : 0 < s) (hsR : s ≤ R) :
      Φ (τ * s) ≤ a * Φ s + (B * (M : ℝ) ^ 2) * s ^ (2 * (γ : ℝ)) := by
    have h := meanSquare_gradient_oscillation_le_on_interior_ball hΩ U F f hf hF hweak
      ((ball_subset_ball hsR).trans hsub) (mul_pos hτ hs)
      (by nlinarith : τ * s ≤ s / 2) i
    have hd : τ * s / s = τ := mul_div_cancel_right₀ τ hs.ne'
    have hi : s / (τ * s) = τ⁻¹ := by field_simp
    rw [hd, hi, hp s hs] at h
    dsimp only [Φ, a, B, L] at *
    convert h using 1
    ring
  have hdec := decay_at_all_radii (by positivity : 0 ≤ 2 * (γ : ℝ)) hτ
    (by linarith : τ < 1) ha (mul_nonneg hB (sq_nonneg (M : ℝ))) haq n Φ hΦ
      hmono hstep hr hrR
  have houter :
      Φ R + 2 * (B * (M : ℝ) ^ 2) * R ^ (2 * (γ : ℝ)) / q ≤
        (1 + 2 * B / q) * (Φ R + (M * R ^ (γ : ℝ)) ^ 2) := by
    rw [hp R hR]
    have hBQ : 0 ≤ 2 * B / q := by positivity
    simp only [div_eq_mul_inv] at hBQ ⊢
    nlinarith [mul_nonneg hBQ hΦ, mul_nonneg (sq_nonneg (M : ℝ))
      (Real.rpow_nonneg hR.le (2 * (γ : ℝ)))]
  refine hdec.trans ?_
  change D * (r / R) ^ (2 * (γ : ℝ)) *
      (Φ R + 2 * (B * (M : ℝ) ^ 2) * R ^ (2 * (γ : ℝ)) / q) ≤ _
  exact (mul_le_mul_of_nonneg_left houter (by positivity)).trans_eq (by ring)

end SobolevSpace.GraphSpace
