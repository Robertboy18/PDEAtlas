/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.LocalOscillation
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Perturbation
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.BallEnergy
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Bounds

/-!
# Full oscillation exponent after the first gradient gain

A local bound for the weak gradient turns the coefficient comparison error
into a fixed multiple of `r^(2γ)`. Quadratic scale iteration then gives the
full coefficient exponent. The preceding H¹-to-Hölder theorem supplies this
bound when applying the estimate to an H¹ solution.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Campanato
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Once a local gradient bound is known, the weak equation gives
mean-square decay of order `2γ` for every `γ < 1`. The constant is uniform
over centres and radii. -/
theorem exists_meanSquare_gradient_estimate_of_bounded_gradient
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ P : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) (hP : 0 ≤ P) {K M γ : ℝ≥0} (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Set ℝ^n}, IsOpen Ω →
      ∀ (a : Fin n → Fin n → DerivLp n ∞ Ω)
        (A : Fin n → Fin n → ℝ^n → ℝ),
        (∀ i j, HolderOnWith K γ (A i j) Ω) →
        (∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A i j) →
      ∀ (u : H¹(Ω)) (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ),
        (∀ i, HolderOnWith M γ (f i) Ω) →
        (∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f i) →
        (∀ v : H¹₀(Ω),
          interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
            ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ) →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R → ball z R ⊆ Ω →
        (∀ i j, ‖A i j z‖ ≤ Λ) →
        (∀ ξ : Fin n → ℝ,
          α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j z * ξ j * ξ i) →
        (∀ i, ∀ᵐ x ∂volume.restrict (ball z R),
          ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ≤ P) →
      ∀ (r : ℝ), 0 < r → r ≤ R → ∀ i : Fin n,
        (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
          ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2) ≤
        C * (r / R) ^ (2 * (γ : ℝ)) *
          ((⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
            ⨍ y in ball z R, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2) +
            R ^ (2 * (γ : ℝ))) := by
  classical
  obtain ⟨L, hL, hosc⟩ :=
    exists_local_gradient_oscillation_of_holder_coefficients hq2 hq hα hΛ
  have hγlt : (γ : ℝ) < 1 := by exact_mod_cast hγ1
  obtain ⟨τ, hτ, hτ8, hscale⟩ := exists_quadratic_decay_scale_le
    (by linarith : 2 * (γ : ℝ) < 2) (by positivity : 0 < 4 * L)
    (by norm_num : (0 : ℝ) < 1 / 8)
  let a := 4 * L * τ ^ 2
  let H := (2 * n * (M : ℝ) ^ 2 + 2 * (n : ℝ) ^ 2 * (K : ℝ) ^ 2) / α ^ 2
  let B := (2 * τ⁻¹ ^ n + a) * H * (1 + n * P ^ 2)
  let Q := τ ^ (2 * (γ : ℝ))
  let D := τ⁻¹ ^ n / Q
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : 0 < Q := Real.rpow_pos_of_pos hτ _
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * (1 + 2 * B / Q), by positivity, ?_⟩
  intro Ω hΩ b A hA hrep u F f hf hF hu z R hR hsub hAz hell hbound r hr hrR i
  let Φ (s : ℝ) := ⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
    ⨍ y in ball z s, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2
  let E (s : ℝ) := ∑ j, ⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n j) u x‖ ^ 2
  have hE (s : ℝ) : 0 ≤ E s :=
    Finset.sum_nonneg (fun _ _ ↦ average_nonneg (fun _ ↦ sq_nonneg _))
  have hΦ : 0 ≤ Φ R := average_nonneg (fun _ ↦ sq_nonneg _)
  have hmem (s : ℝ) (hs : s ≤ R) (j : Fin n) :
      MemLp (wkpCoordinateCLM (singleDerivIndex n j) u) 2
        (volume.restrict (ball z s)) :=
    (Lp.memLp _).mono_measure (domainMeasure_le ((ball_subset_ball hs).trans hsub))
  have hmean (s : ℝ) (hs : 0 < s) (hsR : s ≤ R) : E s ≤ n * P ^ 2 := by
    have hc (j : Fin n) :
        (⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n j) u x‖ ^ 2) ≤ P ^ 2 := by
      apply setAverage_le_of_ae_bound (measure_ball_pos volume z hs).ne'
        measure_ball_lt_top.ne (hmem s hsR j).norm.integrable_sq
      filter_upwards [(hbound j).filter_mono
        (ae_mono (Measure.restrict_mono (ball_subset_ball hsR) le_rfl))] with x hx
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx)
        (add_nonneg hP (norm_nonneg (wkpCoordinateCLM (singleDerivIndex n j) u x)))]
    simpa only [E, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hc j)
  have hstep (s : ℝ) (hs : 0 < s) (hsR : s ≤ R) :
      Φ (τ * s) ≤ a * Φ s + B * s ^ (2 * (γ : ℝ)) := by
    have he := hosc hΩ b A K M γ hA hrep u F f hf hF hu z s hs
      ((ball_subset_ball hsR).trans hsub) hAz hell i (τ * s) (mul_pos hτ hs)
      (by nlinarith : τ * s ≤ s / 8)
    have hr1 : τ * s / s = τ := mul_div_cancel_right₀ τ hs.ne'
    have hr2 : s / (τ * s) = τ⁻¹ := by field_simp
    rw [hr1, hr2] at he
    have herr := holder_comparison_error_le (α := α) (K := (K : ℝ)) (M := (M : ℝ))
      (γ := (γ : ℝ)) n hα hs (hE s)
    have herr' := herr.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hmean s hs hsR))
      (mul_nonneg hH (Real.rpow_nonneg hs.le _)))
    have ht := mul_le_mul_of_nonneg_left herr'
      (show 0 ≤ 2 * τ⁻¹ ^ n + a by positivity)
    dsimp only [a, B, H, Φ, E] at he ht ⊢
    nlinarith only [he, ht]
  have hd := decay_at_all_radii (by positivity : 0 ≤ 2 * (γ : ℝ)) hτ
    (by linarith : τ < 1) ha hB hscale n Φ hΦ
    (fun r s hr hrs hsR ↦
      setAverage_oscillation_sq_le_of_radius_le hr hrs (hmem s hsR i))
    hstep hr hrR
  have houter : Φ R + 2 * B * R ^ (2 * (γ : ℝ)) / Q ≤
      (1 + 2 * B / Q) * (Φ R + R ^ (2 * (γ : ℝ))) := by
    have hp := mul_nonneg (by positivity : 0 ≤ 2 * B / Q) hΦ
    simp only [div_eq_mul_inv] at hp ⊢
    nlinarith only [hp, Real.rpow_nonneg hR.le (2 * (γ : ℝ))]
  exact hd.trans ((mul_le_mul_of_nonneg_left houter (by positivity)).trans_eq (by ring))

end SobolevSpace.GraphSpace
