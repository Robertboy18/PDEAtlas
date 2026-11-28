/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.BallEnergy
public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.Comparison
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.BallEnergy

/-!
# Mean gradient energy under a Hölder coefficient perturbation

The constant coefficient comparison has volume-order gradient energy decay.
Its constructed error gives an energy recurrence for the original H¹ solution.
The perturbation tends to zero with the radius when the Hölder exponent is
positive; no bound on the original gradient is an input.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Campanato
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Mean gradient energy is bounded by the constant coefficient contribution
and a vanishing coefficient perturbation times the original energy. -/
theorem exists_gradient_mean_energy_of_holder_coefficients
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : ℝ^n) (R : ℝ), 0 < R →
      ∀ (a : Fin n → Fin n → DerivLp n ∞ (ball z R))
        (A : Fin n → Fin n → ℝ^n → ℝ) (K M γ : ℝ≥0),
        (∀ i j, HolderOnWith K γ (A i j) (ball z R)) →
        (∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] A i j) →
        (∀ i j, ‖A i j z‖ ≤ Λ) →
        (∀ ξ : Fin n → ℝ,
          α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j z * ξ j * ξ i) →
      ∀ (u : H¹(ball z R)) (F : Fin n → DerivLp n 2 (ball z R))
        (f : Fin n → ℝ^n → ℝ),
        (∀ i, HolderOnWith M γ (f i) (ball z R)) →
        (∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] f i) →
        (∀ v : H¹₀(ball z R),
          interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
            ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ) →
      ∀ (r : ℝ), 0 < r → r ≤ R / 4 →
        (∑ i, ⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2) ≤
        4 * C * (∑ i, ⨍ x in ball z R,
          ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2) +
        n * (2 * (R / r) ^ n + 4 * C) *
          ((2 * n * (M * R ^ (γ : ℝ)) ^ 2 +
            2 * (n : ℝ) ^ 2 * (K * R ^ (γ : ℝ)) ^ 2 *
              ((volume.real (ball z R))⁻¹ *
                ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ^ 2)) / α ^ 2) := by
  classical
  obtain ⟨C, hC, hdecay⟩ :=
    exists_ball_gradient_mean_energy_of_constant_coefficients hq2 hq hα hΛ
  refine ⟨C, hC, ?_⟩
  intro z R hR a A K M γ hA hrep hAz hell u F f hf hF hu r hr hrR
  obtain ⟨b, w, hb, hbEll, hbΛ, hhom, herr⟩ :=
    exists_frozen_comparison_with_mean_error Fact.out z hR a A hA hrep hα hΛ hAz hell
      u F f hf hF hu
  let H : H¹(ball z R) := u - (w : H¹(ball z R))
  let E : ℝ := (2 * n * (M * R ^ (γ : ℝ)) ^ 2 +
    2 * (n : ℝ) ^ 2 * (K * R ^ (γ : ℝ)) ^ 2 *
      ((volume.real (ball z R))⁻¹ *
        ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ^ 2)) / α ^ 2
  have hcoordinate (i : Fin n) :
      (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2) ≤
      4 * C * (⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2) +
        (2 * (R / r) ^ n + 4 * C) * E := by
    simpa only [sub_zero] using
      setAverage_norm_sub_sq_le_of_comparison_decay (c := 0) (c' := 0) hr
        (by linarith : r ≤ R) (Lp.memLp (wkpCoordinateCLM (singleDerivIndex n i) u))
        (Lp.memLp (wkpCoordinateCLM (singleDerivIndex n i) H)) hC.le (herr i)
        (by simpa only [sub_zero] using
          hdecay z R hR b (fun j k ↦ A j k z) hb hbΛ hbEll H hhom i r hr hrR)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hcoordinate i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_fin, nsmul_eq_mul] at hsum
  refine hsum.trans_eq ?_
  dsimp only [E]
  ring

end SobolevSpace.GraphSpace
