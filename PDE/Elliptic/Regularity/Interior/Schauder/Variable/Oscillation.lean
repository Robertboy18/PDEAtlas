/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.GradientOscillation
public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.Comparison
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.BallEnergy

/-!
# Gradient oscillation with Hölder coefficients

The constructed frozen comparison has uniform quadratic gradient decay.
Combining it with its energy error gives the one-step interior Schauder
estimate for an H¹ solution with Hölder divergence forcing.

The coefficient error retains the original gradient energy. No essential
bound or continuity of that gradient is assumed. The subsequent energy
iteration must control this term before it can yield a Hölder gradient.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Campanato
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- A uniform one-step gradient oscillation estimate for the variable
coefficient equation. The comparison and its regularity are constructed. -/
theorem exists_gradient_oscillation_of_holder_coefficients
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
      ∀ (i : Fin n) (r : ℝ), 0 < r → r ≤ R / 8 →
        (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
          ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2) ≤
        4 * C * (r / R) ^ 2 *
          (⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
            ⨍ y in ball z R, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2) +
        (2 * (R / r) ^ n + 4 * C * (r / R) ^ 2) *
          ((2 * n * (M * R ^ (γ : ℝ)) ^ 2 +
            2 * (n : ℝ) ^ 2 * (K * R ^ (γ : ℝ)) ^ 2 *
              ((volume.real (ball z R))⁻¹ *
                ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ^ 2)) / α ^ 2) := by
  classical
  obtain ⟨C, hC, hdecay⟩ :=
    exists_gradient_oscillation_of_constant_coefficients hq2 hq hα hΛ
  refine ⟨C, hC, ?_⟩
  intro z R hR a A K M γ hA hrep hAz hell u F f hf hF hu i r hr hrR
  obtain ⟨b, w, hb, hbEll, hbΛ, hhom, herr⟩ :=
    exists_frozen_comparison_with_mean_error Fact.out z hR a A hA hrep hα hΛ hAz hell
      u F f hf hF hu
  refine (setAverage_oscillation_sq_le_of_comparison_decay hr (by linarith) (Lp.memLp _)
    (Lp.memLp _) (mul_nonneg hC.le (sq_nonneg (r / R))) (herr i)
    (hdecay z R hR b (fun j k ↦ A j k z) hb hbΛ hbEll _ hhom i _ r hr hrR)).trans_eq ?_
  ring

end SobolevSpace.GraphSpace
