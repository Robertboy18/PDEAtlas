/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.Oscillation
public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.Restriction

/-!
# Local gradient oscillation comparison

Restriction of the coefficient form and of the divergence forcing makes the
quadratic frozen comparison estimate available at every interior scale. The
coefficient error retains the mean energy of the original H¹ gradient.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Uniform local gradient oscillation comparison for an H¹ equation
with Hölder coefficients and divergence forcing. -/
theorem exists_local_gradient_oscillation_of_holder_coefficients
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Set ℝ^n}, IsOpen Ω →
      ∀ (a : Fin n → Fin n → DerivLp n ∞ Ω)
        (A : Fin n → Fin n → ℝ^n → ℝ) (K M γ : ℝ≥0),
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
      ∀ (i : Fin n) (r : ℝ), 0 < r → r ≤ R / 8 →
        (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
          ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2) ≤
        4 * C * (r / R) ^ 2 *
          (⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
            ⨍ y in ball z R, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2) +
        (2 * (R / r) ^ n + 4 * C * (r / R) ^ 2) *
          ((2 * n * (M * R ^ (γ : ℝ)) ^ 2 +
            2 * (n : ℝ) ^ 2 * (K * R ^ (γ : ℝ)) ^ 2 *
              (∑ j, ⨍ x in ball z R,
                ‖wkpCoordinateCLM (singleDerivIndex n j) u x‖ ^ 2)) / α ^ 2) := by
  obtain ⟨C, hC, hosc⟩ :=
    exists_gradient_oscillation_of_holder_coefficients hq2 hq hα hΛ
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ a A K M γ hA hrep u F f hf hF hu z R hR hsub hAz hell i r hr hrR
  let U : H¹(ball z R) := restrictCLM isOpen_ball.measurableSet hsub u
  let b (j k : Fin n) := restrictDerivLp hsub (a j k)
  let G (j : Fin n) := restrictDerivLp hsub (F j)
  have hb (j k : Fin n) : (b j k : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] A j k :=
    (restrictDerivLp_apply_ae hsub (a j k)).trans
      ((hrep j k).filter_mono (ae_mono (domainMeasure_le hsub)))
  have hG (j : Fin n) : (G j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] f j :=
    (restrictDerivLp_apply_ae hsub (F j)).trans
      ((hF j).filter_mono (ae_mono (domainMeasure_le hsub)))
  have h := hosc z R hR b A K M γ (fun j k ↦ (hA j k).mono hsub) hb hAz hell
    U G f (fun j ↦ (hf j).mono hsub) hG
    (interiorVariableCoeffForm_eq_divergence_restrict hΩ isOpen_ball hsub a u F hu)
    i r hr hrR
  have hav (s : ℝ) (hs : s ≤ R) :
      (⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
        ⨍ y in ball z s, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2) =
        ⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
          ⨍ y in ball z s, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2 := by
    have hm := setAverage_comp_gradient_restrict isOpen_ball.measurableSet hsub u i
      (ball_subset_ball hs) id
    change (⨍ x in ball z s, wkpCoordinateCLM (singleDerivIndex n i) U x) = _ at hm
    rw [hm]
    exact setAverage_comp_gradient_restrict isOpen_ball.measurableSet hsub u i
      (ball_subset_ball hs) (fun t ↦ ‖t -
        ⨍ y in ball z s, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2)
  rw [show (volume.real (ball z R))⁻¹ *
      ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) U‖ ^ 2 =
      ∑ j, ⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n j) u x‖ ^ 2 from
    normalized_gradient_energy_restrict u hsub, hav r (by linarith), hav R le_rfl] at h
  exact h

end SobolevSpace.GraphSpace
