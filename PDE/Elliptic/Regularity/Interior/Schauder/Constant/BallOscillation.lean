/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.Oscillation
import PDE.Elliptic.Regularity.Interior.Schauder.Constant.Rescaling
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Averages

/-!
# Uniform constant coefficient oscillation on interior balls

Affine transport gives quadratic oscillation decay on arbitrary concentric
balls. The constant is independent of their centre and radii and of the
particular matrix in the prescribed ellipticity class.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

open MeanScaling

variable {n : ℕ} [Fact (0 < n)]

/-- Quadratic mean oscillation decay for constant coefficient H¹ weak
solutions, normalized by the outer mean-square energy. -/
theorem exists_ball_oscillation_of_constant_coefficients
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : ℝ^n) (R : ℝ), 0 < R →
      ∀ (A : Fin n → Fin n → DerivLp n ∞ (ball z R))
        (a : Fin n → Fin n → ℝ),
        (∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)]
          fun _ ↦ a i j) →
        (∀ i j, ‖A i j‖ ≤ Λ) → AEUniformlyElliptic A α →
      ∀ (u : H¹(ball z R)), IsInteriorWeakDivergenceSolution A 0 u →
      ∀ (c r : ℝ), 0 < r → r ≤ R / 4 →
        (⨍ x in ball z r, ‖wkpBaseCoordinateCLM u x -
          ⨍ y in ball z r, wkpBaseCoordinateCLM u y‖ ^ 2) ≤
          C * (r / R) ^ 2 *
            ⨍ x in ball z R, ‖wkpBaseCoordinateCLM u x - c‖ ^ 2 := by
  obtain ⟨D, hD, hdecay⟩ :=
    exists_quadratic_oscillation_of_constant_coefficients hq2 hq hα hΛ
  let V := volume.real (ball (0 : ℝ^n) 2)
  have hV : 0 < V :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : ℝ^n) (by norm_num)).ne'
      measure_ball_lt_top.ne
  refine ⟨4 * D * V, by positivity, ?_⟩
  intro z R hR
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ R = s * 2 :=
    ⟨R / 2, by positivity, by ring⟩
  intro A a hrep hAΛ hA u hu c r hr hrR
  obtain ⟨B, v, hb, hB, hBΛ, hv, hvbase, _hvgrad⟩ :=
    exists_scaledBallWeakSolution_of_constant_representatives z hs 2 A a hrep hA hAΛ u hu
  have hr' : 0 < r / s := div_pos hr hs
  have hrR' : r / s ≤ 1 / 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hsmall : ball (0 : ℝ^n) (r / s) ⊆ ball 0 2 :=
    ball_subset_ball (hrR'.trans (by norm_num))
  have hmean : (⨍ y in ball (0 : ℝ^n) (r / s), wkpBaseCoordinateCLM v y) =
      ⨍ y in ball z r, wkpBaseCoordinateCLM u y := by
    rw [average_congr (hvbase.filter_mono (ae_mono (domainMeasure_le hsmall))),
      average_comp_ballHomeomorph_mul]
    congr 2
    field_simp
  have hosc :
      (⨍ x in ball (0 : ℝ^n) (r / s), ‖wkpBaseCoordinateCLM v x -
        ⨍ y in ball (0 : ℝ^n) (r / s), wkpBaseCoordinateCLM v y‖ ^ 2) =
      ⨍ x in ball z r, ‖wkpBaseCoordinateCLM u x -
        ⨍ y in ball z r, wkpBaseCoordinateCLM u y‖ ^ 2 := by
    rw [hmean]
    calc
      _ = ⨍ x in ball (0 : ℝ^n) (r / s),
          ‖wkpBaseCoordinateCLM u (ballHomeomorph z hs x) -
            ⨍ y in ball z r, wkpBaseCoordinateCLM u y‖ ^ 2 :=
        average_congr ((hvbase.filter_mono (ae_mono (domainMeasure_le hsmall))).fun_comp
          fun t ↦ ‖t - ⨍ y in ball z r, wkpBaseCoordinateCLM u y‖ ^ 2)
      _ = _ := by
        rw [average_comp_ballHomeomorph_mul z hs (r / s)
          (fun x ↦ ‖wkpBaseCoordinateCLM u x -
            ⨍ y in ball z r, wkpBaseCoordinateCLM u y‖ ^ 2)]
        congr 2
        field_simp
  have henergy :
      (∫ x in ball (0 : ℝ^n) 2, ‖wkpBaseCoordinateCLM v x - c‖ ^ 2) =
        V * ⨍ x in ball z (s * 2), ‖wkpBaseCoordinateCLM u x - c‖ ^ 2 := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : ℝ^n) 2)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    rw [← measure_smul_average]
    simp only [measureReal_restrict_apply_univ, smul_eq_mul]
    congr 1
    calc
      _ = ⨍ x in ball (0 : ℝ^n) 2,
          ‖wkpBaseCoordinateCLM u (ballHomeomorph z hs x) - c‖ ^ 2 :=
        average_congr (hvbase.fun_comp fun t ↦ ‖t - c‖ ^ 2)
      _ = _ := average_comp_ballHomeomorph_mul z hs 2
        (fun x ↦ ‖wkpBaseCoordinateCLM u x - c‖ ^ 2)
  have h := hdecay B a hb hBΛ hB v hv c (r / s) hr' hrR'
  rw [hosc, henergy] at h
  convert h using 1
  ring

end SobolevSpace.GraphSpace
