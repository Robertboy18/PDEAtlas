/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.FrozenCoefficients
public import Mathlib.MeasureTheory.Integral.Average
import PDE.Analysis.MeasureTheory.Lp.EssentialSupremum

/-!
# Frozen comparisons with normalized gradient error

The constructed frozen equation retains the ellipticity and entrywise bounds
at the freezing point. Its energy estimate bounds the mean-square error of
each weak gradient coordinate. This supplies the same comparison to
the energy decay and oscillation arguments.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- Construct a uniformly elliptic constant coefficient comparison and bound
its normalized gradient error from the Hölder coefficients and forcing. -/
theorem exists_frozen_comparison_with_mean_error
    (hn : 0 < n) (z : ℝ^n) {R : ℝ} (hR : 0 < R)
    (a : Fin n → Fin n → DerivLp n ∞ (ball z R))
    (A : Fin n → Fin n → ℝ^n → ℝ) {K M γ : ℝ≥0}
    (hA : ∀ i j, HolderOnWith K γ (A i j) (ball z R))
    (hrep : ∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] A i j)
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) (hAz : ∀ i j, ‖A i j z‖ ≤ Λ)
    (hell : ∀ ξ : Fin n → ℝ,
      α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j z * ξ j * ξ i)
    (u : H¹(ball z R)) (F : Fin n → DerivLp n 2 (ball z R))
    (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ i, HolderOnWith M γ (f i) (ball z R))
    (hF : ∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] f i)
    (hu : ∀ v : H¹₀(ball z R),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
        ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ) :
    ∃ (b : Fin n → Fin n → DerivLp n ∞ (ball z R)) (w : H¹₀(ball z R)),
      (∀ i j, (b i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] fun _ ↦ A i j z) ∧
      AEUniformlyElliptic b α ∧ (∀ i j, ‖b i j‖ ≤ Λ) ∧
      IsInteriorWeakDivergenceSolution b 0 (u - (w : H¹(ball z R))) ∧
      ∀ i, (⨍ x in ball z R,
        ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
          wkpCoordinateCLM (singleDerivIndex n i) (u - (w : H¹(ball z R))) x‖ ^ 2) ≤
        (2 * n * (M * R ^ (γ : ℝ)) ^ 2 +
          2 * (n : ℝ) ^ 2 * (K * R ^ (γ : ℝ)) ^ 2 *
            ((volume.real (ball z R))⁻¹ *
              ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ^ 2)) / α ^ 2 := by
  classical
  let : Fact (0 < n) := ⟨hn⟩
  obtain ⟨b, w, hb, hhom, henergy⟩ := exists_frozen_comparison_of_holder_flux
    hn z hR a A hA hrep hα hell u F f hf hF hu
  have hbEll : AEUniformlyElliptic b α := by
    refine ⟨hα, ?_⟩
    filter_upwards [ae_all_iff.mpr fun j ↦ ae_all_iff.mpr (hb j)] with x hx
    simpa only [hx] using hell
  have hbΛ (j k : Fin n) : ‖b j k‖ ≤ Λ := by
    apply Lp.norm_top_le_of_ae_bound hΛ
    filter_upwards [hb j k] with x hx
    rw [hx]
    exact hAz j k
  refine ⟨b, w, hb, hbEll, hbΛ, hhom, ?_⟩
  intro i
  let H : H¹(ball z R) := u - (w : H¹(ball z R))
  let E : ℝ := (2 * n * (M * R ^ (γ : ℝ)) ^ 2 +
    2 * (n : ℝ) ^ 2 * (K * R ^ (γ : ℝ)) ^ 2 *
      ((volume.real (ball z R))⁻¹ *
        ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ^ 2)) / α ^ 2
  have hD (j : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n j) (w : H¹(ball z R)) =
        derivCoordCLM j w := by
    rw [wkpCoordinateCLM_apply, derivCoordCLM_apply]
  have hsub : wkpCoordinateCLM (singleDerivIndex n i) u -
      wkpCoordinateCLM (singleDerivIndex n i) H = derivCoordCLM i w := by
    simp only [H, map_sub, hD]
    abel
  have hvol : 0 < volume.real (ball z R) :=
    ENNReal.toReal_pos (measure_ball_pos volume z hR).ne' measure_ball_lt_top.ne
  have herr : (volume.real (ball z R))⁻¹ * ∑ j, ‖derivCoordCLM j w‖ ^ 2 ≤ E := by
    apply (le_div_iff₀ (sq_pos_of_pos hα)).mpr
    have ht := mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr hvol.le)
    simp only [measureReal_def] at ht ⊢
    convert ht using 1 <;>
      field_simp [show (volume (ball z R)).toReal ≠ 0 from hvol.ne']
  calc
    _ = (volume.real (ball z R))⁻¹ *
        ‖wkpCoordinateCLM (singleDerivIndex n i) u -
          wkpCoordinateCLM (singleDerivIndex n i) H‖ ^ 2 := by
      rw [setAverage_eq, smul_eq_mul, Lp.norm_sq_eq_integral_norm_sq]
      congr 1
      exact integral_congr_ae ((Lp.coeFn_sub _ _).fun_comp (fun t : ℝ ↦ ‖t‖ ^ 2)).symm
    _ = (volume.real (ball z R))⁻¹ * ‖derivCoordCLM i w‖ ^ 2 := by rw [hsub]
    _ ≤ (volume.real (ball z R))⁻¹ * ∑ j, ‖derivCoordCLM j w‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.single_le_sum
        (fun j _ ↦ sq_nonneg ‖derivCoordCLM j w‖) (Finset.mem_univ i))
        (inv_nonneg.mpr hvol.le)
    _ ≤ E := herr

end SobolevSpace.GraphSpace
