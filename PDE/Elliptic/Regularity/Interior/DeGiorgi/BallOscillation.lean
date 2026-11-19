/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Oscillation
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.WeakEquation
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Normalization

/-!
# Uniform oscillation contraction on arbitrary balls

Spatial rescaling preserves the homogeneous weak equation and its
ellipticity bounds. Affine normalization of the dependent variable then
removes the special essential range used in the unit-ball argument.
The contraction factor depends on the dimension and ellipticity bounds,
and is independent of the ball, solution, and current essential range.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- A uniform contraction of the essential range when the spatial radius
is divided by four. Both the new centre and radius are controlled. The
state is an H¹ weak solution with measurable elliptic coefficients. -/
theorem exists_oscillation_contraction_on_rescaled_balls
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ (z : ℝ^n) (s : ℝ), 0 < s →
      ∀ (A : Fin n → Fin n → DerivLp n ∞ (ball z (s * 2))),
        (∀ i j, ‖A i j‖ ≤ Λ) → AEUniformlyElliptic A α →
      ∀ (u : H¹(ball z (s * 2))), IsInteriorWeakDivergenceSolution A 0 u →
      ∀ (c M : ℝ), 0 < M →
        (∀ᵐ x ∂volume.restrict (ball z (s * 2)),
          |wkpBaseCoordinateCLM u x - c| ≤ M) →
        ∃ d : ℝ, |d - c| ≤ (1 - ρ) * M ∧
          ∀ᵐ x ∂volume.restrict (ball z (s * (1 / 2))),
            |wkpBaseCoordinateCLM u x - d| ≤ ρ * M := by
  obtain ⟨ρ, hρ, hρ1, hdrop⟩ :=
    exists_oscillation_contraction_on_half_ball hq2 hq hα hΛ
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro z s hs A hAΛ hA u hu c M hM hbound
  let μ := domainMeasure n (ball z (s * 2))
  let : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (ball z (s * 2))) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  let v := M⁻¹ • (u - wkpConstant c)
  have hv : IsInteriorWeakDivergenceSolution A 0 v := hu.smul_sub_constant M⁻¹ c
  have hvrep := wkpBaseCoordinateCLM_smul_sub_constant_ae u M⁻¹ c
  have hvbound : ∀ᵐ x ∂μ, |wkpBaseCoordinateCLM v x| ≤ 1 := by
    filter_upwards [hvrep, hbound] with x hx hb
    rw [hx, abs_mul, abs_of_pos (inv_pos.mpr hM)]
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)).trans_eq
      (inv_mul_cancel₀ hM.ne')
  obtain ⟨B, w, hB, hBΛ, hw, hwrep⟩ :=
    MeanScaling.exists_scaledBallWeakSolution z hs 2 A hA hAΛ v hv
  have hwbound : ∀ᵐ y ∂volume.restrict (ball (0 : ℝ^n) 2),
      |wkpBaseCoordinateCLM w y| ≤ 1 := by
    have hp := (MeanScaling.ae_comp_ballHomeomorph_iff z hs 2
      (fun x ↦ |wkpBaseCoordinateCLM v x| ≤ 1)).mpr hvbound
    filter_upwards [hwrep, hp] with y hy hb
    rwa [hy]
  obtain ⟨k, hk, hsmall⟩ := hdrop B hBΛ hB w hw hwbound
  have hmeasure : domainMeasure n (ball (0 : ℝ^n) (1 / 2)) ≤
      domainMeasure n (ball (0 : ℝ^n) 2) :=
    domainMeasure_le (ball_subset_ball (by norm_num))
  have hvsmall : ∀ᵐ x ∂volume.restrict (ball z (s * (1 / 2))),
      |wkpBaseCoordinateCLM v x - k| ≤ ρ := by
    apply (MeanScaling.ae_comp_ballHomeomorph_iff z hs (1 / 2) _).mp
    filter_upwards [hsmall, hwrep.filter_mono (ae_mono hmeasure)] with y hy heq
    rwa [heq] at hy
  refine ⟨c + M * k, ?_, ?_⟩
  · rw [show c + M * k - c = M * k by abel, abs_mul, abs_of_pos hM]
    simpa only [mul_comm M (1 - ρ)] using mul_le_mul_of_nonneg_left hk hM.le
  · have hsmallMeasure : volume.restrict (ball z (s * (1 / 2))) ≤ μ :=
      domainMeasure_le (ball_subset_ball (mul_le_mul_of_nonneg_left (by norm_num) hs.le))
    filter_upwards [hvsmall, hvrep.filter_mono (ae_mono hsmallMeasure)] with x hx heq
    have hid : wkpBaseCoordinateCLM u x - (c + M * k) =
        M * (wkpBaseCoordinateCLM v x - k) := by
      rw [heq]
      field_simp [hM.ne']
      ring
    rw [hid, abs_mul, abs_of_pos hM]
    simpa only [mul_comm M ρ] using mul_le_mul_of_nonneg_left hx hM.le

end SobolevSpace.GraphSpace
