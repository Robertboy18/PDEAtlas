/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.GradientEnergy
import PDE.Elliptic.Regularity.Interior.Schauder.Constant.Rescaling
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Averages

/-!
# Volume-order gradient energy decay on arbitrary balls

The derivative scaling factor cancels between the inner and outer mean
energies. The constant coefficient gradient estimate therefore controls all
small concentric balls uniformly in their centre and outer radius.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

open MeanScaling

variable {n : ℕ} [Fact (0 < n)]

/-- The mean-square weak gradient on a small ball is bounded by the outer
mean-square gradient for constant coefficient H¹ weak solutions. -/
theorem exists_ball_gradient_mean_energy_of_constant_coefficients
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
      ∀ (i : Fin n) (r : ℝ), 0 < r → r ≤ R / 4 →
        (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2) ≤
          C * ⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2 := by
  obtain ⟨C, hC, henergy⟩ :=
    exists_gradient_mean_energy_of_constant_coefficients hq2 hq hα hΛ
  refine ⟨C, hC, ?_⟩
  intro z R hR
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ R = s * 2 :=
    ⟨R / 2, by positivity, by ring⟩
  intro A a hrep hAΛ hA u hu i r hr hrR
  obtain ⟨B, v, hb, hB, hBΛ, hv, _hvbase, hvgrad⟩ :=
    exists_scaledBallWeakSolution_of_constant_representatives z hs 2 A a hrep hA hAΛ u hu
  have hr' : 0 < r / s := div_pos hr hs
  have hrR' : r / s ≤ 1 / 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hmean (t : ℝ) (ht : t ≤ 2) :
      (⨍ x in ball (0 : ℝ^n) t,
        ‖wkpCoordinateCLM (singleDerivIndex n i) v x‖ ^ 2) =
      s ^ 2 * ⨍ x in ball z (s * t),
        ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2 := by
    calc
      _ = ⨍ x in ball (0 : ℝ^n) t, s ^ 2 *
          ‖wkpCoordinateCLM (singleDerivIndex n i) u (ballHomeomorph z hs x)‖ ^ 2 := by
        apply average_congr
        filter_upwards [(hvgrad i).filter_mono
          (ae_mono (domainMeasure_le (ball_subset_ball ht)))] with x hx
        rw [hx, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ = _ := by
        rw [average_const_mul, average_comp_ballHomeomorph_mul z hs t
          (fun x ↦ ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2)]
  have hsmall :
      (⨍ x in ball (0 : ℝ^n) (r / s),
        ‖wkpCoordinateCLM (singleDerivIndex n i) v x‖ ^ 2) =
      s ^ 2 * ⨍ x in ball z r,
        ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2 := by
    simpa only [show s * (r / s) = r by field_simp] using
      hmean (r / s) (hrR'.trans (by norm_num))
  have h := henergy B a hb hBΛ hB v hv i (r / s) hr' hrR'
  rw [hsmall, hmean 2 le_rfl] at h
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hs)).mp
  simpa only [mul_assoc, mul_left_comm C] using h

end SobolevSpace.GraphSpace
