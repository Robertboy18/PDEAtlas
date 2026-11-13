/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Harmonic.PoissonDecay
public import Mathlib.Topology.MetricSpace.Holder
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.Constant

/-!
# Poisson gradient decay with Hölder divergence forcing

Subtracting the value of the forcing at the ball centre does not change the
weak equation: a constant flux annihilates derivatives of zero-boundary tests.
Hölder continuity then bounds the correction energy by `n M² R^(2γ)`.
Combining this with harmonic replacement gives the scale-decaying error term
needed for the interior Schauder iteration.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev InnerProductSpace NNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The one-step gradient oscillation estimate with an error of order `R^(2γ)`.
The state starts in `H¹`; Hölder regularity is required only of the forcing. -/
theorem meanSquare_gradient_oscillation_le_of_holder_divergence
    {z : ℝ^n} {R r : ℝ} (U : H¹(ball z R))
    (F : Fin n → DerivLp n 2 (ball z R))
    (f : Fin n → ℝ^n → ℝ) {M γ : ℝ≥0}
    (hf : ∀ j, HolderOnWith M γ (f j) (ball z R))
    (hF : ∀ j, (F j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] f j)
    (hweak : ∀ t : H¹₀(ball z R),
      (∑ j, ⟪wkpCoordinateCLM (singleDerivIndex n j) U, derivCoordCLM j t⟫_ℝ) =
        ∑ j, ⟪F j, derivCoordCLM j t⟫_ℝ)
    (hr : 0 < r) (hrR : r ≤ R / 2) (i : Fin n) :
    (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
      ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2) ≤
      4 * (((2 : ℝ) ^ (2 * n + 3) * n) * (r / R)) ^ 2 *
        (⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
          ⨍ y in ball z R, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2) +
      (2 * (R / r) ^ n + 4 * (((2 : ℝ) ^ (2 * n + 3) * n) * (r / R)) ^ 2) *
        ((n : ℝ) * (M * R ^ (γ : ℝ)) ^ 2) := by
  have hR : 0 < R := by linarith
  have := isFiniteMeasure_domainMeasure_of_isBounded
    (isBounded_ball (x := z) (r := R))
  let C (j : Fin n) : DerivLp n 2 (ball z R) :=
    (memLp_const (μ := domainMeasure n (ball z R)) (f j z)).toLp _
  have hC (j : Fin n) :
      (C j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] fun _ ↦ f j z :=
    MemLp.coeFn_toLp _
  have hcenter (t : H¹₀(ball z R)) :
      (∑ j, ⟪wkpCoordinateCLM (singleDerivIndex n j) U, derivCoordCLM j t⟫_ℝ) =
        ∑ j, ⟪F j - C j, derivCoordCLM j t⟫_ℝ := by
    rw [hweak]
    apply Finset.sum_congr rfl
    intro j _
    rw [inner_sub_left, inner_constant_derivCoordCLM_eq_zero (f j z) (C j) (hC j)]
    exact (sub_zero _).symm
  have hbound (j : Fin n) :
      ‖F j - C j‖ ^ 2 ≤ volume.real (ball z R) * (M * R ^ (γ : ℝ)) ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    calc
      _ ≤ ∫ _x, (M * R ^ (γ : ℝ)) ^ 2 ∂domainMeasure n (ball z R) := by
        apply integral_mono_ae ((Lp.memLp (F j - C j)).norm.integrable_sq)
          (integrable_const _)
        filter_upwards [Lp.coeFn_sub (F j) (C j), hF j, hC j,
          ae_restrict_mem isOpen_ball.measurableSet] with x hsub hfx hcx hx
        rw [hsub, Pi.sub_apply, hfx, hcx]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        simpa only [dist_eq_norm] using
          (hf j).dist_le_of_le hx (mem_ball_self hR) (mem_ball.mp hx).le
      _ = _ := by simp [domainMeasure, measureReal_def, smul_eq_mul]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hbound j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hv : 0 < volume.real (ball z R) :=
    ENNReal.toReal_pos (measure_ball_pos volume z hR).ne' measure_ball_lt_top.ne
  have hmean : (volume.real (ball z R))⁻¹ * ∑ j, ‖F j - C j‖ ^ 2 ≤
      (n : ℝ) * (M * R ^ (γ : ℝ)) ^ 2 := by
    apply (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hv.le)).trans_eq
    field_simp
  refine (meanSquare_gradient_oscillation_le_of_dirichlet_eq_divergence
    U (fun j ↦ F j - C j) hcenter hr hrR i).trans ?_
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left hmean
  positivity

end SobolevSpace.GraphSpace
