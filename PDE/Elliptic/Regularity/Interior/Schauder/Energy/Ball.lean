/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Energy.Cutoff
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Cutoffs
import PDE.Elliptic.Regularity.Coefficients.Restriction

/-!
# Uniform elliptic gradient energy on concentric balls

The cutoff energy estimate gives a Caccioppoli bound on a smaller ball, with
a constant depending only on dimension and ellipticity bounds. The cutoff is
constructed and the weak equation is restricted from the given open domain.
The result requires only H¹ membership and measurable coefficients.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open scoped Sobolev ENNReal Distributions

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- Uniform Caccioppoli on balls, with the correct inverse square dependence
on the gap between radii. The constant is independent of the coefficients,
domain, centre, radii, and weak solution. -/
theorem exists_ball_gradient_sq_le
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set ℝ^n),
      ∀ (a : Fin n → Fin n → DerivLp n ∞ Ω),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(Ω)), IsInteriorWeakDivergenceSolution a 0 u →
      ∀ (z : ℝ^n) (r R : ℝ), 0 < r → r < R → ball z R ⊆ Ω →
        (∑ i, ∫ x in ball z r, wkpCoordinateCLM (singleDerivIndex n i) u x ^ 2) ≤
          C / (R - r) ^ 2 * ∫ x in ball z R, wkpBaseCoordinateCLM u x ^ 2 := by
  obtain ⟨D, hD, hcut⟩ :=
    PDE.Elliptic.Regularity.DeGiorgi.exists_ball_cutoffs_with_derivative_bound (n := n)
  let C := 4 * ((n : ℝ) * n * Λ * D) ^ 2 / α ^ 2 + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro Ω a haΛ ha u hu z r R hr hrR hball
  have := isFiniteMeasure_domainMeasure_of_isBounded (isBounded_ball (x := z) (r := R))
  let V : H¹(ball z R) := restrictCLM isOpen_ball.measurableSet hball u
  let b (i j : Fin n) : DerivLp n ∞ (ball z R) := restrictDerivLp hball (a i j)
  have hbΛ (i j : Fin n) : ‖b i j‖ ≤ Λ :=
    (norm_restrictDerivLp_le hball (a i j)).trans (haΛ i j)
  have hV : IsInteriorWeakDivergenceSolution b 0 V := by
    simpa only [map_zero] using hu.restrict isOpen_ball hball
  obtain ⟨η, hη, hone, _, hηD⟩ := hcut z r R hr hrR
  have hηnorm := norm_partialTestFunctionLpTop_le_of_fderiv_bound
    (V := ball z R) η (div_nonneg hD.le (sub_pos.mpr hrR).le) hηD
  let μ := domainMeasure n (ball z R)
  let q : DerivLp n ∞ (ball z R) := testFunctionLpTop η
  have hmeasure : μ.restrict (ball z r) = volume.restrict (ball z r) :=
    Measure.restrict_restrict_of_subset (ball_subset_ball hrR.le)
  have hcoord (i : Fin n) :
      (∫ x in ball z r, wkpCoordinateCLM (singleDerivIndex n i) u x ^ 2) ≤
        ‖(q • wkpCoordinateCLM (singleDerivIndex n i) V : DerivLp n 2 (ball z R))‖ ^ 2 := by
    let p : DerivLp n 2 (ball z R) := q • wkpCoordinateCLM (singleDerivIndex n i) V
    have hrep : ∀ᵐ x ∂μ, x ∈ ball z r →
        p x = wkpCoordinateCLM (singleDerivIndex n i) u x := by
      filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) q
        (wkpCoordinateCLM (singleDerivIndex n i) V),
        testFunctionLpTop_apply_ae (Ω := ball z R) η,
        restrictCLM_apply_ae isOpen_ball.measurableSet hball u (singleDerivIndex n i)]
        with x hp hqx hvx hx
      change p x = q x * wkpCoordinateCLM (singleDerivIndex n i) V x at hp
      rw [hp, hqx, hone x (ball_subset_closedBall hx), one_mul]
      exact hvx
    calc
      _ = ∫ x in ball z r, p x ^ 2 ∂μ := by
        rw [← hmeasure]
        apply integral_congr_ae
        filter_upwards [hrep.filter_mono (ae_mono Measure.restrict_le_self),
          ae_restrict_mem measurableSet_ball] with x hx hxE
        exact congrArg (fun t : ℝ ↦ t ^ 2) (hx hxE).symm
      _ ≤ ∫ x, p x ^ 2 ∂μ :=
        setIntegral_le_integral (Lp.memLp p).integrable_sq
          (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
      _ = _ := (Lp.norm_sq_eq_integral_sq p).symm
  have hsum : (∑ i, ∑ j, ‖b i j‖ * ‖partialTestFunctionLpTop (Ω := ball z R) η i‖) ≤
      ((n : ℝ) * n * Λ * D) / (R - r) := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, Λ * (D / (R - r)) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
          mul_le_mul (hbΛ i j) (hηnorm i) (norm_nonneg _) hΛ
      _ = _ := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
  have he := hV.cutoff_gradient_sq_le b (ha.restrict hball) 0 V η hη
  change α ^ 2 * ∑ i, ‖(q • wkpCoordinateCLM (singleDerivIndex n i) V :
    DerivLp n 2 (ball z R))‖ ^ 2 ≤ _ at he
  simp only [norm_zero, mul_zero, zero_mul, add_zero] at he
  have hnorm : ‖wkpBaseCoordinateCLM V‖ ^ 2 =
      ∫ x in ball z R, wkpBaseCoordinateCLM u x ^ 2 := by
    rw [Lp.norm_sq_eq_integral_sq]
    exact integral_congr_ae ((restrictCLM_apply_ae isOpen_ball.measurableSet hball
      u (baseIndex n 1)).fun_comp (fun t : ℝ ↦ t ^ 2))
  calc
    _ ≤ ∑ i, ‖(q • wkpCoordinateCLM (singleDerivIndex n i) V :
        DerivLp n 2 (ball z R))‖ ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ hcoord i
    _ ≤ (4 * (((n : ℝ) * n * Λ * D) / (R - r)) ^ 2 *
        ‖wkpBaseCoordinateCLM V‖ ^ 2) / α ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hα), mul_comm]
      exact he.trans (by gcongr)
    _ = (4 * ((n : ℝ) * n * Λ * D) ^ 2 / α ^ 2) / (R - r) ^ 2 *
        ∫ x in ball z R, wkpBaseCoordinateCLM u x ^ 2 := by
      rw [div_pow, hnorm]
      ring
    _ ≤ _ := by gcongr; exact le_add_of_nonneg_right zero_le_one

end SobolevSpace.GraphSpace
