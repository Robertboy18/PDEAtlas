/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Harmonic.WeakDecay
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.BallEnergy
import PDE.Elliptic.Variational.Harmonic.Extension

/-!
# Gradient oscillation for the Poisson equation with divergence forcing

For a weak `H¹` solution of `Δu = div F`, harmonic replacement and
testing the correction with itself give an error bounded by the `L²` energy
of `F`. The quadratic harmonic decay then gives a one-step gradient
oscillation estimate, with explicit constants independent of the radii.

The comparison is constructed by the harmonic extension theorem.
Neither a comparison field nor its energy estimate is an input.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev InnerProductSpace

namespace SobolevSpace.GraphSpace

open PDE.Elliptic.Regularity.Campanato

variable {n : ℕ} [Fact (0 < n)]

/-- A weak Poisson solution has harmonic quadratic gradient decay up to the
mean energy of its divergence forcing. This is the one-step Campanato
estimate for the original Sobolev gradient coordinates. -/
theorem meanSquare_gradient_oscillation_le_of_dirichlet_eq_divergence
    {z : ℝ^n} {R r : ℝ} (U : H¹(ball z R))
    (F : Fin n → DerivLp n 2 (ball z R))
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
        ((volume.real (ball z R))⁻¹ * ∑ j, ‖F j‖ ^ 2) := by
  have hR : 0 < R := by linarith
  classical
  obtain ⟨w, hw⟩ := exists_weak_harmonic_extension (Fact.out : 0 < n) isBounded_ball U
  let H : H¹(ball z R) := U + (w : H¹(ball z R))
  have hD (j : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n j) (w : H¹(ball z R)) =
        derivCoordCLM j w := by
    rw [wkpCoordinateCLM_apply, derivCoordCLM_apply]
  have hpair : (∑ j, ⟪F j, derivCoordCLM j w⟫_ℝ) +
      ∑ j, ‖derivCoordCLM j w‖ ^ 2 = 0 := by
    have ht := hw w
    simp only [map_add, hD, inner_add_left, Finset.sum_add_distrib,
      real_inner_self_eq_norm_sq] at ht
    rwa [hweak w] at ht
  have henergy : (∑ j, ‖derivCoordCLM j w‖ ^ 2) ≤ ∑ j, ‖F j‖ ^ 2 := by
    have hs := Finset.sum_nonneg
      (s := Finset.univ) (fun j _ ↦ sq_nonneg ‖F j + derivCoordCLM j w‖)
    simp only [norm_add_sq_real, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    linarith
  let d : ℝ^n → ℝ := wkpCoordinateCLM (singleDerivIndex n i) U
  let e : ℝ^n → ℝ := wkpCoordinateCLM (singleDerivIndex n i) H
  have hd : MemLp d 2 (volume.restrict (ball z R)) := Lp.memLp _
  have he : MemLp e 2 (volume.restrict (ball z R)) := Lp.memLp _
  have hsub : wkpCoordinateCLM (singleDerivIndex n i) U -
      wkpCoordinateCLM (singleDerivIndex n i) H = -(derivCoordCLM i w) := by
    simp only [H, map_add, hD]
    abel
  have herror : (⨍ x in ball z R, ‖d x - e x‖ ^ 2) ≤
      (volume.real (ball z R))⁻¹ * ∑ j, ‖F j‖ ^ 2 := by
    calc
      _ = (volume.real (ball z R))⁻¹ *
          ‖wkpCoordinateCLM (singleDerivIndex n i) U -
            wkpCoordinateCLM (singleDerivIndex n i) H‖ ^ 2 := by
        rw [setAverage_eq, smul_eq_mul, Lp.norm_sq_eq_integral_norm_sq]
        congr 1
        exact integral_congr_ae ((Lp.coeFn_sub _ _).fun_comp
          (fun t : ℝ ↦ ‖t‖ ^ 2)).symm
      _ = (volume.real (ball z R))⁻¹ * ‖derivCoordCLM i w‖ ^ 2 := by
        rw [hsub, norm_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖derivCoordCLM j w‖)
          (Finset.mem_univ i)).trans henergy) (inv_nonneg.mpr measureReal_nonneg)
  have hrR' : r ≤ R := hrR.trans (by linarith)
  have herrSmall := (setAverage_norm_sq_le_of_radius_le hr hrR' (hd.sub he)).trans
    (mul_le_mul_of_nonneg_left herror (pow_nonneg (div_nonneg hR.le hr.le) n))
  have hcompare := setAverage_oscillation_sq_le_comparison
    (hd.mono_measure (Measure.restrict_mono (ball_subset_ball hrR') le_rfl))
    (he.mono_measure (Measure.restrict_mono (ball_subset_ball hrR') le_rfl))
  have hdecay := meanSquare_gradient_oscillation_le_of_dirichlet_eq_zero
    H hw hr hrR i (⨍ y in ball z R, d y)
  have houter := setAverage_norm_sub_sq_le he hd
    (⨍ y in ball z R, d y)
  simp only [norm_sub_rev (e _) (d _)] at houter
  have hscaled := mul_le_mul_of_nonneg_left houter
    (sq_nonneg ((((2 : ℝ) ^ (2 * n + 3) * n) * (r / R))))
  change (⨍ x in ball z r, ‖e x - ⨍ y in ball z r, e y‖ ^ 2) ≤ _ at hdecay
  change (⨍ x in ball z r, ‖d x - ⨍ y in ball z r, d y‖ ^ 2) ≤ _
  have hscaledError := mul_le_mul_of_nonneg_left herror
    (sq_nonneg ((((2 : ℝ) ^ (2 * n + 3) * n) * (r / R))))
  simp only [Pi.sub_apply] at herrSmall
  dsimp only [d, e] at herrSmall hcompare hscaled hdecay hscaledError ⊢
  nlinarith only [herrSmall, hcompare, hscaled, hdecay, hscaledError]

end SobolevSpace.GraphSpace
