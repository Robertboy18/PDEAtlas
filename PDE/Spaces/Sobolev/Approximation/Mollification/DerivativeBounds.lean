/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Differentiated
public import PDE.Spaces.Sobolev.Approximation.Mollification.KernelMoment
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Bounds for differentiated mollifiers

One derivative of the scaled kernel costs one inverse power of its scale.
The change of variables in the L¹ norm cancels the volume normalization,
leaving exactly that inverse power. Thus multiplying the derivative operator
by the scale gives a bound independent of the scale.

For H¹ initial data this controls the viscous term `ε Δ(ρ_ε * g)` uniformly.
One derivative falls on the kernel and the other remains a weak derivative
of the original datum.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Approximation

open MeasureTheory GraphSpace
open scoped ENNReal Sobolev Laplacian

variable {n : ℕ}

/-- The L¹ norm of a directional kernel derivative scales by the inverse length. -/
theorem integral_norm_fderiv_scaled_apply
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (v : ℝ^n) :
    (∫ x, ‖fderiv ℝ (scaled μ ε) x v‖) =
      ε⁻¹ * ∫ x, ‖fderiv ℝ μ.ρ x v‖ := by
  let g : ℝ^n → ℝ := fun x ↦ ‖fderiv ℝ μ.ρ x v‖
  have hpoint (x : ℝ^n) :
      ‖fderiv ℝ (scaled μ ε) x v‖ = ((ε⁻¹) ^ n * ε⁻¹) * g (ε⁻¹ • x) := by
    rw [fderiv_scaled_apply μ hε]
    simp only [norm_mul, Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hε.le) n),
      Real.norm_of_nonneg (inv_nonneg.mpr hε.le), mul_assoc, g]
  have hfinrank : Module.finrank ℝ (ℝ^n) = n := by simp
  have hscale : (∫ x, g (ε⁻¹ • x)) = ε ^ n * ∫ x, g x := by
    simpa only [hfinrank, smul_eq_mul] using
      (Measure.integral_comp_inv_smul_of_nonneg
        (μ := (volume : Measure (ℝ^n))) (f := g) hε.le)
  calc
    _ = ((ε⁻¹) ^ n * ε⁻¹) * ∫ x, g (ε⁻¹ • x) := by
      simp_rw [hpoint]
      exact integral_const_mul _ _
    _ = ((ε⁻¹) ^ n * ε⁻¹) * (ε ^ n * ∫ x, g x) := by rw [hscale]
    _ = ε⁻¹ * ∫ x, g x := by
      rw [inv_pow]
      field_simp

/-- Scaling the differentiated L² mollifier by its length removes the inverse-scale
growth. The same estimate holds for normed vector-valued inputs. -/
theorem mul_norm_mollifierDerivativeL2CLM_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (j : Fin n) :
    ε * ‖mollifierDerivativeL2CLM (E := E) μ hε j‖ ≤
      ∫ x, ‖fderiv ℝ μ.ρ x (EuclideanSpace.single j 1)‖ := by
  have h := mul_le_mul_of_nonneg_left
    (norm_mollifierDerivativeL2CLM_le (E := E) μ hε j) hε.le
  change ε * ‖mollifierDerivativeL2CLM (E := E) μ hε j‖ ≤
    ε * (∫ x, ‖fderiv ℝ (scaled μ ε) x (EuclideanSpace.single j 1)‖) at h
  rw [integral_norm_fderiv_scaled_apply μ hε, ← mul_assoc,
    mul_inv_cancel₀ hε.ne', one_mul] at h
  exact h

/-- The derivative bound in the Sobolev coordinate model follows by its L² isometry. -/
theorem mul_norm_mollifierDerivativeRowCLM_apply_le
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (j : Fin n)
    (u : DerivLp n 2 Set.univ) :
    ε * ‖mollifierDerivativeRowCLM μ hε j u‖ ≤
      (∫ x, ‖fderiv ℝ μ.ρ x (EuclideanSpace.single j 1)‖) * ‖u‖ := by
  rw [← wholeSpaceL2Equiv.norm_map (mollifierDerivativeRowCLM μ hε j u),
    wholeSpaceL2Equiv_mollifierDerivativeRowCLM, ← wholeSpaceL2Equiv.norm_map u]
  calc
    _ ≤ ε * (‖mollifierDerivativeL2CLM (E := ℝ) μ hε j‖ * ‖wholeSpaceL2Equiv u‖) :=
      mul_le_mul_of_nonneg_left
        ((mollifierDerivativeL2CLM (E := ℝ) μ hε j).le_opNorm
          (wholeSpaceL2Equiv u)) hε.le
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_norm_mollifierDerivativeL2CLM_le (E := ℝ) μ hε j) (norm_nonneg _)

/-- A second derivative of smoothed H¹ data puts one derivative on the kernel
and one on the original datum; no second weak derivative of the datum is needed. -/
theorem mollifierSmoothingCLM_pair_of_H1
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (i j : Fin n) (U : H¹(ℝ^n)) :
    wkpCoordinateCLM (pairDerivIndex n i j)
        (mollifierSmoothingCLM 2 μ hε (wkpBaseCoordinateCLM U)) =
      mollifierDerivativeRowCLM μ hε j
        (wkpCoordinateCLM (singleDerivIndex n i) U) := by
  have h := congrArg (fun V : H¹(ℝ^n) ↦ wkpCoordinateCLM (singleDerivIndex n j) V)
    (derivativeWordCLM_mollifierSmoothingCLM
      (r := 1) (s := 2) [i] (by simp) (by simp) μ hε U)
  rw [mollifierSmoothingCLM_one, mollifierH1CLM_derivative] at h
  simpa only [wkpCoordinateCLM_apply, derivativeWordCLM_apply, derivativeWordIndex,
    singleDerivIndex_toList, List.cons_append, List.nil_append,
    pairDerivIndex, secondDerivIndex, derivIndexOfList_singleton,
    firstDerivIndex_one] using h

/-- The viscous Laplacian of mollified H¹ data is bounded independently of the
scale. Each diagonal derivative uses one derivative of the fixed kernel. -/
theorem mul_norm_laplacian_mollifierSmoothingCLM_le
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (U : H¹(ℝ^n)) :
    ε * ‖Δ (mollifierSmoothingCLM 2 μ hε (wkpBaseCoordinateCLM U))‖ ≤
      (∑ j : Fin n, ∫ x, ‖fderiv ℝ μ.ρ x (EuclideanSpace.single j 1)‖) * ‖U‖ := by
  classical
  rw [laplacian_eq_wkpLaplacianCLM, wkpLaplacianCLM_apply]
  change ε * ‖∑ j : Fin n, wkpCoordinateCLM (pairDerivIndex n j j)
      (mollifierSmoothingCLM 2 μ hε (wkpBaseCoordinateCLM U))‖ ≤ _
  simp_rw [mollifierSmoothingCLM_pair_of_H1]
  calc
    _ ≤ ε * ∑ j : Fin n, ‖mollifierDerivativeRowCLM μ hε j
        (wkpCoordinateCLM (singleDerivIndex n j) U)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hε.le
    _ = ∑ j : Fin n, ε * ‖mollifierDerivativeRowCLM μ hε j
        (wkpCoordinateCLM (singleDerivIndex n j) U)‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ j : Fin n, (∫ x, ‖fderiv ℝ μ.ρ x (EuclideanSpace.single j 1)‖) * ‖U‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact (mul_norm_mollifierDerivativeRowCLM_apply_le μ hε j _).trans
        (mul_le_mul_of_nonneg_left (wkpCoordinateCLM_norm_le _ U)
          (integral_nonneg fun x ↦ norm_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

end SobolevSpace.Approximation
