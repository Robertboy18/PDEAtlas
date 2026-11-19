/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.FourierMoments

/-!
# The Laplacian of an inverse Fourier integral

Two integrable frequency moments justify the Laplacian multiplier.
The proof restricts the joint cosine wave to zero time and contracts its
integral Hessian in an orthonormal basis. No Schwartz assumption is needed.
-/

@[expose] public section

open MeasureTheory FourierTransform PDE.Analysis.Fourier

namespace WaveEquation.Fourier

attribute [local instance] instNormedAddCommGroupComplexDerivative
  instNormedSpaceComplexDerivative instNormedAddCommGroupComplexHessian
  instNormedSpaceComplexHessian instContinuousENormWaveDerivative
  instContinuousENormWaveHessian

/-- Integrable frequency moments give the Laplacian of the inverse Fourier integral. -/
theorem laplacian_fourierInv_of_integrable_moments {n : ℕ} {G : ℝ^n → ℂ}
    (hG : Integrable G) (hG₁ : Integrable (fun ξ ↦ ‖ξ‖ * ‖G ξ‖))
    (hG₂ : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖G ξ‖)) (x : ℝ^n) :
    Laplacian.laplacian (𝓕⁻ G : ℝ^n → ℂ) x = 𝓕⁻ (fun ξ ↦ -((2 * Real.pi * ‖ξ‖) ^ 2) • G ξ) x := by
  let u := waveSolution G 0
  let L : ℝ^n →L[ℝ] ℝ × ℝ^n := ContinuousLinearMap.inr ℝ ℝ (ℝ^n)
  have hreg := cosine_wave_regular_of_integrable_moments hG hG₁ hG₂
  have hu : ContDiff ℝ 2 u := hreg.1
  have hv : 𝓕⁻ G = u ∘ L := funext fun y ↦ (waveSolution_initial_position G 0 y).symm
  have hsp : Laplacian.laplacian (𝓕⁻ G : ℝ^n → ℂ) x = ∑ i : Fin n, fderiv ℝ (fderiv ℝ u) (0, x)
        (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1) := by
    rw [hv, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (u ∘ L) (EuclideanSpace.basisFun (Fin n) ℝ)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [L.iteratedFDeriv_comp_right hu x le_rfl]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply, L]
  have hw := waveSolution_waveTrace_of_integrable_moments hG hG₁ hG₂ (0, x)
  rw [waveTrace_apply] at hw
  rw [hsp, ← sub_eq_zero.mp hw]
  obtain ⟨hKi, hD⟩ := (hreg.2 (0, x)).2.2
  change diagonalEval (E := ℝ × ℝ^n) (1, 0) (fderiv ℝ (fderiv ℝ u) (0, x)) = _
  rw [hD.fderiv, ← (diagonalEval (E := ℝ × ℝ^n) (1, 0)).integral_comp_comm hKi]
  simp only [diagonalEval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    waveSecondKernel_time, waveAcceleration, mul_zero, Real.cos_zero, Real.sin_zero,
    mul_one, zero_smul, add_zero, Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]

end WaveEquation.Fourier
