/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.FourierMoments
public import PDE.Common.Euclidean.SpaceTime
public import PDE.Hyperbolic.Models.Wave.InitialValueProblem

/-!
# Classical cosine waves from integrable frequency moments

Three integrable frequency moments yield a C² real solution in canonical
spacetime coordinates. The wave equation and both initial traces follow from the derivatives of the
Fourier integral.
-/

@[expose] public section

open PDE (SatisfiesPDEProblem)
open MeasureTheory FourierTransform PDE.Analysis.Fourier
open scoped Topology

namespace WaveEquation.Fourier
open PDE.Common WaveEquation
variable {n : ℕ}

/-- Real projection of a cosine Fourier wave in canonical spacetime coordinates. -/
noncomputable def realCosineSolution (G : ℝ^n → ℂ) : ℝ^(n + 1) → ℝ :=
  Complex.reCLM ∘ waveSolution G 0 ∘ timeSpaceContinuousLinearEquiv n

/-- Integrable frequency moments give joint C² regularity in canonical coordinates. -/
theorem contDiff_two_realCosineSolution {G : ℝ^n → ℂ} (hG : Integrable G)
    (hG₁ : Integrable (fun ξ ↦ ‖ξ‖ * ‖G ξ‖)) (hG₂ : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖G ξ‖)) :
    ContDiff ℝ 2 (realCosineSolution G) :=
  Complex.reCLM.contDiff.comp ((cosine_wave_regular_of_integrable_moments hG hG₁ hG₂).1.comp
      (timeSpaceContinuousLinearEquiv n).contDiff)

/-- The cosine wave has zero initial time derivative, obtained from its integral derivative. -/
theorem waveSolution_initial_time_derivative_of_integrable_moments {G : ℝ^n → ℂ}
    (hG : Integrable G) (hG₁ : Integrable (fun ξ ↦ ‖ξ‖ * ‖G ξ‖))
    (hG₂ : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖G ξ‖)) (x : ℝ^n) :
    fderiv ℝ (waveSolution G 0) (0, x) (1, 0) = 0 := by
  obtain ⟨hKi, hD, _⟩ := (cosine_wave_regular_of_integrable_moments hG hG₁ hG₂).2 (0, x)
  rw [hD.fderiv, ContinuousLinearMap.integral_apply hKi]
  simp [waveFirstKernel, PDE.Analysis.Fourier.inverseKernelDerivative_apply, waveVelocity]

/-- At zero time the real cosine wave equals the real inverse Fourier datum. -/
theorem realCosineSolution_initial_position (G : ℝ^n → ℂ) (x : ℝ^n) :
    realCosineSolution G (timeSpaceCons 0 x) = (𝓕⁻ G x).re := by
  simp [realCosineSolution, Function.comp_def, PDE.time, waveSolution_initial_position]

/-- The canonical time derivative of the real cosine wave vanishes at zero. -/
theorem partialDeriv_realCosineSolution_initial_velocity {G : ℝ^n → ℂ}
    (hG : Integrable G) (hG₁ : Integrable (fun ξ ↦ ‖ξ‖ * ‖G ξ‖))
    (hG₂ : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖G ξ‖)) (x : ℝ^n) :
    (∂[(0 : Fin (n + 1))] (realCosineSolution G)) (timeSpaceCons 0 x) = 0 := by
  let u := waveSolution G 0
  let L := (timeSpaceContinuousLinearEquiv n).toContinuousLinearMap
  have hu : ContDiff ℝ 2 u := (cosine_wave_regular_of_integrable_moments hG hG₁ hG₂).1
  have htime : L (EuclideanSpace.single (0 : Fin (n + 1)) 1) = (1, 0) := by
    change timeSpaceContinuousLinearEquiv n (EuclideanSpace.single (0 : Fin (n + 1)) 1) = (1, 0)
    rw [timeSpaceContinuousLinearEquiv_apply,
      ← spatialPartCLM_eq_spatialPart, spatialPartCLM_single_zero]
    simp [PDE.time]
  change fderiv ℝ (Complex.reCLM ∘ u ∘ L) (timeSpaceCons 0 x) _ = _
  rw [fderiv_comp _ Complex.reCLM.differentiableAt
    ((hu.differentiable (by norm_num)).differentiableAt.comp _ L.differentiableAt),
    fderiv_comp _ ((hu.differentiable (by norm_num)).differentiableAt) L.differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, htime]
  change (fderiv ℝ u (0, x) (1, 0)).re = 0
  rw [waveSolution_initial_time_derivative_of_integrable_moments hG hG₁ hG₂]
  rfl

/-- The constructed Fourier field solves the wave equation at every spacetime point. -/
theorem waveOperator_realCosineSolution {G : ℝ^n → ℂ}
    (hG : Integrable G) (hG₁ : Integrable (fun ξ ↦ ‖ξ‖ * ‖G ξ‖))
    (hG₂ : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖G ξ‖)) (p : ℝ^(n + 1)) :
    waveOperator (realCosineSolution G) p = 0 := by
  let u := waveSolution G 0
  let L := (timeSpaceContinuousLinearEquiv n).toContinuousLinearMap
  have hu : ContDiff ℝ 2 u := (cosine_wave_regular_of_integrable_moments hG hG₁ hG₂).1
  have hsecond (i : Fin (n + 1)) : (∂[i] (∂[i] (realCosineSolution G))) p =
        (fderiv ℝ (fderiv ℝ u) (L p)
          (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single i 1))).re := by
    change (∂[i] (∂[i] (Complex.reCLM ∘ (u ∘ L)))) p = _
    rw [PDE.secondPartialDeriv_eq_iteratedFDeriv_apply i i
      (Complex.reCLM.contDiff.comp (hu.comp L.contDiff)).contDiffAt,
      Complex.reCLM.iteratedFDeriv_comp_left (hu.comp L.contDiff).contDiffAt le_rfl,
      L.iteratedFDeriv_comp_right hu p le_rfl]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply]
  have htime : L (EuclideanSpace.single (0 : Fin (n + 1)) 1) = (1, 0) := by
    change timeSpaceContinuousLinearEquiv n (EuclideanSpace.single (0 : Fin (n + 1)) 1) = (1, 0)
    rw [timeSpaceContinuousLinearEquiv_apply,
      ← spatialPartCLM_eq_spatialPart, spatialPartCLM_single_zero]
    simp [PDE.time]
  have hspace (i : Fin n) :
      L (EuclideanSpace.single i.succ 1) = (0, EuclideanSpace.single i 1) := by
    change timeSpaceContinuousLinearEquiv n
      (EuclideanSpace.single i.succ 1) = (0, EuclideanSpace.single i 1)
    rw [timeSpaceContinuousLinearEquiv_apply,
      ← spatialPartCLM_eq_spatialPart, spatialPartCLM_single_succ]
    simp [PDE.time]
  have hw := congrArg Complex.reCLM (waveSolution_waveTrace_of_integrable_moments hG hG₁ hG₂ (L p))
  simpa only [waveOperator, hsecond, htime, hspace, waveTrace_apply,
    map_sub, map_sum, map_zero, Complex.reCLM_apply] using hw

/-- The real cosine wave satisfies the assigned homogeneous Cauchy problem. -/
theorem realCosineSolution_satisfiesResidualAssignedCauchyData {G : ℝ^n → ℂ} (hG : Integrable G)
    (hG₁ : Integrable (fun ξ ↦ ‖ξ‖ * ‖G ξ‖)) (hG₂ : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖G ξ‖)) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem
      (fun x ↦ (𝓕⁻ G x).re) (fun _ ↦ 0)) (realCosineSolution G) := by
  apply forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial
  · exact fun p _ ↦ waveOperator_realCosineSolution hG hG₁ hG₂ p
  · intro p hp
    have heq : p = timeSpaceCons 0 (spatialPartCLM n p) := by
      rw [← hp, timeSpaceCons_spatialPartCLM]
    rw [heq, realCosineSolution_initial_position, spatialPartCLM_timeSpaceCons]
  · intro p hp
    have heq : p = timeSpaceCons 0 (spatialPartCLM n p) := by
      rw [← hp, timeSpaceCons_spatialPartCLM]
    rw [heq, partialDeriv_realCosineSolution_initial_velocity hG hG₁ hG₂]

end WaveEquation.Fourier
