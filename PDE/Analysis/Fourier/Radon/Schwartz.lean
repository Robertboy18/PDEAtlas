/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Continuity
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The Radon transform on Schwartz space

An orthogonal marginal is again a Schwartz function. We construct the
continuous linear map by restricting the Fourier transform to the base
subspace and applying Fourier inversion there. The Fourier slice theorem
identifies this construction with the fiber integral at every point;
continuity of that integral is the step that upgrades the `L¹` identity.

For each unit normal, composition with the isometry from the real line
to its span gives the Radon transform as a continuous linear map into
one-dimensional Schwartz space. Smoothness and rapid decay therefore
follow from the original Schwartz data.
-/

@[expose] public noncomputable section

open FourierTransform
open scoped SchwartzMap

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Integrating out an orthogonal subspace, bundled as a continuous linear
map between Schwartz spaces. Fourier inversion realizes the marginal. -/
def orthogonalMarginalCLM (K : Submodule ℝ E) : 𝓢(E, F) →L[ℂ] 𝓢(K, F) :=
  fourierInvCLM ℂ 𝓢(K, F) ∘L
    compCLMOfAntilipschitz ℂ K.subtypeL.hasTemperateGrowth
      K.subtypeₗᵢ.isometry.antilipschitzWith ∘L
    fourierCLM ℂ 𝓢(E, F)

/-- For a fixed unit normal, the Radon transform is a continuous linear map
from ambient Schwartz space to Schwartz functions of the displacement. -/
def radonTransformCLM {θ : E} (hθ : ‖θ‖ = 1) : 𝓢(E, F) →L[ℂ] 𝓢(ℝ, F) :=
  compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.toSpanUnitSingleton θ hθ).toContinuousLinearEquiv ∘L
    orthogonalMarginalCLM (ℝ ∙ θ)

variable [CompleteSpace F]

/-- The Schwartz-space marginal is the orthogonal fiber integral
at every base point. -/
theorem orthogonalMarginalCLM_apply (K : Submodule ℝ E) (f : 𝓢(E, F)) :
    (orthogonalMarginalCLM K f : K → F) =
      PDE.Analysis.Fourier.orthogonalMarginal K f := by
  let R : 𝓢(E, F) →L[ℂ] 𝓢(K, F) :=
    compCLMOfAntilipschitz ℂ K.subtypeL.hasTemperateGrowth
      K.subtypeₗᵢ.isometry.antilipschitzWith
  have hslice : (R (𝓕 f) : K → F) =
      𝓕 (PDE.Analysis.Fourier.orthogonalMarginal K f) := by
    funext ξ
    exact (PDE.Analysis.Fourier.fourier_orthogonalMarginal K f.integrable ξ).symm
  change ((𝓕⁻ (R (𝓕 f)) : 𝓢(K, F)) : K → F) = _
  rw [fourierInv_coe, hslice]
  exact (f.continuous_orthogonalMarginal K).fourierInv_fourier_eq
    (PDE.Analysis.Fourier.integrable_orthogonalMarginal K f.integrable)
    (hslice ▸ (R (𝓕 f)).integrable)

/-- The bundled Radon transform agrees everywhere with the hyperplane integral. -/
theorem radonTransformCLM_apply {θ : E} (hθ : ‖θ‖ = 1) (f : 𝓢(E, F)) :
    (radonTransformCLM hθ f : ℝ → F) =
      PDE.Analysis.Fourier.radonTransform f θ := by
  let A : ℝ ≃ₗᵢ[ℝ] ℝ ∙ θ := LinearIsometryEquiv.toSpanUnitSingleton θ hθ
  change (fun s : ℝ ↦ orthogonalMarginalCLM (ℝ ∙ θ) f (A s)) = _
  rw [orthogonalMarginalCLM_apply]
  rfl

/-- Hyperplane integrals of Schwartz data are smooth in the displacement. -/
theorem contDiff_radonTransform (f : 𝓢(E, F)) {θ : E} (hθ : ‖θ‖ = 1) (n : ℕ∞) :
    ContDiff ℝ n (PDE.Analysis.Fourier.radonTransform f θ) := by
  rw [← radonTransformCLM_apply hθ f]
  exact (radonTransformCLM hθ f).smooth n

/-- Fourier slices of the bundled transform retain Mathlib's `2π` normalization. -/
theorem fourier_radonTransformCLM_apply {θ : E} (hθ : ‖θ‖ = 1)
    (f : 𝓢(E, F)) (σ : ℝ) :
    𝓕 (radonTransformCLM hθ f) σ = 𝓕 f (σ • θ) := by
  change 𝓕 (radonTransformCLM hθ f : ℝ → F) σ = _
  rw [radonTransformCLM_apply]
  exact PDE.Analysis.Fourier.fourier_radonTransform f.integrable hθ σ

end SchwartzMap
