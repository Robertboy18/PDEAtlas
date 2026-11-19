/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Real

/-!
# The real Radon transform on Schwartz space

The complex Schwartz-space construction agrees with the hyperplane
integral at every point. Complexifying real data, applying that construction,
and taking the real part gives a continuous real-linear Radon map.

This retains smoothness and rapid decay together, so analytic results for
one-dimensional Schwartz functions apply directly to real Radon data.
-/

@[expose] public noncomputable section

open scoped SchwartzMap

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The real Radon transform as a continuous linear map on Schwartz spaces. -/
def radonTransformRealCLM {θ : E} (hθ : ‖θ‖ = 1) :
    𝓢(E, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) :=
  postcompCLM Complex.reCLM ∘L (radonTransformCLM hθ).restrictScalars ℝ ∘L
    postcompCLM Complex.ofRealCLM

/-- The real Schwartz-space map gives the hyperplane integral at every displacement. -/
theorem radonTransformRealCLM_apply {θ : E} (hθ : ‖θ‖ = 1) (f : 𝓢(E, ℝ)) :
    (radonTransformRealCLM hθ f : ℝ → ℝ) =
      PDE.Analysis.Fourier.radonTransform f θ := by
  funext s
  change (radonTransformCLM hθ (f.postcompCLM Complex.ofRealCLM) s).re = _
  rw [radonTransformCLM_apply]
  change (PDE.Analysis.Fourier.radonTransform (fun x ↦ (f x : ℂ)) θ s).re = _
  rw [PDE.Analysis.Fourier.radonTransform_ofReal]
  rfl

end SchwartzMap
