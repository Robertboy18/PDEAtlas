/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.OrthogonalDecomposition
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The Radon transform and the Fourier slice theorem

The Radon transform integrates a function over affine hyperplanes. For a
unit normal `θ`, the hyperplane at signed distance `s` consists of the points
`s • θ + y` with `y` orthogonal to `θ`. We use the induced Euclidean volume
on this orthogonal complement.

Taking the one-dimensional Fourier transform in `s` gives the ambient
Fourier transform on the line through `θ`. The proof first establishes the
same statement for the marginal along an arbitrary orthogonal subspace;
the hyperplane case follows from Mathlib's isometry between the real line
and the span of a unit vector.

Only integrability of the original function is assumed. Fubini supplies
integrability of the marginal; individual hyperplane integrals need exist
only for almost every `s`. The Fourier convention is Mathlib's
`exp (-2 * π * I * ⟪x, ξ⟫)`, so the slice identity has no prefactor.

`radonTransform` is Evans's (30) in §4.3.2, and `fourier_radonTransform` is his Theorem 4,
(31), in Mathlib's convention, without his factor `(2π)^(n/2)`. Evans assumes `u ∈ C_c^∞`; we
assume only integrability.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.2, the definition (30), p. 197, and Theorem 4, (31),
  p. 198. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace

namespace PDE.Analysis.Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]

section Real

variable [NormedSpace ℝ F]

/-- Integrate over the orthogonal fibers above the subspace `K`. -/
def orthogonalMarginal (K : Submodule ℝ E) (f : E → F) (x : K) : F :=
  ∫ y : Kᗮ, f ((x : E) + (y : E))

/-- An `L¹` function has an `L¹` orthogonal marginal. -/
theorem integrable_orthogonalMarginal (K : Submodule ℝ E) {f : E → F}
    (hf : Integrable f) : Integrable (orthogonalMarginal K f) :=
  (integrable_add_orthogonal K hf).integral_prod_left

/-- Hyperplane integrals parameterized by a normal and a signed displacement.
The geometric interpretation of `s` as distance requires `‖θ‖ = 1`. -/
def radonTransform (f : E → F) (θ : E) (s : ℝ) : F :=
  ∫ y : (ℝ ∙ θ)ᗮ, f (s • θ + (y : E))

/-- For each unit normal, the Radon transform of an integrable function is
integrable in its signed displacement. -/
theorem integrable_radonTransform {f : E → F} (hf : Integrable f)
    {θ : E} (hθ : ‖θ‖ = 1) : Integrable (radonTransform f θ) := by
  let A : ℝ ≃ₗᵢ[ℝ] ℝ ∙ θ := LinearIsometryEquiv.toSpanUnitSingleton θ hθ
  change Integrable (orthogonalMarginal (ℝ ∙ θ) f ∘ A)
  exact A.measurePreserving.integrable_comp_of_integrable
    (integrable_orthogonalMarginal (ℝ ∙ θ) hf)

end Real

section Complex

variable [NormedSpace ℂ F]

/-- Integrating out an orthogonal subspace restricts the Fourier transform
to the remaining subspace. -/
theorem fourier_orthogonalMarginal (K : Submodule ℝ E) {f : E → F}
    (hf : Integrable f) (ξ : K) :
    𝓕 (orthogonalMarginal K f) ξ = 𝓕 f (ξ : E) := by
  have horth (y : Kᗮ) : ⟪(y : E), (ξ : E)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal ξ.property y.property
  rw [Real.fourier_eq, Real.fourier_eq,
    integral_add_orthogonal K ((Real.fourierIntegral_convergent_iff (ξ : E)).mpr hf)]
  simp_rw [inner_add_left, horth, add_zero, ← Submodule.coe_inner,
    orthogonalMarginal, Circle.smul_def, integral_smul]

/-- The Fourier slice theorem: transforming the Radon data in the displacement
variable recovers the ambient Fourier transform on the corresponding line. -/
theorem fourier_radonTransform {f : E → F} (hf : Integrable f)
    {θ : E} (hθ : ‖θ‖ = 1) (σ : ℝ) :
    𝓕 (radonTransform f θ) σ = 𝓕 f (σ • θ) := by
  let A : ℝ ≃ₗᵢ[ℝ] ℝ ∙ θ := LinearIsometryEquiv.toSpanUnitSingleton θ hθ
  have h := Real.fourier_comp_linearIsometry
    (f := orthogonalMarginal (ℝ ∙ θ) f) A σ
  calc
    𝓕 (radonTransform f θ) σ =
        𝓕 (orthogonalMarginal (ℝ ∙ θ) f) (A σ) := h
    _ = 𝓕 f ((A σ : ℝ ∙ θ) : E) := fourier_orthogonalMarginal _ hf _
    _ = 𝓕 f (σ • θ) := rfl

end Complex

end PDE.Analysis.Fourier
