/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Schwartz

/-!
# Differentiation through the Radon transform

For a unit normal `θ`, an ambient derivative in direction `v` becomes
`⟪θ, v⟫` times differentiation in the displacement. Tangential derivatives
therefore disappear, and the ambient Laplacian becomes the second derivative
on the real line.

We prove the directional identity using Fourier slices and Mathlib's Fourier
derivative theorem. Summing over an orthonormal basis then gives the Laplacian
identity, since the squared normal components sum to one. The Schwartz-space
construction supplies smoothness and integrability, so these are identities for
the hyperplane integrals at every point.

`radonTransformCLM_lineDerivOp` and `radonTransform_fderiv` are Evans, §4.3.2, Theorem 3(ii),
for first derivatives in any direction, and `radonTransformCLM_laplacian` and
`radonTransform_laplacian` are Theorem 3(iii). Evans proves (ii) for compactly supported
smooth `u` with an orthonormal basis of the hyperplane; we prove the directional identity for
Schwartz functions with Fourier slices.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.2, Theorem 3(ii)-(iii) and its proof, pp. 197-198.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open FourierTransform LineDeriv Laplacian
open scoped SchwartzMap RealInnerProductSpace

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Only the component of an ambient derivative in the normal direction
survives integration over a hyperplane. -/
theorem radonTransformCLM_lineDerivOp {θ : E} (hθ : ‖θ‖ = 1)
    (f : 𝓢(E, F)) (v : E) :
    radonTransformCLM hθ (∂_{v} f) =
      ⟪θ, v⟫ • ∂_{(1 : ℝ)} (radonTransformCLM hθ f) := by
  apply (fourierEquiv ℂ 𝓢(ℝ, F)).injective
  ext σ
  change 𝓕 (radonTransformCLM hθ (∂_{v} f)) σ =
    𝓕 (⟪θ, v⟫ • ∂_{(1 : ℝ)} (radonTransformCLM hθ f)) σ
  have hg : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  have hg' : (inner ℝ · (1 : ℝ)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (1 : ℝ)).hasTemperateGrowth
  rw [fourier_radonTransformCLM_apply, fourier_smul,
    fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
  simp only [smul_apply]
  rw [smulLeftCLM_apply_apply hg, smulLeftCLM_apply_apply hg']
  simp only [real_inner_smul_left, Real.inner_apply, mul_one,
    fourier_radonTransformCLM_apply]
  rw [mul_comm σ, mul_smul ⟪θ, v⟫ σ, smul_comm (2 * Real.pi * Complex.I) ⟪θ, v⟫]

/-- The Radon transform turns the ambient Laplacian into the one-dimensional
second derivative. -/
theorem radonTransformCLM_laplacian {θ : E} (hθ : ‖θ‖ = 1)
    (f : 𝓢(E, F)) :
    radonTransformCLM hθ (Δ f) =
      ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (radonTransformCLM hθ f)) := by
  rw [SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ E), map_sum]
  simp_rw [radonTransformCLM_lineDerivOp, lineDerivOp_smul, smul_smul, ← sq]
  rw [← Finset.sum_smul, (stdOrthonormalBasis ℝ E).sum_sq_inner_left, hθ, one_pow,
    one_smul]

/-- The directional identity written with ordinary Fréchet and real derivatives. -/
theorem radonTransform_fderiv {θ : E} (hθ : ‖θ‖ = 1)
    (f : 𝓢(E, F)) (v : E) (s : ℝ) :
    PDE.Analysis.Fourier.radonTransform (fun x ↦ fderiv ℝ f x v) θ s =
      ⟪θ, v⟫ • deriv (PDE.Analysis.Fourier.radonTransform f θ) s := by
  change PDE.Analysis.Fourier.radonTransform (∂_{v} f : 𝓢(E, F)) θ s = _
  rw [← radonTransformCLM_apply hθ, radonTransformCLM_lineDerivOp]
  simp only [smul_apply, lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv,
    radonTransformCLM_apply]

/-- Integration of the ordinary Laplacian equals the second ordinary derivative
of the hyperplane integral. -/
theorem radonTransform_laplacian {θ : E} (hθ : ‖θ‖ = 1)
    (f : 𝓢(E, F)) (s : ℝ) :
    PDE.Analysis.Fourier.radonTransform (Δ (f : E → F)) θ s =
      deriv (deriv (PDE.Analysis.Fourier.radonTransform f θ)) s := by
  have hΔ : (Δ (f : E → F)) = (Δ f : 𝓢(E, F)) := by
    ext x
    exact (SchwartzMap.laplacian_apply f x).symm
  rw [hΔ, ← radonTransformCLM_apply hθ, radonTransformCLM_laplacian]
  change fderiv ℝ (fun s ↦ fderiv ℝ (radonTransformCLM hθ f) s 1) s 1 = _
  simp only [fderiv_apply_one_eq_deriv, radonTransformCLM_apply]

end SchwartzMap
