/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Convolution of tempered distributions with Schwartz functions

For a tempered distribution `T` on a finite-dimensional inner product space `E` and a
Schwartz function `φ : 𝓢(E, ℂ)`, the convolution `φ * T` is defined on the Fourier side:

`φ * T := 𝓕⁻¹ ( 𝓕φ · 𝓕T )`,

where `𝓕φ · 𝓕T` is multiplication of the tempered distribution `𝓕T` by the Schwartz (hence
smooth, polynomially bounded) function `𝓕φ`, using Mathlib's `smulLeftCLM`. With Mathlib's
normalization `𝓕φ(ξ) = ∫ e^{-2πi⟨x,ξ⟩} φ(x) dx` no constant appears in the convolution
theorem `𝓕(f * g) = 𝓕f · 𝓕g`, so this definition reproduces the classical convolution of
Schwartz functions (`SchwartzMap.convolution`) when `T` is the regular distribution induced by
a Schwartz function. The Fourier-side definition sidesteps the usual direct construction
`⟨φ * T, ψ⟩ = ⟨T, φ̌ * ψ⟩` (see Hörmander, Chapter VII, or Stein and Weiss, Chapter I), at
the price of requiring the Fourier transform on `𝓢'(E, F)`.

## Main results

* `convolutionSchwartzCLM`: `T ↦ φ * T` as a continuous linear map on `𝓢'(E, F)`.
* `fourier_convolutionSchwartzCLM`: `𝓕(φ * T) = 𝓕φ · 𝓕T`.
* `convolutionSchwartzCLM_toTemperedDistributionCLM_eq`: for `T = f` a Schwartz function, `φ * T`
  is the regular distribution of the Schwartz convolution `f * φ`.
* `lineDerivOp_convolutionSchwartzCLM`: `∂_m (φ * T) = φ * ∂_m T`; on the Fourier side this is
  commutativity of two multiplication operators.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Classics in
  Mathematics, Springer, 2003, Chapter VII, "The Fourier Transformation".
  <https://doi.org/10.1007/978-3-642-61497-2_8>
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  Mathematical Series 32, Princeton University Press, 1971, Chapter I, "The Fourier
  Transform".
  <https://doi.org/10.1515/9781400883899-002>
-/

@[expose] public section

noncomputable section

open FourierTransform
open LineDeriv
open scoped SchwartzMap

namespace TemperedDistribution

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section TopologicalValueSpace

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-- Convolution with a scalar-valued Schwartz function, as a continuous linear map on tempered
distributions. It is defined by Fourier-side multiplication. -/
def convolutionSchwartzCLM (φ : 𝓢(E, ℂ)) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  FourierTransform.fourierInvCLM ℂ 𝓢'(E, F) ∘L
    smulLeftCLM F ((𝓕 φ : 𝓢(E, ℂ)) : E → ℂ) ∘L
      FourierTransform.fourierCLM ℂ 𝓢'(E, F)

/-- The convolution theorem `𝓕(φ * T) = 𝓕φ · 𝓕T`. With the present definition this holds by
construction (it is `𝓕 ∘ 𝓕⁻¹ = id` on tempered distributions); the content is in
`convolutionSchwartzCLM_toTemperedDistributionCLM_eq`, which shows the definition matches the
integral convolution on Schwartz functions. -/
@[simp]
theorem fourier_convolutionSchwartzCLM (φ : 𝓢(E, ℂ)) (T : 𝓢'(E, F)) :
    𝓕 (convolutionSchwartzCLM φ T) =
      smulLeftCLM F ((𝓕 φ : 𝓢(E, ℂ)) : E → ℂ) (𝓕 T) := by
  simp [convolutionSchwartzCLM]

end TopologicalValueSpace

/-- Convolution of a regular tempered distribution induced by a Schwartz function agrees with
Mathlib's convolution on Schwartz space. -/
theorem convolutionSchwartzCLM_toTemperedDistributionCLM_eq (f φ : 𝓢(E, ℂ)) :
    convolutionSchwartzCLM φ
        (SchwartzMap.toTemperedDistributionCLM E ℂ MeasureTheory.volume f) =
      SchwartzMap.toTemperedDistributionCLM E ℂ MeasureTheory.volume
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f φ) := by
  apply (FourierTransform.fourierCLE ℂ 𝓢'(E, ℂ)).injective
  simp only [FourierTransform.fourierCLE_apply]
  rw [fourier_convolutionSchwartzCLM,
    fourier_toTemperedDistributionCLM_eq,
    fourier_toTemperedDistributionCLM_eq,
    SchwartzMap.fourier_convolution]
  ext ψ
  simp only [smulLeftCLM_apply_apply, SchwartzMap.coe_apply,
    SchwartzMap.pairing_apply_apply]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp [smul_eq_mul, mul_left_comm, mul_comm]

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Distributional differentiation commutes with convolution by a Schwartz function. -/
theorem lineDerivOp_convolutionSchwartzCLM (φ : 𝓢(E, ℂ)) (T : 𝓢'(E, F)) (m : E) :
    ∂_{m} (convolutionSchwartzCLM φ T) =
      convolutionSchwartzCLM φ (∂_{m} T) := by
  apply (FourierTransform.fourierCLE ℂ 𝓢'(E, F)).injective
  simp only [FourierTransform.fourierCLE_apply]
  rw [TemperedDistribution.fourier_lineDerivOp_eq
      (convolutionSchwartzCLM φ T) m,
    fourier_convolutionSchwartzCLM,
    fourier_convolutionSchwartzCLM, fourier_lineDerivOp_eq]
  rw [map_smul]
  congr 1
  rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  have hmul :
      (((𝓕 φ : 𝓢(E, ℂ)) : E → ℂ) * fun x ↦ (inner ℝ x m : ℂ)) =
        (fun x ↦ (inner ℝ x m : ℂ)) * ((𝓕 φ : 𝓢(E, ℂ)) : E → ℂ) := by
    funext x
    exact mul_comm _ _
  rw [hmul]

end TemperedDistribution
