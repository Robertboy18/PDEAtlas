/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Fourier.Convolution
public import PDE.Analysis.Fourier.L2Reconstruction

/-!
# `L²` functions with an integrable Fourier transform

Let `f ∈ L²` have an integrable Fourier transform `f̂`. Then `f` is bounded by `‖f̂‖₁` almost
everywhere. If `g` is a second such function and `h = B(f, g)` is in `L²` for a bounded bilinear
map `B`, then the transform of `h` is the convolution `f̂ ⋆[B] ĝ`. The product estimates in
Sobolev norms on the Fourier side start from these two facts. The functions take values in
complex Hilbert spaces over a finite-dimensional real inner product space. Two `L²` functions
whose transforms are not integrable are not treated: there the product is only integrable, and
its transform is the convolution as a bounded continuous function.

## Main results

* `ae_norm_le_integral_norm_fourier`: `‖u x‖ ≤ ∫ ‖û‖` for almost every `x`.
* `fourierInv_bilin_convolution_eq`: for integrable `k₁` and `k₂`, the inverse Fourier integral of
  `k₁ ⋆[B] k₂` is `B` applied to the two inverse integrals, at every point.
* `fourier_ae_eq_convolution`: if `h = B(f, g)` almost everywhere, then `ĥ = f̂ ⋆[B] ĝ` almost
  everywhere.
* `enorm_fourier_le_lintegral_of_ae_eq_mul`: for scalar functions with `h = f g`,
  `|ĥ(ξ)| ≤ ∫ |f̂(ξ - η)| |ĝ(η)| dη` for almost every `ξ`.

## How it works

A function in `L²` with an integrable transform is almost everywhere the inverse Fourier integral
of its transform (`fourierInvIntegral_eq_L2_ae`), so it is bounded by `‖û‖₁`. The inverse
integral of `f̂ ⋆[B] ĝ` is `B` applied to the two inverse integrals at every point: the inverse
integral at `x` is the forward integral at `-x`, and for the forward integral this is Mathlib's
`Real.fourier_bilin_convolution_eq`, a consequence of Fubini's theorem. So the integrable
function `f̂ ⋆[B] ĝ` has the inverse integral `B(f, g) = h`, and since `h` is in
`L²`, it is the transform of `h` (`fourier_eq_of_fourierInvIntegral_eq_ae`). The convolution is
not assumed to be square integrable: that is part of the conclusion.
`convolution_eq_fourierInv_mul_L2` is the dual statement, for the convolution of two `L²`
functions.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  for the Fourier inversion theorem and the Fourier transform of a convolution.
  <https://www.wiley.com/en-us/Real+Analysis%3A+Modern+Techniques+and+Their+Applications%2C+2nd+Edition-p-9780471317166>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped Convolution ENNReal

namespace PDE.Analysis.Fourier

variable {E F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
  [NormedAddCommGroup F₃] [InnerProductSpace ℂ F₃] [CompleteSpace F₃]

/-- **A function in `L²` with an integrable transform is bounded by the `L¹` norm of the
transform**, almost everywhere: it is the inverse Fourier integral of its transform. -/
theorem ae_norm_le_integral_norm_fourier (u : Lp F₁ 2 (volume : Measure E))
    (hu : Integrable (𝓕 u : Lp F₁ 2 (volume : Measure E))) :
    ∀ᵐ x, ‖u x‖ ≤ ∫ ξ, ‖(𝓕 u : Lp F₁ 2 (volume : Measure E)) ξ‖ := by
  have hrec := fourierInvIntegral_eq_L2_ae hu (𝓕 u) (ae_eq_refl _)
  rw [fourierInv_fourier_eq] at hrec
  filter_upwards [hrec] with x hx
  rw [← hx, Real.fourierInv_eq_fourier_neg]
  exact Real.norm_fourier_le_integral_norm _ _

/-- **The inverse Fourier integral of a convolution** is the bilinear map applied to the two
inverse integrals, at every point. -/
theorem fourierInv_bilin_convolution_eq (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) {k₁ : E → F₁} {k₂ : E → F₂}
    (h₁ : Integrable k₁) (h₂ : Integrable k₂) (x : E) :
    𝓕⁻ (k₁ ⋆[B] k₂) x = B (𝓕⁻ k₁ x) (𝓕⁻ k₂ x) := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_bilin_convolution_eq B h₁ h₂,
    ← Real.fourierInv_eq_fourier_neg, ← Real.fourierInv_eq_fourier_neg]

/-- **The transform of a product is the convolution of the transforms.** Let `f`, `g`, `h` be
in `L²`, with `h = B(f, g)` almost everywhere for a bounded bilinear map `B`, and let the
transforms of `f` and `g` be integrable. Then `ĥ = f̂ ⋆[B] ĝ` almost everywhere. -/
theorem fourier_ae_eq_convolution (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)
    (f : Lp F₁ 2 (volume : Measure E)) (g : Lp F₂ 2 (volume : Measure E))
    (h : Lp F₃ 2 (volume : Measure E))
    (hf : Integrable (𝓕 f : Lp F₁ 2 (volume : Measure E)))
    (hg : Integrable (𝓕 g : Lp F₂ 2 (volume : Measure E)))
    (hh : (h : E → F₃) =ᵐ[volume] fun x ↦ B (f x) (g x)) :
    ((𝓕 h : Lp F₃ 2 (volume : Measure E)) : E → F₃) =ᵐ[volume]
      ((𝓕 f : Lp F₁ 2 (volume : Measure E)) : E → F₁) ⋆[B]
        ((𝓕 g : Lp F₂ 2 (volume : Measure E)) : E → F₂) := by
  -- `f` and `g` are the inverse integrals of their transforms
  have hf' := fourierInvIntegral_eq_L2_ae hf (𝓕 f) (ae_eq_refl _)
  have hg' := fourierInvIntegral_eq_L2_ae hg (𝓕 g) (ae_eq_refl _)
  rw [fourierInv_fourier_eq] at hf' hg'
  -- so the inverse integral of the convolution is `h`
  refine fourier_eq_of_fourierInvIntegral_eq_ae (hf.integrable_convolution B hg) h ?_
  filter_upwards [hf', hg', hh] with x h1 h2 h3
  rw [fourierInv_bilin_convolution_eq B hf hg, h1, h2, h3]

/-- **The transform of a product of scalar functions is dominated by the convolution of the
moduli.** If `f`, `g`, `h` are in `L²(E; ℂ)` with `h = f g` almost everywhere and `f̂`, `ĝ` are
integrable, then `|ĥ(ξ)| ≤ ∫ |f̂(ξ - η)| |ĝ(η)| dη` for almost every `ξ`. -/
theorem enorm_fourier_le_lintegral_of_ae_eq_mul
    (f g h : Lp ℂ 2 (volume : Measure E))
    (hf : Integrable (𝓕 f : Lp ℂ 2 (volume : Measure E)))
    (hg : Integrable (𝓕 g : Lp ℂ 2 (volume : Measure E)))
    (hh : (h : E → ℂ) =ᵐ[volume] fun x ↦ f x * g x) :
    ∀ᵐ ξ : E, ‖(𝓕 h : Lp ℂ 2 (volume : Measure E)) ξ‖ₑ ≤
      ∫⁻ η, ‖(𝓕 f : Lp ℂ 2 (volume : Measure E)) (ξ - η)‖ₑ *
        ‖(𝓕 g : Lp ℂ 2 (volume : Measure E)) η‖ₑ := by
  filter_upwards [fourier_ae_eq_convolution (ContinuousLinearMap.mul ℂ ℂ) f g h hf hg hh]
    with ξ hξ
  rw [hξ, convolution_mul_swap]
  exact (eNorm_integral_le_lintegral_eNorm _).trans_eq
    (lintegral_congr fun η ↦ eNorm_mul _ _)

end PDE.Analysis.Fourier
