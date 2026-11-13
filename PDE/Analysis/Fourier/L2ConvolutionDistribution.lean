/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.L1Reconstruction
public import PDE.Analysis.Fourier.L2Convolution

/-!
# The Fourier convolution identity for arbitrary L² inputs

The actual convolution of two complex `L²` functions is bounded and continuous,
so it defines a tempered distribution through its `L∞` class. Its distributional
Fourier transform is the `L¹` product of the two `L²` Fourier transforms.

The proof identifies the convolution with the inverse integral of this product
and uses its pairing with Schwartz tests. The convolution need not belong to `L²`.
The normalization is Mathlib's `exp (-2π i ⟪x, ξ⟫)`, with no additional constant.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped Convolution SchwartzMap

namespace PDE.Analysis.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The convolution of two `L²` functions belongs to `L∞`: it is the bounded
continuous inverse Fourier integral of an integrable product. -/
theorem memLp_convolution_top_L2 (u v : Lp ℂ 2 (volume : Measure E)) :
    MemLp ((u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ)) ⊤ volume := by
  rw [convolution_eq_fourierInv_mul_L2,
    ← Real.Lp.fourierTransformInv_toLp
      (memLp_one_iff_integrable.mpr (integrable_fourier_mul_L2 u v))]
  exact (Real.Lp.fourierTransformInv _).memLp_top

/-- The tempered distribution of the actual convolution is the inverse Fourier
transform of the `L¹` Hölder product of the two Fourier transforms. -/
theorem convolution_toTemperedDistribution_eq_fourierInv_mul_L2
    (u v : Lp ℂ 2 (volume : Measure E)) :
    ((memLp_convolution_top_L2 u v).toLp _ : 𝓢'(E, ℂ)) =
      𝓕⁻ ((ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 2 1 (𝓕 u) (𝓕 v) : 𝓢'(E, ℂ)) := by
  apply DFunLike.ext
  intro φ
  rw [Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x, φ x •
        𝓕⁻ (fun ξ : E ↦ (𝓕 u : Lp ℂ 2 volume) ξ * (𝓕 v : Lp ℂ 2 volume) ξ) x := by
      apply integral_congr_ae
      filter_upwards [(memLp_convolution_top_L2 u v).coeFn_toLp] with x hx
      rw [hx, convolution_eq_fourierInv_mul_L2]
    _ = ∫ x, φ x • 𝓕⁻
        ((ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 2 1 (𝓕 u) (𝓕 v) : E → ℂ) x := by
      apply integral_congr_ae
      filter_upwards with x
      exact congrArg (fun z : ℂ ↦ φ x • z) <| Real.fourierInv_congr_ae
        ((ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 1) (𝓕 u) (𝓕 v)).symm x
    _ = _ := integral_smul_fourierInv_eq _ φ

/-- The forward Fourier convolution identity holds as tempered distributions for
all `L²` inputs. The actual convolution is represented in `L∞`, and its Fourier
transform is the `L¹` product; neither convolution nor product is assumed to
belong to `L²`. -/
theorem fourier_convolution_toTemperedDistribution_L2
    (u v : Lp ℂ 2 (volume : Measure E)) :
    𝓕 ((memLp_convolution_top_L2 u v).toLp _ : 𝓢'(E, ℂ)) =
      ((ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 2 1 (𝓕 u) (𝓕 v) : 𝓢'(E, ℂ)) := by
  rw [convolution_toTemperedDistribution_eq_fourierInv_mul_L2, fourier_fourierInv_eq]

end PDE.Analysis.Fourier
