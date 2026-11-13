/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Convolution of square-integrable functions

The convolution of two complex `L²` functions exists at every point and equals the inverse
Fourier integral of the product of their `L²` Fourier transforms. Hölder's inequality puts this
product in `L¹`, so the inverse integral gives a bounded continuous representative.

The identity uses Mathlib's `exp (-2π i ⟪x, ξ⟫)` normalization and has no extra constant.
The convolution need not belong to `L²`; no `L²` Fourier transform of it is asserted.
The proof extends the Schwartz identity by continuity in both `L²` inputs.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped Convolution SchwartzMap

namespace PDE.Analysis.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The product of two `L²` Fourier transforms is integrable, so its inverse Fourier
integral is defined without any further decay assumption on the original functions. -/
theorem integrable_fourier_mul_L2 (u v : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun ξ : E ↦ (𝓕 u : Lp ℂ 2 volume) ξ * (𝓕 v : Lp ℂ 2 volume) ξ) :=
  (Lp.memLp (𝓕 u)).integrable_mul (Lp.memLp (𝓕 v))

private theorem convolution_eq_lpPairing
    (u v : Lp ℂ 2 (volume : Measure E)) (x : E) :
    ((u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ)) x =
      (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2 u
        (Lp.compMeasurePreserving (fun y : E ↦ x - y)
          (volume.measurePreserving_sub_left x) v) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving v (volume.measurePreserving_sub_left x)]
    with y hy
  exact congrArg (u y * ·) hy.symm

private theorem continuous_convolution_evaluation (x : E) :
    Continuous (fun p : Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E) ↦
      ((p.1 : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (p.2 : E → ℂ)) x) := by
  simp_rw [convolution_eq_lpPairing]
  exact ((ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2).continuous₂.comp
    (continuous_fst.prodMk
      ((Lp.isometry_compMeasurePreserving (volume.measurePreserving_sub_left x)).continuous.comp
        continuous_snd))

private theorem fourierInv_mul_eq_holder
    (u v : Lp ℂ 2 (volume : Measure E)) (x : E) :
    𝓕⁻ (fun ξ : E ↦ (𝓕 u : Lp ℂ 2 volume) ξ * (𝓕 v : Lp ℂ 2 volume) ξ) x =
      Real.Lp.fourierTransformInv
        ((ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 2 1 (𝓕 u) (𝓕 v)) x := by
  rw [Real.Lp.fourierTransformInv_apply]
  exact Real.fourierInv_congr_ae
    ((ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 1) (𝓕 u) (𝓕 v)).symm x

private theorem continuous_fourierInv_mul_evaluation (x : E) :
    Continuous (fun p : Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E) ↦
      𝓕⁻ (fun ξ : E ↦ (𝓕 p.1 : Lp ℂ 2 volume) ξ * (𝓕 p.2 : Lp ℂ 2 volume) ξ) x) := by
  simp_rw [fourierInv_mul_eq_holder]
  let B : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 volume →L[ℂ] Lp ℂ 1 volume :=
    (ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 2 1
  have hfourier : Continuous (fun u : Lp ℂ 2 (volume : Measure E) ↦
      (𝓕 u : Lp ℂ 2 volume)) :=
    continuous_fourier
  have hleft :
      Continuous (fun p : Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E) ↦
        (𝓕 p.1 : Lp ℂ 2 volume)) := hfourier.comp continuous_fst
  have hright :
      Continuous (fun p : Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E) ↦
        (𝓕 p.2 : Lp ℂ 2 volume)) := hfourier.comp continuous_snd
  have hprod :
      Continuous (fun p : Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E) ↦
        B (𝓕 p.1) (𝓕 p.2)) :=
    (B.continuous.comp hleft).clm_apply hright
  have hinv : Continuous (fun w : Lp ℂ 1 (volume : Measure E) ↦
      Real.Lp.fourierTransformInv w x) :=
    (BoundedContinuousFunction.evalCLM ℂ x).continuous.comp
      (Real.Lp.fourierTransformInvCLM E ℂ).continuous
  exact hinv.comp hprod

private theorem convolution_toLp_eq_fourierInv_mul
    (f g : 𝓢(E, ℂ)) (x : E) :
    ((f.toLp 2 volume : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (g.toLp 2 volume : E → ℂ)) x =
      𝓕⁻ (fun ξ : E ↦ (𝓕 (f.toLp 2 volume) : Lp ℂ 2 volume) ξ *
        (𝓕 (g.toLp 2 volume) : Lp ℂ 2 volume) ξ) x := by
  rw [convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ)
    (f.coeFn_toLp 2 volume) (g.coeFn_toLp 2 volume)]
  have hprod :
      (fun ξ : E ↦ (𝓕 (f.toLp 2 volume) : Lp ℂ 2 volume) ξ *
        (𝓕 (g.toLp 2 volume) : Lp ℂ 2 volume) ξ) =ᵐ[volume]
        (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) : E → ℂ) := by
    simp only [SchwartzMap.toLp_fourier_eq]
    filter_upwards [(𝓕 f).coeFn_toLp 2 volume, (𝓕 g).coeFn_toLp 2 volume]
      with ξ hf hg
    simp only [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply', hf, hg]
  rw [Real.fourierInv_congr_ae hprod x, ← SchwartzMap.fourier_convolution,
    ← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]
  exact (SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) f g x).symm

/-- The convolution of arbitrary complex `L²` functions is the inverse Fourier integral
of the `L¹` product of their `L²` Fourier transforms, at every spatial point. -/
theorem convolution_eq_fourierInv_mul_L2
    (u v : Lp ℂ 2 (volume : Measure E)) :
    (u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ) =
      𝓕⁻ (fun ξ : E ↦ (𝓕 u : Lp ℂ 2 volume) ξ * (𝓕 v : Lp ℂ 2 volume) ξ) := by
  funext x
  refine DenseRange.induction_on₂
    (SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ) (p := 2)
      (μ := volume) ENNReal.ofNat_ne_top)
    (isClosed_eq (continuous_convolution_evaluation x)
      (continuous_fourierInv_mul_evaluation x)) ?_ u v
  intro f g
  exact convolution_toLp_eq_fourierInv_mul f g x

/-- The everywhere-defined convolution of two `L²` classes is continuous. -/
theorem continuous_convolution_L2
    (u v : Lp ℂ 2 (volume : Measure E)) :
    Continuous ((u : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : E → ℂ)) := by
  rw [convolution_eq_fourierInv_mul_L2]
  have heq :
      𝓕⁻ (fun ξ : E ↦ (𝓕 u : Lp ℂ 2 volume) ξ * (𝓕 v : Lp ℂ 2 volume) ξ) =
        (Real.Lp.fourierTransformInv
          ((ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 2 1 (𝓕 u) (𝓕 v)) : E → ℂ) :=
    funext (fourierInv_mul_eq_holder u v)
  rw [heq]
  exact (Real.Lp.fourierTransformInv _).continuous

end PDE.Analysis.Fourier
