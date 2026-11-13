/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.LpSpace
public import PDE.Analysis.Fourier.L1Reconstruction
public import PDE.DistributionTheory.TemperedDistribution.Representative.Uniqueness

/-!
# Fourier integrals and their square-integrable representatives

On the intersection of `L¹` and `L²`, the Fourier integral represents the `L²`
Fourier transform. Schwartz-test pairings identify both transforms with the same
tempered distribution. The argument applies to a finite-dimensional real
inner-product domain and a complete complex Hilbert value space.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace PDE.Analysis.Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The Fourier integral of an integrable representative agrees almost everywhere
with the Hilbert-space Fourier transform of its `L²` class. -/
theorem fourierIntegral_eq_L2_ae {g : E → F} (hg : Integrable g)
    (G : Lp F 2 (volume : Measure E)) (hG : g =ᵐ[volume] G) :
    𝓕 g =ᵐ[volume] (𝓕 G : Lp F 2 (volume : Measure E)) := by
  have hc : Continuous (𝓕 g) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hg)]
    exact (Real.Lp.fourierTransform _).continuous
  apply ae_eq_of_integral_schwartz_smul_eq hc.locallyIntegrable
    ((Lp.memLp (𝓕 G)).locallyIntegrable (by norm_num))
  intro φ
  have hflip : (innerₗ E).flip = innerₗ E := by
    ext x y
    exact real_inner_comm x y
  have hpair := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (L := innerₗ E) Real.continuous_fourierChar continuous_inner φ.integrable hg
  rw [hflip] at hpair
  have hdist := congrArg (fun T : 𝓢'(E, F) ↦ T φ)
    (Lp.fourier_toTemperedDistribution_eq G)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hdist
  calc
    _ = ∫ x, 𝓕 (φ : E → ℂ) x • g x := hpair.symm
    _ = ∫ x, 𝓕 φ x • G x := by
      apply integral_congr_ae
      filter_upwards [hG] with x hx
      rw [hx, SchwartzMap.fourier_coe]
    _ = _ := hdist

/-- The inverse Fourier integral of an integrable representative agrees almost
everywhere with the inverse Hilbert-space Fourier transform of its `L²` class. -/
theorem fourierInvIntegral_eq_L2_ae {g : E → F} (hg : Integrable g)
    (G : Lp F 2 (volume : Measure E)) (hG : g =ᵐ[volume] G) :
    𝓕⁻ g =ᵐ[volume] (𝓕⁻ G : Lp F 2 (volume : Measure E)) := by
  have h₁ : MemLp g 1 volume := memLp_one_iff_integrable.mpr hg
  have hc : Continuous (𝓕⁻ g) := by
    rw [← Real.Lp.fourierTransformInv_toLp h₁]
    exact (Real.Lp.fourierTransformInv _).continuous
  apply ae_eq_of_integral_schwartz_smul_eq hc.locallyIntegrable
    ((Lp.memLp (𝓕⁻ G)).locallyIntegrable (by norm_num))
  intro φ
  have hdist := congrArg (fun T : 𝓢'(E, F) ↦ T φ)
    (Lp.fourierInv_toTemperedDistribution_eq G)
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at hdist
  calc
    _ = ∫ x, φ x • 𝓕⁻ (h₁.toLp g : E → F) x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.fourierInv_congr_ae h₁.coeFn_toLp x]
    _ = ∫ x, 𝓕⁻ φ x • h₁.toLp g x := by
      rw [integral_smul_fourierInv_eq, TemperedDistribution.fourierInv_apply,
        Lp.toTemperedDistribution_apply]
    _ = ∫ x, 𝓕⁻ φ x • G x := by
      apply integral_congr_ae
      filter_upwards [h₁.coeFn_toLp.trans hG] with x hx
      rw [hx]
    _ = _ := hdist

end PDE.Analysis.Fourier
