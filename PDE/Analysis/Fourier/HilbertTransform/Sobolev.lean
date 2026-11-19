/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Sobolev
public import PDE.Analysis.Fourier.HilbertTransform
public import PDE.DistributionTheory.TemperedDistribution.Fourier.Derivatives

/-!
# Weak derivatives of the spectral Hilbert transform

The Fourier derivative domain is exactly the set of complex `L²` classes whose
distributional derivative has an `L²` representative, so the multiplier derivative
is a weak derivative. The Hilbert transform then
commutes with weak differentiation without pointwise regularity assumptions.
-/

@[expose] public section

namespace PDE.Analysis

open FourierTransform MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv

noncomputable section

/-- Fourier transformation of the real-line distributional derivative uses the
same symbol as the existing partial `L²` derivative operator. -/
theorem fourier_lineDeriv_one (T : 𝓢'(ℝ, ℂ)) :
    𝓕 (∂_{(1 : ℝ)} T) =
      smulLeftCLM ℂ Fourier.fourierDerivativeSymbol1D (𝓕 T) := by
  have hs : Fourier.fourierDerivativeSymbol1D =
      fun ξ : ℝ ↦ (2 * Real.pi * Complex.I) * (ξ : ℂ) := by
    funext ξ
    rfl
  rw [hs]
  simpa using
    fourier_iteratedLineDerivOp_eq (fun _ : Fin 1 ↦ (1 : ℝ)) T

/-- A distributional derivative between two `L²` classes is equivalent to the
almost-everywhere Fourier multiplier identity. -/
theorem lineDeriv_eq_iff_fourier (f g : ComplexL2) :
    ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ↔
      (fun ξ ↦ Fourier.fourierDerivativeSymbol1D ξ * (𝓕 f : ComplexL2) ξ) =ᵐ[volume]
        (𝓕 g : ComplexL2) := by
  simpa [Fourier.fourierDerivativeSymbol1D, smul_eq_mul] using
    iteratedLineDerivOp_eq_iff_fourier (fun _ : Fin 1 ↦ (1 : ℝ)) f g

/-- The existing Fourier derivative is the distributional derivative of its
input, as an equality of tempered distributions. -/
theorem lineDeriv_eq_fourierDerivativeOnDomain (f : fourierDerivativeDomain) :
    ∂_{(1 : ℝ)} ((f : ComplexL2) : 𝓢'(ℝ, ℂ)) =
      (fourierDerivativeOnDomain f : 𝓢'(ℝ, ℂ)) := by
  apply (lineDeriv_eq_iff_fourier _ _).mpr
  rw [fourier_fourierDerivativeOnDomain]
  exact (mem_fourierDerivativeDomain_iff.mp f.property).coeFn_toLp.symm

/-- The Fourier derivative domain is exactly weak `H¹`: the input and its
distributional derivative both have `L²` representatives. -/
theorem mem_fourierDerivativeDomain_iff_exists_lineDeriv (f : ComplexL2) :
    f ∈ fourierDerivativeDomain ↔
      ∃ g : ComplexL2, ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) := by
  constructor
  · intro hf
    exact ⟨fourierDerivativeOnDomain ⟨f, hf⟩,
      lineDeriv_eq_fourierDerivativeOnDomain ⟨f, hf⟩⟩
  · rintro ⟨g, hg⟩
    exact (memLp_congr_ae ((lineDeriv_eq_iff_fourier f g).mp hg)).mpr
      (Lp.memLp (𝓕 g : ComplexL2))

/-- The Hilbert transform preserves weak derivatives and their `L²` membership.
Only the input derivative identity is assumed. -/
theorem lineDeriv_hilbertTransform {f g : ComplexL2}
    (hg : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ))) :
    ∂_{(1 : ℝ)} (hilbertTransform f : 𝓢'(ℝ, ℂ)) =
      (hilbertTransform g : 𝓢'(ℝ, ℂ)) := by
  have hf := (mem_fourierDerivativeDomain_iff_exists_lineDeriv f).mpr ⟨g, hg⟩
  have hderiv : fourierDerivativeOnDomain ⟨f, hf⟩ = g := by
    apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
    exact (lineDeriv_eq_fourierDerivativeOnDomain ⟨f, hf⟩).symm.trans hg
  have h := lineDeriv_eq_fourierDerivativeOnDomain
    (hilbertTransformOnFourierDerivativeDomain ⟨f, hf⟩)
  rwa [coe_hilbertTransformOnFourierDerivativeDomain,
    fourierDerivative_hilbertTransform, hderiv] at h

/-- For an `L²` class, Mathlib's distributional Sobolev condition is precisely
square integrability of its Bessel-weighted Fourier representative. -/
theorem memSobolev_iff_memLp_fourier_weight (s : ℝ) (f : ComplexL2) :
    MemSobolev s 2 (f : 𝓢'(ℝ, ℂ)) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) *
        (𝓕 f : ComplexL2) ξ) 2 volume := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier, Lp.fourier_toTemperedDistribution_eq]
  have hweight : (fun ξ : ℝ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth :=
    by fun_prop
  constructor
  · rintro ⟨g, hg⟩
    exact (memLp_congr_ae (Lp.smulLeft_toTemperedDistribution_eq_iff hweight |>.mp hg)).mpr
      (Lp.memLp g)
  · intro hf
    exact ⟨hf.toLp _, (Lp.smulLeft_toTemperedDistribution_eq_iff hweight).mpr
      hf.coeFn_toLp.symm⟩

/-- The concrete spectral Hilbert transform preserves every `L²` Sobolev order.
The discontinuous Hilbert symbol is used only as an `L²` multiplier. -/
theorem memSobolev_hilbertTransform {s : ℝ} {f : ComplexL2}
    (hf : MemSobolev s 2 (f : 𝓢'(ℝ, ℂ))) :
    MemSobolev s 2 (hilbertTransform f : 𝓢'(ℝ, ℂ)) := by
  rw [memSobolev_iff_memLp_fourier_weight] at hf ⊢
  have hm : MemLp (fun ξ ↦ hilbertSymbol ξ *
      ((((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 f : ComplexL2) ξ)) 2 volume := by
    apply hf.of_le_mul (c := 1)
    · exact measurable_hilbertSymbol.aestronglyMeasurable.mul hf.aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_hilbertSymbol_le_one ξ)
  apply (memLp_congr_ae ?_).mpr hm
  filter_upwards [coe_hilbertMultiplier (𝓕 f)] with ξ hξ
  rw [fourier_hilbertTransform, hξ]
  exact mul_left_comm _ _ _

/-- An `H¹` input has an `L²` weak derivative, and the Hilbert transform of that
same derivative is the weak derivative of its Hilbert transform. -/
theorem exists_lineDeriv_hilbertTransform_of_memSobolev {f : ComplexL2}
    (hf : MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ))) :
    ∃ g : ComplexL2,
      ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧
      ∂_{(1 : ℝ)} (hilbertTransform f : 𝓢'(ℝ, ℂ)) =
        (hilbertTransform g : 𝓢'(ℝ, ℂ)) := by
  have hd : MemSobolev 0 2 (∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ))) := by
    simpa using hf.lineDerivOp (m := (1 : ℝ))
  obtain ⟨g, hg⟩ := memSobolev_zero_iff.mp hd
  exact ⟨g, hg, lineDeriv_hilbertTransform hg⟩

end

end PDE.Analysis
