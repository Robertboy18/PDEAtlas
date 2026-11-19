/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Duality
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Cauchy

/-!
# Real tests of the physical L2 wave and forcing integral

Real Schwartz tests turn complex L2 pairings into ordinary spatial integrals.
For real forcing representatives, the physical sine propagator gives the
backward Fourier test wave. L1L2 forcing gives its time integrability and the terminal Duhamel
testing identity, with explicit AE transport.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set PDE.Common
open scoped ENNReal SchwartzMap

namespace WaveEquation.Fourier

/-- A real Schwartz test pairs with any representative of an L2 class by the
ordinary real spatial integral. -/
theorem re_inner_realSchwartz_eq_integral {n : ℕ} (φ : 𝓢(ℝ^n, ℝ))
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) {U : ℝ^n → ℂ} (hU : U =ᵐ[volume] u) :
    (inner ℂ ((φ.postcompCLM Complex.ofRealCLM).toLp 2 volume) u).re = ∫ x, φ x * (U x).re := by
  rw [L2.inner_def]
  have hi := L2.integrable_inner (𝕜 := ℂ) ((φ.postcompCLM Complex.ofRealCLM).toLp 2 volume) u
  change RCLike.re (∫ x, inner ℂ _ _) = _
  rw [← integral_re hi]
  apply integral_congr_ae
  filter_upwards [(φ.postcompCLM Complex.ofRealCLM).coeFn_toLp 2 volume, hU] with x hφ hx
  rw [hφ, ← hx]
  change (inner ℂ (φ x : ℂ) (U x)).re = _
  rw [RCLike.inner_apply', Complex.conj_ofReal, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Moving a real terminal test through the physical sine propagator gives the
backward Fourier wave. Only the forcing class needs a real representative. -/
theorem re_inner_sineEvolution_realSchwartz_eq_integral {n : ℕ}
    (φ : 𝓢(ℝ^n, ℝ)) (t : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    {r : ℝ^n → ℝ} (hr : (u : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (r x : ℂ)) :
    (inner ℂ (sineEvolution t ((φ.postcompCLM Complex.ofRealCLM).toLp 2 volume)) u).re =
      ∫ x, r x * realSolution 0 φ (timeSpaceCons t x) := by
  rw [L2.inner_def]
  have hi := L2.integrable_inner (𝕜 := ℂ)
    (sineEvolution t ((φ.postcompCLM Complex.ofRealCLM).toLp 2 volume)) u
  change RCLike.re (∫ x, inner ℂ _ _) = _
  rw [← integral_re hi]
  apply integral_congr_ae
  filter_upwards [sineEvolution_schwartz_ae (φ.postcompCLM Complex.ofRealCLM) t, hr] with x hφ hx
  rw [hφ, hx, RCLike.inner_apply']
  change Complex.re ((starRingEnd ℂ) _ * _) = _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.conj_re]
  have he : realSolution 0 φ (timeSpaceCons t x) = (waveSolution (0 : 𝓢(ℝ^n, ℂ))
        (𝓕 (φ.postcompCLM Complex.ofRealCLM) : 𝓢(ℝ^n, ℂ)) (t, x)).re := by
    simp [realSolution, cauchySolution, Function.comp_def, PDE.time]
  rw [he, mul_comm]

/-- The compact backward-wave residual pairing is integrable whenever the
real residual represents the supplied L1L2 forcing class. -/
theorem integrable_mul_backwardRealSolution {n : ℕ} (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc a b))) (φ : 𝓢(ℝ^n, ℝ))
    {r : ℝ → ℝ^n → ℝ}
    (hr : ∀ᵐ s ∂volume.restrict (Icc a b), (f s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (r s x : ℂ)) :
    Integrable (fun s ↦ ∫ x, r s x * realSolution 0 φ (timeSpaceCons (b - s) x))
      (volume.restrict (Icc a b)) := by
  have hi := integrable_re_inner_backwardSine a b b f
    ((φ.postcompCLM Complex.ofRealCLM).toLp 2 volume)
  apply hi.congr
  filter_upwards [hr, ae_restrict_mem measurableSet_Icc] with s hs hsb
  rw [max_eq_left (sub_nonneg.mpr hsb.2)]
  exact re_inner_sineEvolution_realSchwartz_eq_integral φ (b - s) (f s) hs

/-- Testing Duhamel at its upper time endpoint is integration against the backward Fourier wave. -/
theorem re_inner_duhamelL2_realSchwartz_eq_integral {n : ℕ} (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc a b))) (φ : 𝓢(ℝ^n, ℝ))
    {r : ℝ → ℝ^n → ℝ}
    (hr : ∀ᵐ s ∂volume.restrict (Icc a b), (f s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (r s x : ℂ)) :
    (inner ℂ ((φ.postcompCLM Complex.ofRealCLM).toLp 2 volume) (duhamelL2 a b b f)).re =
      ∫ s in Icc a b, ∫ x, r s x * realSolution 0 φ (timeSpaceCons (b - s) x) := by
  rw [re_inner_duhamelL2_eq_integral]
  apply integral_congr_ae
  filter_upwards [hr, ae_restrict_mem measurableSet_Icc] with s hs hsb
  rw [max_eq_left (sub_nonneg.mpr hsb.2)]
  exact re_inner_sineEvolution_realSchwartz_eq_integral φ (b - s) (f s) hs


end WaveEquation.Fourier
