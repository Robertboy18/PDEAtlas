/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.SpectralBridge
import PDE.Analysis.Calculus.Deriv.LinearMap

/-!
# Odd Fourier filters and the Hilbert transform

An odd derivative has multiplier `(2πiσ)^(2k+1)`. The Hilbert multiplier
`-i sign(σ)` turns this into the real, even multiplier
`(-1)^k (2π)^(2k+1) |σ|^(2k+1)`.

For real Schwartz data, `hilbertPV_eq_fourierInv_of_differentiableAt` identifies that
multiplier with the convergent Hilbert principal value at every point.
Thus an odd absolute frequency power can be evaluated in physical space
by differentiating and taking a principal value. This is the nonlocal
filter used in even-dimensional Radon inversion.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace SchwartzMap

private theorem hilbertSymbol_mul_odd_fourier_power (k : ℕ) (σ : ℝ) :
    PDE.Analysis.hilbertSymbol σ * (2 * Real.pi * Complex.I * σ) ^ (2 * k + 1) =
      (((-1 : ℝ) ^ k * (2 * Real.pi) ^ (2 * k + 1) *
        |σ| ^ (2 * k + 1) : ℝ) : ℂ) := by
  have hbase : (2 * Real.pi * Complex.I * σ : ℂ) ^ 2 =
      -((2 * Real.pi * σ : ℝ) : ℂ) ^ 2 := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [pow_succ, pow_mul, hbase, neg_pow, ← pow_mul]
  rcases lt_trichotomy σ 0 with hσ | rfl | hσ
  · rw [PDE.Analysis.hilbertSymbol_of_neg hσ, abs_of_neg hσ]
    push_cast
    rw [(show Odd (2 * k + 1) from ⟨k, rfl⟩).neg_pow]
    ring_nf
    simp [Complex.I_sq]
  · simp
  · rw [PDE.Analysis.hilbertSymbol_of_pos hσ, abs_of_pos hσ]
    push_cast
    ring_nf
    simp [Complex.I_sq]

/-- Every ordinary derivative of real Schwartz data has a convergent Hilbert
principal value at every evaluation point. -/
theorem hasHilbertPV_iteratedDeriv (f : 𝓢(ℝ, ℝ)) (n : ℕ) (s : ℝ) :
    PDE.Analysis.HasHilbertPV (iteratedDeriv n f) s
      (PDE.Analysis.hilbertPV (iteratedDeriv n f) s) := by
  let d : 𝓢(ℝ, ℝ) := (derivCLM ℝ ℝ : 𝓢(ℝ, ℝ) → 𝓢(ℝ, ℝ))^[n] f
  rw [← show (d : ℝ → ℝ) = iteratedDeriv n f from coe_iterate_derivCLM ℝ f n]
  exact PDE.Analysis.hasHilbertPV_of_differentiableAt d.integrable
    ((d.smooth ⊤).differentiable (by simp)).differentiableAt

/-- Inverting an odd absolute frequency power gives the Hilbert principal
value of the corresponding odd derivative, with Mathlib's Fourier normalization. -/
theorem fourierInv_odd_abs_pow_smul_fourier_real (f : 𝓢(ℝ, ℝ)) (k : ℕ) (s : ℝ) :
    𝓕⁻ (fun σ : ℝ ↦ |σ| ^ (2 * k + 1) • 𝓕 (fun y ↦ (f y : ℂ)) σ) s =
      (((-1 : ℝ) ^ k / (2 * Real.pi) ^ (2 * k + 1)) *
        PDE.Analysis.hilbertPV (iteratedDeriv (2 * k + 1) f) s : ℝ) := by
  let fc : 𝓢(ℝ, ℂ) := f.postcompCLM Complex.ofRealCLM
  let d : 𝓢(ℝ, ℝ) := (derivCLM ℝ ℝ : 𝓢(ℝ, ℝ) → 𝓢(ℝ, ℝ))^[2 * k + 1] f
  have hd : (d : ℝ → ℝ) = iteratedDeriv (2 * k + 1) f :=
    coe_iterate_derivCLM ℝ f _
  have hdc : (fun y ↦ (d y : ℂ)) = iteratedDeriv (2 * k + 1) fc := by
    funext y
    rw [hd]
    exact (Complex.ofRealCLM.iteratedDeriv_comp_left
      (f.smooth (2 * k + 1)).contDiffAt).symm
  have hF : Integrable (𝓕 (fun y ↦ (d y : ℂ))) :=
    (𝓕 (d.postcompCLM Complex.ofRealCLM)).integrable
  have hPV := PDE.Analysis.hilbertPV_eq_fourierInv_of_differentiableAt
    d.integrable hF ((d.smooth ⊤).differentiable (by simp)).differentiableAt (x := s)
  have hspec (σ : ℝ) :
      PDE.Analysis.hilbertSymbol σ * 𝓕 (fun y ↦ (d y : ℂ)) σ =
        (((-1 : ℝ) ^ k * (2 * Real.pi) ^ (2 * k + 1)) : ℝ) •
          (|σ| ^ (2 * k + 1) • 𝓕 (fun y ↦ (f y : ℂ)) σ) := by
    rw [hdc, Real.fourier_iteratedDeriv (fc.smooth ⊤)
      (fun j _ ↦ fc.integrable_iteratedDeriv j) (n := 2 * k + 1) le_top]
    dsimp only
    rw [smul_eq_mul, ← mul_assoc, hilbertSymbol_mul_odd_fourier_power]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]
    exact mul_assoc _ _ _
  simp_rw [hspec] at hPV
  have hscale (a : ℝ) (v : ℝ → ℂ) :
      𝓕⁻ (fun σ ↦ a • v σ) s = a • 𝓕⁻ v s := by
    simp only [Real.fourierInv_eq, smul_comm _ a, integral_smul]
  rw [hscale] at hPV
  have hc : (-1 : ℝ) ^ k / (2 * Real.pi) ^ (2 * k + 1) *
      ((-1 : ℝ) ^ k * (2 * Real.pi) ^ (2 * k + 1)) = 1 := by
    have hp : (2 * Real.pi) ^ (2 * k + 1) ≠ 0 :=
      pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    field_simp
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  have he := congrArg
    (fun z : ℂ ↦ ((-1 : ℝ) ^ k / (2 * Real.pi) ^ (2 * k + 1)) • z) hPV
  rw [smul_smul, hc, one_smul] at he
  rw [← hd]
  exact he.symm.trans (by simp only [Complex.real_smul, Complex.ofReal_mul])

end SchwartzMap
