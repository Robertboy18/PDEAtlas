/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Polynomial Fourier filters and ordinary derivatives

Iterating the Schwartz derivative gives the ordinary iterated derivative,
with rapid decay still available at every order. Mathlib's Fourier derivative
theorem therefore applies without separate integrability assumptions.

Conversely, multiplying the Fourier transform by a power of the frequency and
inverting gives the corresponding derivative. For an even power, the multiplier
is real: the sign alternates because each pair of derivatives contributes `i²`.
This form supplies the local filter in odd-dimensional Radon inversion.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coercion identifies iterates of the bundled Schwartz derivative with
ordinary iterated derivatives. -/
theorem coe_iterate_derivCLM (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F]
    (f : 𝓢(ℝ, F)) (n : ℕ) :
    ⇑((derivCLM 𝕜 F : 𝓢(ℝ, F) → 𝓢(ℝ, F))^[n] f) = iteratedDeriv n f := by
  rw [iteratedDeriv_eq_iterate]
  exact (show Function.Semiconj (fun g : 𝓢(ℝ, F) ↦ (g : ℝ → F))
    (derivCLM 𝕜 F) deriv from fun _ ↦ rfl).iterate_right n f

/-- Every ordinary iterated derivative of a Schwartz function is integrable. -/
theorem integrable_iteratedDeriv (f : 𝓢(ℝ, F)) (n : ℕ) :
    Integrable (iteratedDeriv n f) := by
  rw [← coe_iterate_derivCLM ℝ f n]
  exact ((derivCLM ℝ F : 𝓢(ℝ, F) → 𝓢(ℝ, F))^[n] f).integrable

section Complex

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Inverting a polynomially weighted Fourier transform recovers the ordinary
derivative, with the constant determined by the `exp(-2πixξ)` convention. -/
theorem fourierInv_pow_smul_fourier (f : 𝓢(ℝ, G)) (n : ℕ) (s : ℝ) :
    𝓕⁻ (fun σ : ℝ ↦ σ ^ n • 𝓕 (f : ℝ → G) σ) s =
      ((2 * Real.pi * Complex.I) ^ n)⁻¹ • iteratedDeriv n f s := by
  have hF := Real.fourier_iteratedDeriv (f.smooth ⊤)
    (fun k _ ↦ f.integrable_iteratedDeriv k) (n := n) le_top
  have hc : (2 * Real.pi * Complex.I : ℂ) ^ n ≠ 0 := by
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  let g := (derivCLM ℂ G : 𝓢(ℝ, G) → 𝓢(ℝ, G))^[n] f
  have hg : (g : ℝ → G) = iteratedDeriv n f := coe_iterate_derivCLM ℂ f n
  have he : (fun σ : ℝ ↦ σ ^ n • 𝓕 (f : ℝ → G) σ) =
      (𝓕 (((2 * Real.pi * Complex.I) ^ n)⁻¹ • g) : 𝓢(ℝ, G)) := by
    rw [fourier_smul]
    funext σ
    change σ ^ n • 𝓕 (f : ℝ → G) σ =
      ((2 * Real.pi * Complex.I) ^ n)⁻¹ • 𝓕 (g : ℝ → G) σ
    rw [hg, hF]
    dsimp only
    rw [mul_pow (2 * Real.pi * Complex.I), mul_smul, smul_smul,
      inv_mul_cancel₀ hc, one_smul, ← Complex.ofReal_pow]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  rw [he, ← fourierInv_coe, fourierInv_fourier_eq, smul_apply]
  exact congrArg (((2 * Real.pi * Complex.I) ^ n)⁻¹ • ·) (congrFun hg s)

private theorem inverse_fourier_even_constant (k : ℕ) :
    (((2 * Real.pi * Complex.I) ^ (2 * k))⁻¹ : ℂ) =
      (((-1 : ℝ) ^ k / (2 * Real.pi) ^ (2 * k) : ℝ) : ℂ) := by
  have hbase : (2 * Real.pi * Complex.I : ℂ) ^ 2 =
      ((-((2 * Real.pi) ^ 2) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [pow_mul, hbase, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  congr 1
  rw [neg_pow, mul_inv, ← inv_pow (-1 : ℝ), inv_neg, inv_one,
    ← pow_mul, div_eq_mul_inv, mul_comm]

/-- An even Fourier power is a real multiple of an even ordinary derivative. -/
theorem fourierInv_even_pow_smul_fourier (f : 𝓢(ℝ, G)) (k : ℕ) (s : ℝ) :
    𝓕⁻ (fun σ : ℝ ↦ σ ^ (2 * k) • 𝓕 (f : ℝ → G) σ) s =
      ((-1 : ℝ) ^ k / (2 * Real.pi) ^ (2 * k)) • iteratedDeriv (2 * k) f s := by
  rw [fourierInv_pow_smul_fourier, inverse_fourier_even_constant]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

end Complex

end SchwartzMap
