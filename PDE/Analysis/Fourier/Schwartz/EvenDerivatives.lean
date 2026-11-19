/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Schwartz.Derivatives

/-!
# Fourier transforms of even derivatives

For the Fourier convention `exp(-2πixξ)`, each pair of derivatives contributes
`-(2πξ)²`. Thus the multiplier for an even derivative is real, even when the
function takes values in a complex normed space. This form lets the same filter
act on both initial data in a wave equation.
-/

@[expose] public noncomputable section

open FourierTransform
open scoped SchwartzMap

namespace SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Fourier transform of an even derivative is the corresponding real
polynomial multiplier times the Fourier transform. -/
theorem fourier_iteratedDeriv_even (f : 𝓢(ℝ, F)) (k : ℕ) (σ : ℝ) :
    𝓕 (iteratedDeriv (2 * k) f) σ =
      ((-1 : ℝ) ^ k * (2 * Real.pi) ^ (2 * k) * σ ^ (2 * k)) •
        𝓕 (f : ℝ → F) σ := by
  rw [Real.fourier_iteratedDeriv (f.smooth ⊤)
    (fun j _ ↦ f.integrable_iteratedDeriv j) (n := 2 * k) le_top]
  dsimp only
  have hbase : (2 * Real.pi * Complex.I * σ : ℂ) ^ 2 =
      ((-((2 * Real.pi * σ) ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hc : (2 * Real.pi * Complex.I * σ : ℂ) ^ (2 * k) =
      (((-1 : ℝ) ^ k * (2 * Real.pi) ^ (2 * k) * σ ^ (2 * k) : ℝ) : ℂ) := by
    rw [pow_mul, hbase, ← Complex.ofReal_pow]
    congr 1
    rw [neg_pow, ← pow_mul, mul_pow, mul_assoc]
  rw [hc]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

end SchwartzMap
