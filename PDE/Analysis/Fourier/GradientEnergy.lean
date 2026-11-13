/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier representation of spatial derivative energy

Plancherel and a finite orthonormal basis identify the sum of directional
energies with the squared radial frequency weight. This also proves that
the frequency-weighted Fourier transform of Schwartz data belongs to L².
-/

@[expose] public section

open MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap

namespace SchwartzMap

variable {ι V H : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The squared Fourier derivative norm has the directional frequency weight. -/
theorem norm_fourier_lineDerivOp_sq (f : 𝓢(V, H)) (v ξ : V) :
    ‖𝓕 (∂_{v} f) ξ‖ ^ 2 =
      (2 * Real.pi) ^ 2 * ‖inner ℝ ξ v‖ ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have hg : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq]
  simp only [smul_apply, smulLeftCLM_apply_apply hg, norm_smul, norm_mul,
    Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg Real.pi_pos.le, mul_pow, mul_assoc]

/-- Plancherel identifies the sum of directional derivative energies with the
radial frequency energy, for any finite orthonormal basis. -/
theorem sum_integral_norm_sq_lineDerivOp_eq_fourier
    (b : OrthonormalBasis ι ℝ V) (f : 𝓢(V, H)) :
    (∑ i, ∫ x, ‖∂_{b i} f x‖ ^ 2) =
      ∫ ξ, (2 * Real.pi * ‖ξ‖) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have hi (i : ι) (_ : i ∈ Finset.univ) :
      Integrable (fun ξ ↦ ‖𝓕 (∂_{b i} f) ξ‖ ^ 2) :=
    ((𝓕 (∂_{b i} f)).memLp 2 volume).integrable_norm_pow (by norm_num)
  simp_rw [← integral_norm_sq_fourier (∂_{b _} f)]
  rw [← integral_finsetSum Finset.univ hi]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [norm_fourier_lineDerivOp_sq, ← Finset.sum_mul, ← Finset.mul_sum,
    b.sum_sq_norm_inner_left, mul_pow]

omit [CompleteSpace H] in
/-- Multiplication of a Schwartz Fourier transform by frequency is genuinely in L². -/
theorem memLp_frequency_smul_fourier (f : 𝓢(V, H)) :
    MemLp (fun ξ ↦ (2 * Real.pi * ‖ξ‖) • 𝓕 f ξ) 2 volume := by
  let b := stdOrthonormalBasis ℝ V
  have hi : Integrable (fun ξ ↦ ∑ i, ‖𝓕 (∂_{b i} f) ξ‖ ^ 2) :=
    integrable_finsetSum Finset.univ fun i _ ↦
      ((𝓕 (∂_{b i} f)).memLp 2 volume).integrable_norm_pow (by norm_num)
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  apply hi.congr
  filter_upwards with ξ
  simp only [norm_fourier_lineDerivOp_sq, ← Finset.sum_mul, ← Finset.mul_sum,
    b.sum_sq_norm_inner_left, norm_smul, mul_pow]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * ‖ξ‖)]
  simp only [mul_pow]

end SchwartzMap
