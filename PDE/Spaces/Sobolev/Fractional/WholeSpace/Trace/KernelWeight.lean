/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.NormalFrequency
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Plancherel
public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal
import CAS.ExactTactic

/-!
# Cancellation of the trace kernel and Bessel weights

The Cauchy kernel is chosen so that its product with the ambient `H¹` weight
is the boundary `H^{1/2}` weight divided by `sqrt π`. This identity fixes the
physical normalization of the restriction and lifting operators.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SobolevSpace.Fractional.Trace

open SobolevSpace.Trace.HalfSpace

/-- The Euclidean norm separates tangential and normal coordinates quadratically. -/
theorem norm_join_sq {n : ℕ} (ξ : ℝ^n) (t : ℝ) :
    ‖joinTangentialNormal (ξ, t)‖ ^ 2 = ‖ξ‖ ^ 2 + t ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_castSucc]
  simp only [joinTangentialNormal_castSucc, joinTangentialNormal_last]

/-- Squaring the positive tangential scale gives the tangential Bessel weight base. -/
theorem tangentialScale_sq {n : ℕ} (ξ : ℝ^n) :
    (tangentialScale ξ : ℝ) ^ 2 = 1 + ‖ξ‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

/-- Cancellation of the scalar kernel against the ambient first-order weight. -/
theorem normalKernel_mul_weight {n : ℕ} (ξ : ℝ^n) (t : ℝ) :
    Real.sqrt Real.pi * normalKernel (tangentialScale ξ) t *
      Real.sqrt (1 + ‖joinTangentialNormal (ξ, t)‖ ^ 2) =
        Real.sqrt (tangentialScale ξ : ℝ) := by
  have hden : 0 < t ^ 2 + (tangentialScale ξ : ℝ) ^ 2 := by
    rw [tangentialScale_sq]
    positivity
  apply (sq_eq_sq₀ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (normalKernel_nonneg _ _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, normalKernel_sq,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (tangentialScale ξ).coe_nonneg]
  unfold cauchyPDFReal
  simp only [sub_zero]
  have hnorm : 1 + ‖joinTangentialNormal (ξ, t)‖ ^ 2 =
      t ^ 2 + (tangentialScale ξ : ℝ) ^ 2 := by
    rw [norm_join_sq, tangentialScale_sq]
    cas
  rw [hnorm]
  cas using Real.pi_ne_zero hden.ne'

/-- The half-order Bessel symbol is the square root of the tangential scale. -/
theorem besselSymbol_half_eq {n : ℕ} (ξ : ℝ^n) :
    besselSymbol n (1 / 2) ξ = (Real.sqrt (tangentialScale ξ : ℝ) : ℂ) := by
  unfold besselSymbol tangentialScale
  rw [Real.rpow_div_two_eq_sqrt _ (by positivity), ← Real.sqrt_eq_rpow]
  rfl

/-- The first-order Bessel symbol is a positive square root. -/
theorem besselSymbol_one_eq {n : ℕ} (x : ℝ^n) :
    besselSymbol n 1 x = (Real.sqrt (1 + ‖x‖ ^ 2) : ℂ) := by
  unfold besselSymbol
  rw [← Real.sqrt_eq_rpow]

/-- The normalization identity acting on a complex Fourier value. -/
theorem normalKernel_smul_besselSymbol {n : ℕ} (ξ : ℝ^n) (t : ℝ) (z : ℂ) :
    Real.sqrt Real.pi • (normalKernel (tangentialScale ξ) t •
      (besselSymbol (n + 1) 1 (joinTangentialNormal (ξ, t)) * z)) =
        besselSymbol n (1 / 2) ξ * z := by
  rw [besselSymbol_half_eq, besselSymbol_one_eq]
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    normalKernel_mul_weight]

end SobolevSpace.Fractional.Trace
