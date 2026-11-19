/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolynomialBump.WeightedExpansion
public import PDE.Parabolic.MaximumPrinciple.MatrixOperator
import PDE.Elliptic.Classical.MaximumPrinciple.MatrixStrong
import CAS.ExactTactic

/-!
# Parabolic residual of a weighted expanding ball profile

The squared radius and amplitude may be arbitrary differentiable scalar
functions. The spatial derivatives reuse the stationary polynomial bump.
Pointwise matrix factorization gives the exact residual, including
the moving support sphere and a signed potential.

SymLean's `cas` tactic proves the closing algebraic identity of the residual.
-/

@[expose] public noncomputable section

namespace ParabolicMaximum

open PDE.Analysis EllipticMaximum
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The parabolic residual of a cubic ball profile with variable
amplitude and squared radius. Only the two scalar time derivatives are needed. -/
theorem matrixParabolicOperator_weightedPolynomialBallBump
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ) (z : ℝ^n)
    {ρ w : ℝ → ℝ} {ρ' w' t : ℝ} (x : ℝ^n)
    (hρ : HasDerivAt ρ ρ' t) (hw : HasDerivAt w w' t) (ha : (a x t).PosSemidef) :
    matrixParabolicOperator a b c (fun y s ↦ w s * (ρ s - ‖y - z‖ ^ 2)⁺ ^ 3) x t =
      (w' + c x t * w t) * (ρ t - ‖x - z‖ ^ 2)⁺ ^ 3 +
        w t * (3 * ρ' + 6 * ((a x t).trace - ⟪x - z, b x t⟫)) *
          (ρ t - ‖x - z‖ ^ 2)⁺ ^ 2 -
        24 * w t * (ρ t - ‖x - z‖ ^ 2)⁺ *
          ⟪x - z, (a x t).toEuclideanLin (x - z)⟫ := by
  rcases lt_or_ge (ρ t) 0 with hneg | hradius
  · have hzero (y : ℝ^n) : (ρ t - ‖y - z‖ ^ 2)⁺ = 0 :=
      posPart_eq_zero.mpr (by nlinarith [sq_nonneg ‖y - z‖])
    have hslice : (fun y ↦ w t * (ρ t - ‖y - z‖ ^ 2)⁺ ^ 3) = fun _ ↦ 0 := by
      funext y
      simp [hzero y]
    simp only [matrixParabolicOperator]
    rw [(hasDerivAt_weightedPolynomialBallBump z x hρ hw).deriv, hslice, matrixOperator_const]
    simp [hzero x]
  obtain ⟨σ, hσ⟩ := exists_factors_of_posSemidef ha
  let H := (ρ t - ‖x - z‖ ^ 2)⁺
  have hspace : ContDiffAt ℝ 2 (fun y ↦ w t * (ρ t - ‖y - z‖ ^ 2)⁺ ^ 3) x := by
    rw [weightedPolynomialBallBump_eq_ballBump z hradius]
    exact (contDiff_const.mul (contDiff_polynomialBallBump _ _)).contDiffAt
  have hsum :
      ∑ k, secondDirectionalDerivative (fun y ↦ w t * (ρ t - ‖y - z‖ ^ 2)⁺ ^ 3)
          x (σ k) =
        w t * (24 * H * ⟪x - z, (a x t).toEuclideanLin (x - z)⟫ -
          6 * H ^ 2 * (a x t).trace) := by
    rw [weightedPolynomialBallBump_eq_ballBump z hradius]
    simp only [secondDirectionalDerivative_const_mul,
      secondDirectionalDerivative_polynomialBallBump, Real.sq_sqrt hradius]
    change (∑ k, w t * (24 * H * ⟪x - z, σ k⟫ ^ 2 -
      6 * H ^ 2 * ‖σ k‖ ^ 2)) = _
    simp only [mul_sub, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [sum_inner_sq_eq_matrix_quadratic (a x t) σ hσ,
      sum_norm_sq_eq_matrix_trace (a x t) σ hσ, ← inner_toEuclideanLin_self]
    simp only [Matrix.trace, Matrix.diag_apply]
  have hfirst :
      fderiv ℝ (fun y ↦ w t * (ρ t - ‖y - z‖ ^ 2)⁺ ^ 3) x (b x t) =
        w t * (-6 * H ^ 2 * ⟪x - z, b x t⟫) := by
    rw [weightedPolynomialBallBump_eq_ballBump z hradius,
      fderiv_const_mul ((contDiff_polynomialBallBump _ _).differentiable (by norm_num) x),
      smul_apply, smul_eq_mul, fderiv_polynomialBallBump_apply, Real.sq_sqrt hradius]
  rw [matrixParabolicOperator_eq_factored a (fun _ _ ↦ σ) b c hspace hσ,
    factoredParabolicOperatorWithPotential, factoredParabolicOperator,
    factoredEllipticOperator, (hasDerivAt_weightedPolynomialBallBump z x hρ hw).deriv,
    hsum, hfirst]
  dsimp [H]
  cas

end ParabolicMaximum
