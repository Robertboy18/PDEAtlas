/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolynomialBump.PowerExpansion
public import PDE.Analysis.Calculus.QuadraticDecay
public import PDE.Parabolic.MaximumPrinciple.Barrier.WeightedExpansion
import CAS.ExactTactic

/-!
# Expanding subsolutions with power decay

The logarithmic damping is inversely proportional to the squared support radius.
Uniform ellipticity makes the normalized expanding bump a subsolution once its
natural-number exponent exceeds a coefficient-only bound. This gives polynomial,
rather than exponential, dependence on the initial radius.

SymLean's `cas` tactic proves the closing algebraic identities of the residual and of the
exponent bound.
-/

@[expose] public noncomputable section

namespace ParabolicMaximum

open PDE.Analysis
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Exact residual of the normalized power profile for the matrix parabolic operator. -/
theorem matrixParabolicOperator_powerExpandingPolynomialBump
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ) (z : ℝ^n)
    (r : ℝ) (p : ℕ) (x : ℝ^n) {t : ℝ}
    (ht : 0 < r ^ 2 + t) (ha : (a x t).PosSemidef) :
    matrixParabolicOperator a b c (powerExpandingPolynomialBump z r p) x t =
      (r ^ 2) ^ p / (r ^ 2 + t) ^ (p + 3) *
        ((c x t - ((p : ℝ) + 3) / (r ^ 2 + t)) *
            (r ^ 2 + t - ‖x - z‖ ^ 2)⁺ ^ 3 +
          (3 + 6 * ((a x t).trace - ⟪x - z, b x t⟫)) *
            (r ^ 2 + t - ‖x - z‖ ^ 2)⁺ ^ 2 -
          24 * (r ^ 2 + t - ‖x - z‖ ^ 2)⁺ *
            ⟪x - z, (a x t).toEuclideanLin (x - z)⟫) := by
  have hρ : HasDerivAt (fun s : ℝ ↦ r ^ 2 + s) 1 t := by cas
  unfold powerExpandingPolynomialBump
  rw [matrixParabolicOperator_weightedPolynomialBallBump a b c z x hρ
    (hasDerivAt_power_expansion_amplitude r p ht.ne') ha]
  cas

/-- A single exponent works at every positive support radius below a prescribed
upper bound. The coefficients need only pointwise ellipticity, trace and drift bounds. -/
theorem matrixParabolicOperator_powerExpandingPolynomialBump_nonpos
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (z : ℝ^n) (r : ℝ) (p : ℕ) (x : ℝ^n)
    {R A B θ t : ℝ} (hR : 0 ≤ R) (hθ : 0 < θ)
    (ht : 0 < r ^ 2 + t) (hradius : r ^ 2 + t ≤ R ^ 2)
    (hdecay : (3 + 6 * (A + R * B) + 24 * θ) ^ 2 / (4 * (24 * θ)) ≤ (p : ℝ) + 3)
    (ha : (a x t).PosSemidef)
    (hell : ∀ d : ℝ^n, θ * ‖d‖ ^ 2 ≤ ⟪d, (a x t).toEuclideanLin d⟫)
    (htrace : (a x t).trace ≤ A) (hdrift : ‖b x t‖ ≤ B) :
    matrixParabolicOperator a b (fun _ _ ↦ 0) (powerExpandingPolynomialBump z r p) x t ≤
      0 := by
  rw [matrixParabolicOperator_powerExpandingPolynomialBump a b (fun _ _ ↦ 0) z r p x ht ha]
  let h := r ^ 2 + t - ‖x - z‖ ^ 2
  change (r ^ 2) ^ p / (r ^ 2 + t) ^ (p + 3) *
    ((0 - ((p : ℝ) + 3) / (r ^ 2 + t)) * h⁺ ^ 3 +
      (3 + 6 * ((a x t).trace - ⟪x - z, b x t⟫)) * h⁺ ^ 2 -
      24 * h⁺ * ⟪x - z, (a x t).toEuclideanLin (x - z)⟫) ≤ 0
  by_cases hh : h ≤ 0
  · simp [posPart_eq_zero.mpr hh]
  have hhpos : 0 < h := lt_of_not_ge hh
  rw [posPart_eq_self.mpr hhpos.le]
  have hxR : ‖x - z‖ ≤ R := by
    apply (sq_le_sq₀ (norm_nonneg _) hR).mp
    dsimp [h] at hhpos
    linarith
  have hinner : -⟪x - z, b x t⟫ ≤ R * B :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul hxR hdrift (norm_nonneg _) hR))
  let K := 3 + 6 * (A + R * B)
  let D := 24 * θ
  have hlinear : 3 + 6 * ((a x t).trace - ⟪x - z, b x t⟫) ≤ K := by
    dsimp [K]
    linarith
  have hdecay' :
      0 + (K + D) ^ 2 / (4 * D * (Real.sqrt (r ^ 2 + t)) ^ 2) ≤
        ((p : ℝ) + 3) / (r ^ 2 + t) := by
    simpa only [K, D, zero_add, Real.sq_sqrt ht.le, div_mul_eq_div_div] using
      div_le_div_of_nonneg_right hdecay ht.le
  have hcubic := cubic_decay_nonpos (show 0 < D by dsimp [D]; positivity)
    (Real.sqrt_pos.mpr ht) hhpos.le
    (show (Real.sqrt (r ^ 2 + t)) ^ 2 ≤ h + ‖x - z‖ ^ 2 by
      rw [Real.sq_sqrt ht.le]
      dsimp [h]
      linarith) hdecay'
  have hbase :
      (0 - ((p : ℝ) + 3) / (r ^ 2 + t)) * h ^ 3 +
        (3 + 6 * ((a x t).trace - ⟪x - z, b x t⟫)) * h ^ 2 -
        24 * h * ⟪x - z, (a x t).toEuclideanLin (x - z)⟫ ≤
      (0 - ((p : ℝ) + 3) / (r ^ 2 + t)) * h ^ 3 +
        K * h ^ 2 - D * h * ‖x - z‖ ^ 2 := by
    calc
      _ ≤ (0 - ((p : ℝ) + 3) / (r ^ 2 + t)) * h ^ 3 +
          K * h ^ 2 - 24 * h * (θ * ‖x - z‖ ^ 2) :=
        sub_le_sub
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right hlinear (sq_nonneg h)))
          (mul_le_mul_of_nonneg_left (hell (x - z)) (by positivity))
      _ = _ := by dsimp [D]; cas
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hbase.trans hcubic)

end ParabolicMaximum
