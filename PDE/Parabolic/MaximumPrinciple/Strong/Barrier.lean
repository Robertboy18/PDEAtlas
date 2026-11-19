/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.MovingPolynomialBump
public import PDE.Analysis.Calculus.QuadraticDecay
public import PDE.Analysis.LinearAlgebra.Ellipticity
public import PDE.Parabolic.MaximumPrinciple.MatrixOperator
import PDE.Elliptic.Classical.MaximumPrinciple.MatrixStrong
import CAS.ExactTactic

/-!
# Moving polynomial subsolutions

Uniform ellipticity and upper bounds on the trace, drift, and potential
determine an exponential decay for which a moving cubic ball bump is a
subsolution. Its global `C²` regularity handles the moving sphere directly.
All coefficient assumptions concern values, not derivatives.

SymLean's `cas` tactic proves the closing algebraic identities of the residual computation
and of the decay bound.
-/

@[expose] public section

noncomputable section

namespace ParabolicMaximum

open PDE.Analysis EllipticMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The exact moving-bump residual, valid on the sphere as well as off it. -/
theorem matrixParabolicOperator_movingPolynomialBump
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (z v : ℝ^n) (R ε δ s : ℝ) {x : ℝ^n} {t : ℝ}
    (ha : (a x t).PosSemidef) :
    matrixParabolicOperator a b c (movingPolynomialBump z v R ε δ s) x t =
      ε * Real.exp (-δ * (t - s)) *
        ((c x t - δ) * (R ^ 2 - ‖x - (z + (t - s) • v)‖ ^ 2)⁺ ^ 3 +
          6 * (R ^ 2 - ‖x - (z + (t - s) • v)‖ ^ 2)⁺ ^ 2 *
            (⟪x - (z + (t - s) • v), v⟫ + (a x t).trace -
              ⟪x - (z + (t - s) • v), b x t⟫) -
          24 * (R ^ 2 - ‖x - (z + (t - s) • v)‖ ^ 2)⁺ *
            ⟪x - (z + (t - s) • v),
              (a x t).toEuclideanLin (x - (z + (t - s) • v))⟫) := by
  obtain ⟨σ, hσ⟩ := exists_factors_of_posSemidef ha
  let ζ := x - (z + (t - s) • v)
  let H := (R ^ 2 - ‖ζ‖ ^ 2)⁺
  let α := ε * Real.exp (-δ * (t - s))
  have hsum :
      ∑ k, secondDirectionalDerivative
          (fun y ↦ movingPolynomialBump z v R ε δ s y t) x (σ k) =
        α * (24 * H * ⟪ζ, (a x t).toEuclideanLin ζ⟫ -
            6 * H ^ 2 * (a x t).trace) := by
    simp only [secondDirectionalDerivative_movingPolynomialBump]
    change (∑ k, α * (24 * H * ⟪ζ, σ k⟫ ^ 2 - 6 * H ^ 2 * ‖σ k‖ ^ 2)) = _
    simp only [mul_sub, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [sum_inner_sq_eq_matrix_quadratic (a x t) σ hσ,
      sum_norm_sq_eq_matrix_trace (a x t) σ hσ, ← inner_toEuclideanLin_self]
    simp only [Matrix.trace, Matrix.diag_apply]
  rw [matrixParabolicOperator_eq_factored a (fun _ _ ↦ σ) b c
    (contDiff_movingPolynomialBump z v R ε δ s t).contDiffAt hσ]
  rw [factoredParabolicOperatorWithPotential, factoredParabolicOperator,
    factoredEllipticOperator, (hasDerivAt_movingPolynomialBump z v R ε δ s x t).deriv,
    hsum, fderiv_movingPolynomialBump_apply]
  dsimp [ζ, H, α, movingPolynomialBump, polynomialBallBump]
  cas

/-- Explicit decay makes the moving bump a subsolution. The bounds are pointwise
and only need to hold at the point where the residual is evaluated. -/
theorem matrixParabolicOperator_movingPolynomialBump_nonpos
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (z v : ℝ^n) {R ε δ θ A B C : ℝ} (s : ℝ)
    (hR : 0 < R) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hdecay : C + (6 * (A + R * (‖v‖ + B)) + 24 * θ) ^ 2 /
      (4 * (24 * θ) * R ^ 2) ≤ δ)
    {x : ℝ^n} {t : ℝ} (ha : (a x t).PosSemidef)
    (hell : ∀ d : ℝ^n, θ * ‖d‖ ^ 2 ≤ ⟪d, (a x t).toEuclideanLin d⟫)
    (htrace : (a x t).trace ≤ A) (hdrift : ‖b x t‖ ≤ B) (hc : c x t ≤ C) :
    matrixParabolicOperator a b c (movingPolynomialBump z v R ε δ s) x t ≤ 0 := by
  rw [matrixParabolicOperator_movingPolynomialBump a b c z v R ε δ s ha]
  let ζ := x - (z + (t - s) • v)
  let h := R ^ 2 - ‖ζ‖ ^ 2
  change ε * Real.exp (-δ * (t - s)) *
    ((c x t - δ) * h⁺ ^ 3 +
      6 * h⁺ ^ 2 * (⟪ζ, v⟫ + (a x t).trace - ⟪ζ, b x t⟫) -
      24 * h⁺ * ⟪ζ, (a x t).toEuclideanLin ζ⟫) ≤ 0
  by_cases hh : h ≤ 0
  · simp [posPart_eq_zero.mpr hh]
  have hhpos : 0 < h := lt_of_not_ge hh
  rw [posPart_eq_self.mpr hhpos.le]
  have hζ : ‖ζ‖ ≤ R := by
    apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
    change 0 < R ^ 2 - ‖ζ‖ ^ 2 at hhpos
    exact (sub_pos.mp hhpos).le
  have hv : ⟪ζ, v⟫ ≤ R * ‖v‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hζ (norm_nonneg _))
  have hb : -⟪ζ, b x t⟫ ≤ R * B := by
    exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul hζ hdrift (norm_nonneg _) hR.le))
  have hlinear : ⟪ζ, v⟫ + (a x t).trace - ⟪ζ, b x t⟫ ≤
      A + R * (‖v‖ + B) := by
    cas
  let K := 6 * (A + R * (‖v‖ + B))
  let D := 24 * θ
  have hD : 0 < D := by dsimp [D]; positivity
  have hdecay' : c x t + (K + D) ^ 2 / (4 * D * R ^ 2) ≤ δ :=
    (add_le_add hc le_rfl).trans hdecay
  have hbase :
      (c x t - δ) * h ^ 3 +
          6 * h ^ 2 * (⟪ζ, v⟫ + (a x t).trace - ⟪ζ, b x t⟫) -
          24 * h * ⟪ζ, (a x t).toEuclideanLin ζ⟫ ≤
        (c x t - δ) * h ^ 3 + K * h ^ 2 - D * h * ‖ζ‖ ^ 2 := by
    calc
      _ ≤ (c x t - δ) * h ^ 3 + 6 * h ^ 2 * (A + R * (‖v‖ + B)) -
          24 * h * (θ * ‖ζ‖ ^ 2) :=
        sub_le_sub
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlinear (by positivity)))
          (mul_le_mul_of_nonneg_left (hell ζ) (by positivity))
      _ = _ := by dsimp [K, D]; cas
  have hres := cubic_decay_nonpos hD hR hhpos.le
    (show R ^ 2 ≤ h + ‖ζ‖ ^ 2 by dsimp [h]; linarith) hdecay'
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hε (Real.exp_nonneg _))
    (hbase.trans hres)

end ParabolicMaximum
