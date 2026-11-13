/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolynomialBump.Basic
import CAS.ExactTactic

/-!
# Polynomial bumps with an affine moving center

The positive-part cube of `R² - ‖x - z‖²` is globally `C²`.
Its first and second spatial derivatives vanish on and outside the sphere.
Multiplication by an exponential and translation of the center preserve these
properties. The formulas here concern real inner-product spaces and have no
dependence on a differential equation.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A bump whose center moves with constant velocity, with exponential decay. -/
def movingPolynomialBump (z v : E) (R ε δ s : ℝ) (x : E) (t : ℝ) : ℝ :=
  ε * Real.exp (-δ * (t - s)) * polynomialBallBump (z + (t - s) • v) R x

/-- Spatial regularity of the moving bump includes its moving sphere. -/
theorem contDiff_movingPolynomialBump (z v : E) (R ε δ s t : ℝ) :
    ContDiff ℝ 2 (fun x ↦ movingPolynomialBump z v R ε δ s x t) :=
  contDiff_const.mul (contDiff_polynomialBallBump _ _)

/-- The moving bump is jointly continuous in space and time. -/
theorem continuous_movingPolynomialBump (z v : E) (R ε δ s : ℝ) :
    Continuous (fun p : E × ℝ ↦ movingPolynomialBump z v R ε δ s p.1 p.2) := by
  unfold movingPolynomialBump polynomialBallBump
  simp only [posPart_def]
  fun_prop

/-- Motion of the center contributes the velocity term `6 g⁺² ⟪x - c(t), v⟫` to the time
derivative, where `g = R² - ‖x - c(t)‖²`. Its sign depends on the side of the center. -/
theorem hasDerivAt_movingPolynomialBump (z v : E) (R ε δ s : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (movingPolynomialBump z v R ε δ s x)
      (ε * Real.exp (-δ * (t - s)) *
        (-δ * (R ^ 2 - ‖x - (z + (t - s) • v)‖ ^ 2)⁺ ^ 3 +
          6 * (R ^ 2 - ‖x - (z + (t - s) • v)‖ ^ 2)⁺ ^ 2 *
            ⟪x - (z + (t - s) • v), v⟫_ℝ)) t := by
  have hcenter : HasDerivAt (fun r : ℝ ↦ z + (r - s) • v) v t := by
    simpa using (((hasDerivAt_id t).sub_const s).smul_const v).const_add z
  have hgap : HasDerivAt (fun r : ℝ ↦ R ^ 2 - ‖x - (z + (r - s) • v)‖ ^ 2)
      (2 * ⟪x - (z + (t - s) • v), v⟫_ℝ) t := by
    simpa using (((hasDerivAt_const t x).sub hcenter).norm_sq).const_sub (R ^ 2)
  have hcube := (hasDerivAt_posPart_pow 1 _).comp t hgap
  have hdecay : HasDerivAt (fun r : ℝ ↦ ε * Real.exp (-δ * (r - s)))
      (-δ * ε * Real.exp (-δ * (t - s))) t := by
    cas
  unfold movingPolynomialBump polynomialBallBump
  convert! (hdecay.mul hcube) using 1
  simp only [Function.comp_apply, Nat.reduceAdd, Nat.cast_ofNat]
  cas

/-- The spatial first derivative keeps the time-dependent scalar factor. -/
theorem fderiv_movingPolynomialBump_apply
    (z v : E) (R ε δ s : ℝ) (x d : E) (t : ℝ) :
    fderiv ℝ (fun y ↦ movingPolynomialBump z v R ε δ s y t) x d =
      ε * Real.exp (-δ * (t - s)) *
        (-6 * (R ^ 2 - ‖x - (z + (t - s) • v)‖ ^ 2)⁺ ^ 2 *
          ⟪x - (z + (t - s) • v), d⟫_ℝ) := by
  unfold movingPolynomialBump
  rw [fderiv_const_mul
    ((contDiff_polynomialBallBump (z + (t - s) • v) R).differentiable
      (by norm_num) x)]
  rw [smul_apply, smul_eq_mul, fderiv_polynomialBallBump_apply]

/-- The spatial second derivative keeps the same scalar factor. -/
theorem secondDirectionalDerivative_movingPolynomialBump
    (z v : E) (R ε δ s : ℝ) (x d : E) (t : ℝ) :
    secondDirectionalDerivative (fun y ↦ movingPolynomialBump z v R ε δ s y t) x d =
      ε * Real.exp (-δ * (t - s)) *
        (24 * (R ^ 2 - ‖x - (z + (t - s) • v)‖ ^ 2)⁺ *
            ⟪x - (z + (t - s) • v), d⟫_ℝ ^ 2 -
          6 * (R ^ 2 - ‖x - (z + (t - s) • v)‖ ^ 2)⁺ ^ 2 * ‖d‖ ^ 2) := by
  unfold movingPolynomialBump
  rw [secondDirectionalDerivative_const_mul, secondDirectionalDerivative_polynomialBallBump]

/-- At its starting time the moving bump has its prescribed initial profile. -/
@[simp]
theorem movingPolynomialBump_start (z v : E) (R ε δ s : ℝ) (x : E) :
    movingPolynomialBump z v R ε δ s x s = ε * polynomialBallBump z R x := by
  simp [movingPolynomialBump]

/-- The value at the moving center is `ε e^{-δ(t-s)} R⁶`. It is positive when `0 < ε` and
`R ≠ 0`. -/
theorem movingPolynomialBump_center (z v : E) (R ε δ s t : ℝ) :
    movingPolynomialBump z v R ε δ s (z + (t - s) • v) t =
      ε * Real.exp (-δ * (t - s)) * R ^ 6 := by
  simp [movingPolynomialBump]

end PDE.Analysis
