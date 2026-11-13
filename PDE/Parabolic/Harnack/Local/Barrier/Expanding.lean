/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolynomialBump.Expanding
public import PDE.Analysis.Calculus.QuadraticDecay
public import PDE.Parabolic.MaximumPrinciple.Barrier.WeightedExpansion
public import PDE.Analysis.LinearAlgebra.Ellipticity
import CAS.ExactTactic

/-!
# Expanding polynomial barriers with early forcing

The activated bump has zero initial value. An explicit exponential damping
makes its parabolic residual nonpositive after a prescribed activation
time. Before that time the residual vanishes outside the small support ball.
This separates the source cylinder from a later cylinder where the bump has
expanded. Only coefficient values and ellipticity are used.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis EllipticMaximum ParabolicMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The residual of an activated expanding bump, including on its moving
sphere. Activation contributes the additional undamped cubic term. -/
theorem matrixParabolicOperator_expandingPolynomialBump
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (z : ℝ^n) {r v δ t : ℝ} (x : ℝ^n) (ha : (a x t).PosSemidef) :
    matrixParabolicOperator a b (fun _ _ ↦ 0) (expandingPolynomialBump z r v δ) x t =
      Real.exp (-δ * t) *
        ((1 - δ * t) * (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ ^ 3 +
          t * (3 * v + 6 * ((a x t).trace - ⟪x - z, b x t⟫)) *
            (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ ^ 2 -
          24 * t * (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ *
            ⟪x - z, (a x t).toEuclideanLin (x - z)⟫) := by
  have hρ : HasDerivAt (fun s : ℝ ↦ r ^ 2 + v * s) v t := by cas
  have hw : HasDerivAt (fun s : ℝ ↦ s * Real.exp (-δ * s))
      ((1 - δ * t) * Real.exp (-δ * t)) t := by cas
  unfold expandingPolynomialBump
  rw [matrixParabolicOperator_weightedPolynomialBallBump a b (fun _ _ ↦ 0) z x
    hρ hw ha]
  cas

/-- After the activation time, the growing bump is a subsolution. The lower
radius controls the damping and the upper radius controls the drift. -/
theorem matrixParabolicOperator_expandingPolynomialBump_nonpos
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (z : ℝ^n) {r R v δ τ B θ ε t : ℝ} (x : ℝ^n)
    (hr : 0 < r) (hR : 0 ≤ R) (hv : 0 ≤ v) (hθ : 0 < θ)
    (hε : 0 < ε) (ht : ε ≤ t) (hradius : r ^ 2 + v * t ≤ R ^ 2)
    (hdecay : ε⁻¹ +
      (3 * v + 6 * (τ + R * B) + 24 * θ) ^ 2 / (4 * (24 * θ) * r ^ 2) ≤ δ)
    (ha : (a x t).PosSemidef)
    (hell : ∀ d : ℝ^n, θ * ‖d‖ ^ 2 ≤ ⟪d, (a x t).toEuclideanLin d⟫)
    (htrace : (a x t).trace ≤ τ) (hdrift : ‖b x t‖ ≤ B) :
    matrixParabolicOperator a b (fun _ _ ↦ 0) (expandingPolynomialBump z r v δ) x t ≤ 0 := by
  have ht0 : 0 ≤ t := hε.le.trans ht
  rw [matrixParabolicOperator_expandingPolynomialBump a b z x ha]
  let h := r ^ 2 + v * t - ‖x - z‖ ^ 2
  change Real.exp (-δ * t) *
    ((1 - δ * t) * h⁺ ^ 3 +
      t * (3 * v + 6 * ((a x t).trace - ⟪x - z, b x t⟫)) * h⁺ ^ 2 -
      24 * t * h⁺ * ⟪x - z, (a x t).toEuclideanLin (x - z)⟫) ≤ 0
  by_cases hh : h ≤ 0
  · simp [posPart_eq_zero.mpr hh]
  have hhpos : 0 < h := lt_of_not_ge hh
  rw [posPart_eq_self.mpr hhpos.le]
  have hxR : ‖x - z‖ ≤ R := (sq_le_sq₀ (norm_nonneg _) hR).mp (by dsimp [h] at hhpos; linarith)
  have hinner : -⟪x - z, b x t⟫ ≤ R * B :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul hxR hdrift (norm_nonneg _) hR))
  have hlinear : 3 * v + 6 * ((a x t).trace - ⟪x - z, b x t⟫) ≤
      3 * v + 6 * (τ + R * B) := by linarith
  have hone : 1 ≤ ε⁻¹ * t := by
    simpa only [inv_mul_cancel₀ hε.ne'] using mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hε.le)
  let K := 3 * v + 6 * (τ + R * B)
  let D := 24 * θ
  have hdecay' := cubic_decay_nonpos (show 0 < D by dsimp [D]; positivity) hr hhpos.le
    (show r ^ 2 ≤ h + ‖x - z‖ ^ 2 by dsimp [h]; nlinarith) hdecay
  have hbase :
      (1 - δ * t) * h ^ 3 +
        t * (3 * v + 6 * ((a x t).trace - ⟪x - z, b x t⟫)) * h ^ 2 -
        24 * t * h * ⟪x - z, (a x t).toEuclideanLin (x - z)⟫ ≤
      t * ((ε⁻¹ - δ) * h ^ 3 + K * h ^ 2 - D * h * ‖x - z‖ ^ 2) := by
    calc
      _ ≤ (ε⁻¹ * t - δ * t) * h ^ 3 + t * K * h ^ 2 -
          24 * t * h * (θ * ‖x - z‖ ^ 2) :=
        sub_le_sub
          (add_le_add
            (mul_le_mul_of_nonneg_right (sub_le_sub_right hone _) (pow_nonneg hhpos.le _))
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlinear ht0) (sq_nonneg h)))
          (mul_le_mul_of_nonneg_left (hell (x - z)) (by positivity))
      _ = _ := by dsimp [D]; cas
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
    (hbase.trans (mul_nonpos_of_nonneg_of_nonpos ht0 hdecay'))

/-- A coefficient-only upper bound for the forcing throughout the activation
slab. Neither the exponential decay nor elliptic curvature contributes
positively to this bound. -/
theorem matrixParabolicOperator_expandingPolynomialBump_le
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (z : ℝ^n) {r R v δ τ B s t : ℝ} (x : ℝ^n)
    (hR : 0 ≤ R) (hv : 0 ≤ v) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (ht : 0 ≤ t) (hts : t ≤ s) (hradius : r ^ 2 + v * t ≤ R ^ 2)
    (ha : (a x t).PosSemidef) (hquadratic : 0 ≤ ⟪x - z, (a x t).toEuclideanLin (x - z)⟫)
    (htrace : (a x t).trace ≤ τ) (hdrift : ‖b x t‖ ≤ B) :
    matrixParabolicOperator a b (fun _ _ ↦ 0) (expandingPolynomialBump z r v δ) x t ≤
      R ^ 6 + s * (3 * v + 6 * (τ + R * B)) * R ^ 4 := by
  have hs : 0 ≤ s := ht.trans hts
  rw [matrixParabolicOperator_expandingPolynomialBump a b z x ha]
  let h := r ^ 2 + v * t - ‖x - z‖ ^ 2
  let K := 3 * v + 6 * (τ + R * B)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  change Real.exp (-δ * t) *
    ((1 - δ * t) * h⁺ ^ 3 +
      t * (3 * v + 6 * ((a x t).trace - ⟪x - z, b x t⟫)) * h⁺ ^ 2 -
      24 * t * h⁺ * ⟪x - z, (a x t).toEuclideanLin (x - z)⟫) ≤ R ^ 6 + s * K * R ^ 4
  by_cases hh : h ≤ 0
  · simp only [posPart_eq_zero.mpr hh, zero_pow (by decide : 3 ≠ 0),
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero]
    positivity
  have hhpos : 0 < h := lt_of_not_ge hh
  rw [posPart_eq_self.mpr hhpos.le]
  have hhR : h ≤ R ^ 2 := by dsimp [h]; linarith [sq_nonneg ‖x - z‖]
  have hxR : ‖x - z‖ ≤ R := (sq_le_sq₀ (norm_nonneg _) hR).mp (by dsimp [h] at hhpos; linarith)
  have hinner : -⟪x - z, b x t⟫ ≤ R * B :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul hxR hdrift (norm_nonneg _) hR))
  have hlinear : 3 * v + 6 * ((a x t).trace - ⟪x - z, b x t⟫) ≤ K := by dsimp [K]; linarith
  have hcubic : h ^ 3 ≤ R ^ 6 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ hhpos.le hhR 3
  have hsquare : h ^ 2 ≤ R ^ 4 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ hhpos.le hhR 2
  have hbase :
      (1 - δ * t) * h ^ 3 +
        t * (3 * v + 6 * ((a x t).trace - ⟪x - z, b x t⟫)) * h ^ 2 -
        24 * t * h * ⟪x - z, (a x t).toEuclideanLin (x - z)⟫ ≤
      R ^ 6 + s * K * R ^ 4 := by
    calc
      _ ≤ h ^ 3 + t * K * h ^ 2 := by
        have hfirst : (1 - δ * t) * h ^ 3 ≤ h ^ 3 := by
          simpa using mul_le_mul_of_nonneg_right
            (sub_le_self (1 : ℝ) (mul_nonneg hδ ht)) (pow_nonneg hhpos.le 3)
        have hsecond := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlinear ht) (sq_nonneg h)
        exact (sub_le_self _ (mul_nonneg (by positivity) hquadratic)).trans
          (add_le_add hfirst hsecond)
      _ ≤ _ := add_le_add hcubic
        (mul_le_mul (mul_le_mul_of_nonneg_right hts hK) hsquare (sq_nonneg h)
          (mul_nonneg hs hK))
  calc _ ≤ Real.exp (-δ * t) * (R ^ 6 + s * K * R ^ 4) := by gcongr
    _ ≤ _ := mul_le_of_le_one_left (by positivity)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) ht))

/-- Outside the early support ball the residual is exactly zero,
including on the support sphere. -/
theorem matrixParabolicOperator_expandingPolynomialBump_eq_zero
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (z : ℝ^n) {r v δ t : ℝ} (x : ℝ^n)
    (houtside : r ^ 2 + v * t ≤ ‖x - z‖ ^ 2) (ha : (a x t).PosSemidef) :
    matrixParabolicOperator a b (fun _ _ ↦ 0) (expandingPolynomialBump z r v δ) x t = 0 := by
  rw [matrixParabolicOperator_expandingPolynomialBump a b z x ha,
    posPart_eq_zero.mpr (sub_nonpos.mpr houtside)]
  simp

end ParabolicHarnack
