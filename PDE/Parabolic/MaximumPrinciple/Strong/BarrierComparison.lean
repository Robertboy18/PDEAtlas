/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.Strong.Barrier
public import PDE.Parabolic.MaximumPrinciple.TimeSlab
import CAS.ExactTactic

/-!
# Quantitative transport of a ball lower bound

A prescribed lower bound on an initial ball propagates to the inner half of
a moving ball. The explicit exponential decay depends only on its radius,
velocity, ellipticity, and coefficient bounds. The comparison assumes
spatial C² and temporal differentiability separately, and continuity
supplies the terminal time.
-/

@[expose] public noncomputable section

namespace ParabolicMaximum

open PDE.Analysis Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A uniform initial ball lower bound gives a quantitative lower bound on a
moving half-ball throughout a closed slab. All decay parameters precede the
coefficients and supersolution. No coefficient derivatives are needed. -/
theorem lower_bound_on_moving_halfBall
    {y : ℝ^n} {r R s t θ η δ A B C : ℝ}
    (hR : 0 < R) (hRr : R ≤ r) (hst : s < t)
    (hθ : 0 < θ) (hη : 0 ≤ η) (v : ℝ^n)
    (htravel : (t - s) * ‖v‖ ≤ r)
    (hdecay : C + (6 * (A + R * (‖v‖ + B)) + 24 * θ) ^ 2 /
      (4 * (24 * θ) * R ^ 2) ≤ δ)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (ha : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, (a x q).PosSemidef)
    (hell : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, ∀ d : ℝ^n,
      θ * ‖d‖ ^ 2 ≤ ⟪d, (a x q).toEuclideanLin d⟫)
    (htrace : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, (a x q).trace ≤ A)
    (hdrift : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, ‖b x q‖ ≤ B)
    (hc : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, 0 ≤ c x q)
    (hcupper : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, c x q ≤ C)
    (w : ℝ^n → ℝ → ℝ)
    (hwcont : ContinuousOn (Function.uncurry w) (closedBall y (2 * r) ×ˢ Icc s t))
    (hwspace : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t,
      ContDiffAt ℝ 2 (fun z ↦ w z q) x)
    (hwtime : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, DifferentiableAt ℝ (w x) q)
    (hwsuper : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t,
      0 ≤ matrixParabolicOperator a b c w x q)
    (hwnonneg : ∀ x ∈ closedBall y (2 * r), ∀ q ∈ Icc s t, 0 ≤ w x q)
    (hinitial : ∀ x ∈ closedBall y R, η ≤ w x s) :
    ∀ q ∈ Icc s t, ∀ x ∈ closedBall (y + (q - s) • v) (R / 2),
      η / 8 * Real.exp (-δ * (q - s)) ≤ w x q := by
  have hr : 0 < r := by linarith
  let ε := η / R ^ 6
  have hε : 0 ≤ ε := div_nonneg hη (pow_nonneg hR.le _)
  have hεR : ε * R ^ 6 = η := div_mul_cancel₀ _ (ne_of_gt (pow_pos hR _))
  let φ := movingPolynomialBump y v R ε δ s
  have hcenter (q : ℝ) (hq : q ∈ Icc s t) :
      dist (y + (q - s) • v) y ≤ r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hq.1)]
    exact (mul_le_mul_of_nonneg_right (by linarith [hq.2]) (norm_nonneg _)).trans htravel
  have hφsub (x : ℝ^n) (hx : x ∈ ball y (2 * r)) (q : ℝ) (hq : q ∈ Ioo s t) :
      matrixParabolicOperator a b c φ x q ≤ 0 :=
    matrixParabolicOperator_movingPolynomialBump_nonpos a b c y v s hR hε hθ
      hdecay (ha x hx q hq) (hell x hx q hq) (htrace x hx q hq)
      (hdrift x hx q hq) (hcupper x hx q hq)
  have hφinitial (x : ℝ^n) (hx : x ∈ closure (ball y (2 * r))) :
      φ x s ≤ w x s := by
    change movingPolynomialBump y v R ε δ s x s ≤ _
    rw [movingPolynomialBump_start]
    by_cases hxR : x ∈ closedBall y R
    · calc
        _ ≤ ε * R ^ 6 := mul_le_mul_of_nonneg_left (polynomialBallBump_le y R x) hε
        _ = η := hεR
        _ ≤ _ := hinitial x hxR
    · have hxnorm : R ≤ ‖x - y‖ := (lt_of_not_ge hxR).le
      rw [polynomialBallBump_eq_zero hR.le hxnorm, mul_zero]
      exact hwnonneg x (closure_ball_subset_closedBall hx) s ⟨le_rfl, hst.le⟩
  have hφlateral (x : ℝ^n) (hx : x ∈ frontier (ball y (2 * r)))
      (q : ℝ) (hq : q ∈ Icc s t) : φ x q ≤ w x q := by
    have hxnorm : R ≤ ‖x - (y + (q - s) • v)‖ := by
      rw [← dist_eq_norm]
      linarith [dist_triangle x (y + (q - s) • v) y, hcenter q hq,
        mem_sphere.1 (frontier_ball_subset_sphere hx)]
    rw [show φ x q = 0 by
      dsimp only [φ, movingPolynomialBump]
      rw [polynomialBallBump_eq_zero hR.le hxnorm, mul_zero]]
    exact hwnonneg x (closure_ball_subset_closedBall (frontier_subset_closure hx)) q hq
  have hΩcompact : IsCompact (closure (ball y (2 * r))) :=
    (isCompact_closedBall y (2 * r)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  have hcompare := matrix_comparison_on_timeSlab isOpen_ball
    (nonempty_ball.mpr (by positivity)) hΩcompact hst a b c ha hc φ w
    (continuous_movingPolynomialBump y v R ε δ s).continuousOn
    (hwcont.mono (Set.prod_mono closure_ball_subset_closedBall Subset.rfl))
    (fun _ _ q _ ↦ (contDiff_movingPolynomialBump y v R ε δ s q).contDiffAt)
    hwspace
    (fun x _ q _ ↦ (hasDerivAt_movingPolynomialBump y v R ε δ s x q).differentiableAt)
    hwtime
    (fun x hx q hq ↦ (hφsub x hx q hq).trans (hwsuper x hx q hq))
    hφlateral hφinitial
  intro q hq x hx
  have hxnorm : ‖x - (y + (q - s) • v)‖ ≤ R / 2 := hx
  have hxΩ : x ∈ closure (ball y (2 * r)) := subset_closure (mem_ball.2 (by
    linarith [dist_triangle x (y + (q - s) • v) y, hcenter q hq, mem_closedBall.1 hx]))
  have hgap : R ^ 2 / 2 ≤ (R ^ 2 - ‖x - (y + (q - s) • v)‖ ^ 2)⁺ := by
    have hsq := (sq_le_sq₀ (norm_nonneg _) (half_pos hR).le).mpr hxnorm
    exact (by nlinarith : R ^ 2 / 2 ≤ R ^ 2 - ‖x - (y + (q - s) • v)‖ ^ 2).trans
      (le_sup_left)
  have hbump : R ^ 6 / 8 ≤ polynomialBallBump (y + (q - s) • v) R x := by
    calc
      _ = (R ^ 2 / 2) ^ 3 := by cas
      _ ≤ _ := pow_le_pow_left₀ (by positivity : 0 ≤ R ^ 2 / 2) hgap 3
  have hlow : η / 8 * Real.exp (-δ * (q - s)) ≤ φ x q := by
    calc
      _ = ε * Real.exp (-δ * (q - s)) * (R ^ 6 / 8) := by rw [← hεR]; cas
      _ ≤ _ := mul_le_mul_of_nonneg_left hbump (mul_nonneg hε (Real.exp_nonneg _))
  exact hlow.trans (hcompare x hxΩ q hq)

end ParabolicMaximum
