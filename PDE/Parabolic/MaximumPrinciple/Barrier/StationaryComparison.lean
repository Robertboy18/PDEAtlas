/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.Strong.BarrierComparison
import CAS.ExactTactic

/-!
# Uniform retention of a ball lower bound

Over a time interval proportional to the square of its radius, a stationary
ball retains a fixed fraction of its initial lower bound. The decay rate of
the moving polynomial barrier scales as the inverse radius squared, so the
two factors cancel. A bounded drift is controlled uniformly at scales
at most one.
-/

@[expose] public noncomputable section

namespace ParabolicMaximum

open Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A ball lower bound persists on its inner half for a prescribed number of
parabolic time units. The retained fraction is independent of the scale,
center, starting time, coefficients, and supersolution. -/
theorem exists_uniform_stationary_halfBall_fraction
    {R H θ A B : ℝ} (hR : 0 < R) (hH : 0 < H) (hθ : 0 < θ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ (z : ℝ^n) (s r : ℝ), 0 < r → r ≤ 1 →
        ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ → ℝ^n),
          (∀ x ∈ ball z (2 * (r * R)), ∀ q ∈ Ioo s (s + r ^ 2 * H),
            (a x q).PosSemidef) →
          (∀ x ∈ ball z (2 * (r * R)), ∀ q ∈ Ioo s (s + r ^ 2 * H), ∀ d : ℝ^n,
            θ * ‖d‖ ^ 2 ≤ ⟪d, (a x q).toEuclideanLin d⟫) →
          (∀ x ∈ ball z (2 * (r * R)), ∀ q ∈ Ioo s (s + r ^ 2 * H),
            (a x q).trace ≤ A) →
          (∀ x ∈ ball z (2 * (r * R)), ∀ q ∈ Ioo s (s + r ^ 2 * H), ‖b x q‖ ≤ B) →
          ∀ (w : ℝ^n → ℝ → ℝ) (η : ℝ), 0 ≤ η →
            ContinuousOn (Function.uncurry w)
              (closedBall z (2 * (r * R)) ×ˢ Icc s (s + r ^ 2 * H)) →
            (∀ x ∈ ball z (2 * (r * R)), ∀ q ∈ Ioo s (s + r ^ 2 * H),
              ContDiffAt ℝ 2 (fun y ↦ w y q) x) →
            (∀ x ∈ ball z (2 * (r * R)), ∀ q ∈ Ioo s (s + r ^ 2 * H),
              DifferentiableAt ℝ (w x) q) →
            (∀ x ∈ ball z (2 * (r * R)), ∀ q ∈ Ioo s (s + r ^ 2 * H),
              0 ≤ matrixParabolicOperator a b (fun _ _ ↦ 0) w x q) →
            (∀ x ∈ closedBall z (2 * (r * R)), ∀ q ∈ Icc s (s + r ^ 2 * H),
              0 ≤ w x q) →
            (∀ x ∈ closedBall z (r * R), η ≤ w x s) →
            ∀ q ∈ Icc s (s + r ^ 2 * H), ∀ x ∈ closedBall z (r * R / 2),
              γ * η ≤ w x q := by
  let D := (6 * (A + R * B) + 24 * θ) ^ 2 / (4 * (24 * θ) * R ^ 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨Real.exp (-D * H) / 8, by positivity, ?_⟩
  intro z s r hr hr₁ a b ha hell htrace hdrift w η hη hcont hspace htime hsuper
    hnonneg hinitial
  have hrR : 0 < r * R := mul_pos hr hR
  have hr₂ : 0 < r ^ 2 := sq_pos_of_pos hr
  have hnum : (6 * (A + r * R * B) + 24 * θ) ^ 2 ≤
      (6 * (A + R * B) + 24 * θ) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    have hscale : r * R ≤ R := mul_le_of_le_one_left hR.le hr₁
    linarith [mul_le_mul_of_nonneg_right hscale hB]
  have hdecay : 0 + (6 * (A + r * R * (‖(0 : ℝ^n)‖ + B)) + 24 * θ) ^ 2 /
      (4 * (24 * θ) * (r * R) ^ 2) ≤ D / r ^ 2 := by
    simp only [norm_zero, zero_add]
    calc
      _ ≤ (6 * (A + R * B) + 24 * θ) ^ 2 / (4 * (24 * θ) * (r * R) ^ 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = D / r ^ 2 := by dsimp only [D]; cas
  have h := lower_bound_on_moving_halfBall hrR le_rfl
    (lt_add_of_pos_right s (mul_pos hr₂ hH)) hθ hη (0 : ℝ^n)
    (by simp only [norm_zero, mul_zero]; exact hrR.le) hdecay a b (fun _ _ ↦ 0)
    ha hell htrace hdrift (fun _ _ _ _ ↦ le_rfl) (fun _ _ _ _ ↦ le_rfl)
    w hcont hspace htime hsuper hnonneg hinitial
  intro q hq x hx
  have hdecayTime : D / r ^ 2 * (q - s) ≤ D * H := by
    calc
      _ ≤ D / r ^ 2 * (r ^ 2 * H) :=
        mul_le_mul_of_nonneg_left (by linarith [hq.2]) (div_nonneg hD hr₂.le)
      _ = D * H := by cas using hr₂.ne'
  have hretained : Real.exp (-D * H) / 8 * η ≤
      η / 8 * Real.exp (-(D / r ^ 2) * (q - s)) := by
    calc
      _ = η / 8 * Real.exp (-D * H) := by cas
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) (div_nonneg hη (by norm_num))
  exact hretained.trans (h q hq x (by simpa only [smul_zero, add_zero] using hx))

end ParabolicMaximum
