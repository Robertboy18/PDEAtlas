/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.Barrier.PowerComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expansion to a fixed later ball

The expanding polynomial barrier turns a lower bound on a small ball, at a
time in `[-1,1]`, into a lower bound on the unit ball at time `64`. The loss
is a fixed multiple of the initial radius to the power `2p`. This is the
power that will cancel the boundary weight in the Harnack argument.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A small-ball lower bound expands to the unit ball after a fixed delay.
Only separate spatial C² and temporal differentiability are needed. -/
theorem lower_bound_at_delayed_unit_ball
    {α τ B η r q : ℝ} {z : ℝ^n} (p : ℕ)
    (hα : 0 < α) (hη : 0 ≤ η) (hr : 0 < r) (hr₁ : r ≤ 1)
    (hz : z ∈ closedBall (0 : ℝ^n) 2) (hq : q ∈ Icc (-1) 1)
    (hdecay : (3 + 6 * (τ + 10 * B) + 24 * α) ^ 2 / (4 * (24 * α)) ≤
      (p : ℝ) + 3)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
    (ha : ∀ v ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64, (a v.1 v.2).PosSemidef)
    (hell : ∀ v ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64, ∀ w : ℝ^n,
      α * ‖w‖ ^ 2 ≤ ⟪w, (a v.1 v.2).toEuclideanLin w⟫)
    (htrace : ∀ v ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64, (a v.1 v.2).trace ≤ τ)
    (hdrift : ∀ v ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64, ‖d v.1 v.2‖ ≤ B)
    (u : ℝ^n → ℝ → ℝ)
    (hu : ContinuousOn (Function.uncurry u) (closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64))
    (hspace : ∀ v ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64,
      ContDiffAt ℝ 2 (fun x ↦ u x v.2) v.1)
    (htime : ∀ v ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64,
      DifferentiableAt ℝ (u v.1) v.2)
    (hsuper : ∀ v ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64,
      0 ≤ matrixParabolicOperator a d (fun _ _ ↦ 0) u v.1 v.2)
    (hnonneg : ∀ v ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64, 0 ≤ u v.1 v.2)
    (hinitial : ∀ x ∈ closedBall z r, η ≤ u x q) :
    ∀ y ∈ closedBall (0 : ℝ^n) 1,
      η / (8 * 66 ^ p) * r ^ (2 * p) ≤ u y 64 := by
  have ht : 0 < 64 - q := by linarith only [hq.2]
  have hradius : r ^ 2 + (64 - q) ≤ 10 ^ 2 := by
    nlinarith only [hr, hr₁, hq.1]
  have hmap :
      MapsTo (fun v : ℝ^n × ℝ ↦ (v.1, q + v.2))
        (closedBall z 10 ×ˢ Icc 0 (64 - q))
        (closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64) := by
    intro v hv
    refine ⟨?_, ?_, ?_⟩
    · exact mem_closedBall.2
        (by linarith only [dist_triangle v.1 z 0, mem_closedBall.1 hv.1, mem_closedBall.1 hz])
    · linarith only [hq.1, hv.2.1]
    · linarith only [hv.2.2]
  have hopen (x : ℝ^n) (hx : x ∈ ball z 10) (t : ℝ)
      (ht : t ∈ Ioo 0 (64 - q)) :
      (x, q + t) ∈ closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64 :=
    @hmap (x, t) ⟨ball_subset_closedBall hx, ht.1.le, ht.2.le⟩
  have h := lower_bound_on_expanding_halfBall
    (z := z) (r := r) (R := 10) (t := 64 - q) (θ := α) (η := η) (A := τ) (B := B)
    p hr (by norm_num) ht hα hη
    hradius hdecay (fun x t ↦ a x (q + t)) (fun x t ↦ d x (q + t))
    (fun x hx t ht ↦ ha (x, q + t) (hopen x hx t ht))
    (fun x hx t ht w ↦ hell (x, q + t) (hopen x hx t ht) w)
    (fun x hx t ht ↦ htrace (x, q + t) (hopen x hx t ht))
    (fun x hx t ht ↦ hdrift (x, q + t) (hopen x hx t ht))
    (fun x t ↦ u x (q + t))
    (hu.comp (continuous_fst.prodMk (continuous_const.add continuous_snd)).continuousOn hmap)
    (fun x hx t ht ↦ hspace (x, q + t) (hopen x hx t ht))
    (fun x hx t ht ↦
      ((htime (x, q + t) (hopen x hx t ht)).hasDerivAt.comp_const_add q t).differentiableAt)
    (fun x hx t ht ↦ by
      simpa only [matrixParabolicOperator, deriv_comp_const_add] using
        hsuper (x, q + t) (hopen x hx t ht))
    (fun x hx t ht ↦ hnonneg (x, q + t) (@hmap (x, t) ⟨hx, ht⟩))
    (by simpa only [add_zero] using hinitial)
  intro y hy
  have hyball : y ∈ closedBall z (Real.sqrt (r ^ 2 + (64 - q)) / 2) := by
    have hsqrt : 6 ≤ Real.sqrt (r ^ 2 + (64 - q)) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [sq_nonneg r, hq.2])
    rw [mem_closedBall]
    linarith only [dist_triangle y 0 z, mem_closedBall.1 hy, dist_comm (0 : ℝ^n) z,
      mem_closedBall.1 hz, hsqrt]
  have hpositive : 0 < r ^ 2 + (64 - q) := by positivity
  have hden : r ^ 2 + (64 - q) ≤ 66 := by nlinarith only [hr, hr₁, hq.1]
  have hratio : r ^ 2 / 66 ≤ r ^ 2 / (r ^ 2 + (64 - q)) :=
    div_le_div_of_nonneg_left (sq_nonneg r) hpositive hden
  have hpow := pow_le_pow_left₀ (div_nonneg (sq_nonneg r) (by norm_num)) hratio p
  calc
    _ = η / 8 * (r ^ 2 / 66) ^ p := by rw [div_pow, pow_mul]; ring
    _ ≤ η / 8 * (r ^ 2 / (r ^ 2 + (64 - q))) ^ p :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg hη (by norm_num))
    _ ≤ u y 64 := by
      simpa only [add_sub_cancel] using h (64 - q) ⟨ht.le, le_rfl⟩ y hyball

end ParabolicHarnack
