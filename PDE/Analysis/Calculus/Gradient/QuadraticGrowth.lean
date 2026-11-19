/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Gradient.HessianBounds

/-!
# Quadratic growth with an arbitrary affine part

A positive lower Hessian bound and a bounded Hessian give two-sided
quadratic growth. The offsets retain the value and derivative at zero:
neither normalization is required. These estimates are useful when a
signed integral energy is extended by `+∞` outside its Sobolev domain.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {L : E → ℝ}

/-- Uniform convexity absorbs the linear part at zero into a constant,
leaving a positive quadratic lower bound. -/
theorem quadratic_lower_bound_of_hessian_bound (hL : ContDiff ℝ 2 L)
    {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v) (z : E) :
    θ / 4 * ‖z‖ ^ 2 - (|L 0| + ‖fderiv ℝ L 0‖ ^ 2 / θ) ≤ L z := by
  have hs := Convex.fderiv_add_quadratic_le_sub_of_strongConvex
    (strongConvexOn_of_hessian_bound hL hlower)
    (hL.differentiable (by norm_num) 0).hasFDerivAt z
  simp only [sub_zero] at hs
  have hD := neg_abs_le (fderiv ℝ L 0 z)
  have hnorm := (fderiv ℝ L 0).le_opNorm z
  rw [Real.norm_eq_abs] at hnorm
  have hcancel : θ * (‖fderiv ℝ L 0‖ ^ 2 / θ) = ‖fderiv ℝ L 0‖ ^ 2 := by
    field_simp
  have hYoung : ‖fderiv ℝ L 0‖ * ‖z‖ ≤
      θ / 4 * ‖z‖ ^ 2 + ‖fderiv ℝ L 0‖ ^ 2 / θ := by
    nlinarith [sq_nonneg (θ * ‖z‖ - 2 * ‖fderiv ℝ L 0‖)]
  linarith [neg_abs_le (L 0)]

/-- A Hessian norm bound gives a quadratic upper bound without removing
the density's constant or affine part. -/
theorem quadratic_upper_bound_of_hessian_bound (hL : ContDiff ℝ 2 L)
    {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) (z : E) :
    L z ≤ (|L 0| + ‖fderiv ℝ L 0‖ ^ 2) + (C + 1) * ‖z‖ ^ 2 := by
  have hs := norm_sub_sub_fderiv_le_of_hessian_bound hC convex_univ
    (hL.differentiable (by norm_num))
    ((hL.fderiv_right (m := 1) (by norm_num)).differentiable_one)
    (fun x _ ↦ hupper x) (mem_univ (0 : E)) (mem_univ z)
  simp only [sub_zero, Real.norm_eq_abs] at hs
  have hnorm := (fderiv ℝ L 0).le_opNorm z
  rw [Real.norm_eq_abs] at hnorm
  nlinarith [le_abs_self (L z - L 0 - fderiv ℝ L 0 z),
    le_abs_self (fderiv ℝ L 0 z), le_abs_self (L 0),
    sq_nonneg (‖fderiv ℝ L 0‖ - ‖z‖)]

end PDE.Analysis
