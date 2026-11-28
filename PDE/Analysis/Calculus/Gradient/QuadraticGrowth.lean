/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Calculus.Gradient.HessianBounds

/-!
# Quadratic growth with an arbitrary affine part

A positive lower Hessian bound and a bounded Hessian give two-sided
quadratic growth. The offsets retain the value and derivative at zero:
neither normalization is required. These estimates are useful when a
signed integral energy is extended by `+∞` outside its Sobolev domain.

A Lipschitz map grows at most linearly (`norm_le_norm_zero_add_mul_of_lipschitzWith`). A
Lipschitz derivative therefore bounds the absolute value by a quadratic
(`abs_le_quadratic_of_lipschitzWith_fderiv`), in every real normed space and
without convexity. The upper bound under a Hessian norm bound is a case of it.
A Lipschitz gradient gives a Lipschitz derivative (`lipschitzWith_fderiv_of_gradient`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set
open scoped NNReal

/-- A Lipschitz map between seminormed groups grows at most linearly:
`‖g z‖ ≤ ‖g 0‖ + C ‖z‖`. -/
theorem norm_le_norm_zero_add_mul_of_lipschitzWith {E G : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup G] {g : E → G} {C : ℝ≥0} (h : LipschitzWith C g) (z : E) :
    ‖g z‖ ≤ ‖g 0‖ + C * ‖z‖ := by
  have hsub := h.norm_sub_le z 0
  rw [sub_zero] at hsub
  have htri := norm_add_le (g z - g 0) (g 0)
  rw [sub_add_cancel] at htri
  linarith

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : E → ℝ}

/-- A differentiable function with Lipschitz derivative grows at most quadratically, in
absolute value. The offset retains the value and the derivative at zero. The mean value
inequality on the ball of radius `‖z‖` gives `|L z - L 0| ≤ (‖DL(0)‖ + C ‖z‖) ‖z‖`. -/
theorem abs_le_quadratic_of_lipschitzWith_fderiv (hd : Differentiable ℝ L) {C : ℝ≥0}
    (hLip : LipschitzWith C (fderiv ℝ L)) (z : E) :
    |L z| ≤ (|L 0| + ‖fderiv ℝ L 0‖ ^ 2) + (C + 1) * ‖z‖ ^ 2 := by
  have hbound : ∀ x ∈ Metric.closedBall (0 : E) ‖z‖,
      ‖fderiv ℝ L x‖ ≤ ‖fderiv ℝ L 0‖ + C * ‖z‖ := by
    intro x hx
    have hx' : ‖x‖ ≤ ‖z‖ := mem_closedBall_zero_iff.mp hx
    have hgrow := norm_le_norm_zero_add_mul_of_lipschitzWith hLip x
    have hmul : (C : ℝ) * ‖x‖ ≤ C * ‖z‖ := mul_le_mul_of_nonneg_left hx' C.coe_nonneg
    linarith
  have hmv := (convex_closedBall (0 : E) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ ↦ hd x) hbound (Metric.mem_closedBall_self (norm_nonneg z))
    (mem_closedBall_zero_iff.mpr le_rfl)
  rw [sub_zero, Real.norm_eq_abs] at hmv
  have habs : |L z| ≤ |L 0| + |L z - L 0| := by
    simpa only [add_sub_cancel] using abs_add_le (L 0) (L z - L 0)
  nlinarith [sq_nonneg (‖fderiv ℝ L 0‖ - ‖z‖), norm_nonneg z, norm_nonneg (fderiv ℝ L 0),
    mul_nonneg (norm_nonneg (fderiv ℝ L 0)) (norm_nonneg z)]

end Lipschitz

/-- A Lipschitz bound for the gradient is a Lipschitz bound for the Fréchet derivative, with
the same constant: the Riesz identification is an isometry. This puts a function with
Lipschitz gradient in the scope of `abs_le_quadratic_of_lipschitzWith_fderiv`. -/
theorem lipschitzWith_fderiv_of_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {L : E → ℝ} {C : ℝ≥0}
    (h : LipschitzWith C (gradient L)) : LipschitzWith C (fderiv ℝ L) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hxy := h.dist_le_mul x y
  rw [dist_eq_norm] at hxy ⊢
  have heq : fderiv ℝ L x - fderiv ℝ L y =
      InnerProductSpace.toDual ℝ E (gradient L x - gradient L y) := by
    simp only [gradient, map_sub, LinearIsometryEquiv.apply_symm_apply]
  rwa [heq, LinearIsometryEquiv.norm_map]

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
the density's constant or affine part. The derivative is Lipschitz, so this is
a case of `abs_le_quadratic_of_lipschitzWith_fderiv`. -/
theorem quadratic_upper_bound_of_hessian_bound (hL : ContDiff ℝ 2 L)
    {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) (z : E) :
    L z ≤ (|L 0| + ‖fderiv ℝ L 0‖ ^ 2) + (C + 1) * ‖z‖ ^ 2 :=
  (le_abs_self _).trans (abs_le_quadratic_of_lipschitzWith_fderiv
    (hL.differentiable (by norm_num))
    (lipschitzWith_of_nnNorm_fderiv_le (C := ⟨C, hC⟩)
      (hL.fderiv_right (m := 1) (by norm_num)).differentiable_one hupper) z)

end PDE.Analysis
