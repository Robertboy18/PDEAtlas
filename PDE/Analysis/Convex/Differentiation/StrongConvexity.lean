/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Differentiable.Supporting
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Quadratic support and monotonicity of strongly convex gradients

Subtracting half the convexity modulus times the squared norm reduces
quadratic support to the ordinary supporting-hyperplane inequality.
Adding the support inequalities in both directions then proves strong
monotonicity of the gradient.
-/

@[expose] public section

namespace PDE.Analysis.Convex

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strong convexity gives a quadratic improvement of the tangent inequality. -/
theorem fderiv_add_quadratic_le_sub_of_strongConvex
    {L : E → ℝ} {θ : ℝ} (hL : StrongConvexOn univ θ L)
    {u : E} {D : E →L[ℝ] ℝ} (hD : HasFDerivAt L D u) (v : E) :
    D (v - u) + θ / 2 * ‖v - u‖ ^ 2 ≤ L v - L u := by
  have hq := hD.sub ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_mul (θ / 2))
  have hs := PDE.Analysis.fderiv_apply_sub_le_sub_of_convex
    (strongConvexOn_iff_convex.mp hL) hq v (mem_univ _) (mem_univ _)
  simp only [sub_apply, smul_apply, add_apply, innerSL_apply_apply, smul_eq_mul, two_smul,
    inner_sub_right, real_inner_self_eq_norm_sq] at hs
  rw [norm_sub_sq_real, real_inner_comm u v]
  nlinarith

/-- The derivative of a strongly convex potential is strongly monotone,
with the same modulus. -/
theorem strongMonotonicity_of_strongConvex
    {L : E → ℝ} {A : E → E} {θ : ℝ} (hL : StrongConvexOn univ θ L)
    (hD : ∀ u, HasFDerivAt L (innerSL ℝ (A u)) u) (u v : E) :
    θ * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫ := by
  have huv := fderiv_add_quadratic_le_sub_of_strongConvex hL (hD u) v
  have hvu := fderiv_add_quadratic_le_sub_of_strongConvex hL (hD v) u
  simp only [innerSL_apply_apply, inner_sub_right, norm_sub_rev v u] at huv hvu
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith

end PDE.Analysis.Convex
