/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Gradient
public import PDE.Analysis.Calculus.StrongConvex
public import PDE.Analysis.Calculus.SecondDifference
public import PDE.Analysis.Convex.Differentiation.StrongConvexity

/-!
# Uniform Hessian bounds and the gradient

The Riesz isometry transfers a Hessian norm bound to a global Lipschitz
bound for the gradient. A positive quadratic Hessian lower bound gives
strong convexity, hence strong monotonicity. These conclusions use the
Fréchet derivatives of the potential and require no chosen coefficient field.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Analysis

open Set
open scoped NNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {L : E → ℝ}

/-- A twice continuously differentiable potential has a continuously
differentiable gradient. -/
theorem contDiff_gradient_of_contDiff_two (hL : ContDiff ℝ 2 L) :
    ContDiff ℝ 1 (∇ L) := by
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact R.contDiff.comp (hL.fderiv_right (m := 1) (by norm_num))

/-- A global Hessian norm bound is a Lipschitz bound for the gradient. -/
theorem lipschitzWith_gradient_of_hessian_bound (hL : ContDiff ℝ 2 L)
    {C : ℝ≥0} (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) :
    LipschitzWith C (∇ L) := by
  have hd : Differentiable ℝ (fderiv ℝ L) :=
    (hL.fderiv_right (m := 1) (by norm_num)).differentiable_one
  have hLip : LipschitzWith C (fderiv ℝ L) :=
    lipschitzWith_of_nnnorm_fderiv_le hd hbound
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ L x) -
    (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ L y)‖ ≤ _
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  exact hLip.norm_sub_le x y

omit [CompleteSpace E] in
/-- Uniform positivity of the Hessian gives strong convexity. -/
theorem strongConvexOn_of_hessian_bound (hL : ContDiff ℝ 2 L)
    {θ : ℝ} (hbound : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v) :
    StrongConvexOn univ θ L :=
  strongConvexOn_univ_of_hessian_lower_bound (hL.differentiable (by norm_num))
    ((hL.fderiv_right (m := 1) (by norm_num)).differentiable_one) hbound

/-- The gradient is strongly monotone with the Hessian lower-bound constant. -/
theorem strongMonotonicity_gradient_of_hessian_bound (hL : ContDiff ℝ 2 L)
    {θ : ℝ} (hbound : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (u v : E) :
    θ * ‖u - v‖ * ‖u - v‖ ≤ ⟪∇ L u - ∇ L v, u - v⟫ := by
  simpa only [pow_two, mul_assoc] using
    Convex.strongMonotonicity_of_strongConvex (strongConvexOn_of_hessian_bound hL hbound)
      (fun x ↦ (hL.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt) u v

end PDE.Analysis
