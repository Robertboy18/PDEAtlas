/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Symmetry of the derivative of the gradient

The Riesz identification transports the second Fréchet derivative
to the derivative of the gradient. Schwarz symmetry then gives symmetry
of this linear operator in the real inner product.
-/

@[expose] public noncomputable section

open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {u : E → ℝ} {x : E}

/-- The derivative of a C² gradient is symmetric in the real inner product. -/
theorem ContDiffAt.inner_fderiv_gradient_comm (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    inner ℝ (fderiv ℝ (∇ u) x v) w =
      inner ℝ v (fderiv ℝ (∇ u) x w) := by
  have hd := (hu.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)).differentiableAt
    (by norm_num)
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hg := R.hasFDerivAt.comp x hd.hasFDerivAt
  change inner ℝ (fderiv ℝ (R ∘ fderiv ℝ u) x v) w =
    inner ℝ v (fderiv ℝ (R ∘ fderiv ℝ u) x w)
  rw [hg.fderiv]
  change inner ℝ ((InnerProductSpace.toDual ℝ E).symm
      (fderiv ℝ (fderiv ℝ u) x v)) w =
    inner ℝ v ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ u) x w))
  rw [InnerProductSpace.toDual_symm_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  exact (hu.isSymmSndFDerivAt (by norm_num)).eq v w
