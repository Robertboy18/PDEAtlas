/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Differentiating gradients

The Riesz map turns the derivative of a real-valued function into its gradient
(Mathlib's `gradient`, written `∇ u`, defined with `InnerProductSpace.toDual`).
Since this map is continuous and linear, it preserves local smoothness and
identifies the derivative of the gradient with the Hessian. The map also sends
zero to zero, so the gradient keeps compact support. These facts apply in any
real Hilbert space. On `ℝ^n`, `∇ u` is Evans's gradient vector `Du`, and the derivative of the
gradient is his Hessian matrix `D²u`.

## Main results

* `contDiffAt_gradient`, `contDiff_top_gradient`, `continuous_gradient_of_contDiff`: the
  gradient of a `C^(m+1)` function is `C^m`.
* `inner_fderiv_gradient_at`: `⟪D(∇ u)(x) v, w⟫ = D²u(x)(v, w)` at a point where `u` is `C²`.
* `HasCompactSupport.gradient`: the gradient of a compactly supported function is compactly
  supported.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix A.3, Notation for derivatives, (iv)(e), p. 701.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

noncomputable section

namespace PDE.Analysis

open scoped ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Riesz representation preserves the local smoothness of the derivative. -/
theorem contDiffAt_gradient {m : ℕ∞} {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ((m : ℕ∞ω) + 1) u x) :
    ContDiffAt ℝ m (∇ u) x := by
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact R.contDiff.contDiffAt.comp x (hu.fderiv_right le_rfl)

/-- The gradient of a smooth real functional is smooth. -/
theorem contDiff_top_gradient {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (∇ u) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ contDiffAt_gradient (m := ⊤) hu.contDiffAt

/-- The gradient of a continuously differentiable real functional is continuous. -/
theorem continuous_gradient_of_contDiff {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (∇ u) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (contDiffAt_gradient (m := 0) (by simpa using hu.contDiffAt (x := x))).continuousAt

/-- At a `C²` point, differentiating the gradient gives the Hessian bilinear form. -/
theorem inner_fderiv_gradient_at {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    ⟪fderiv ℝ (∇ u) x v, w⟫ = fderiv ℝ (fderiv ℝ u) x v w := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have h : HasFDerivAt (∇ u) (R.comp (fderiv ℝ (fderiv ℝ u) x)) x :=
    R.hasFDerivAt.comp x hdu.hasFDerivAt
  rw [h.fderiv]
  exact InnerProductSpace.toDual_symm_apply

end PDE.Analysis

/-- The gradient of a compactly supported real functional is compactly supported. -/
protected theorem HasCompactSupport.gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {u : E → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (∇ u) :=
  (hu.fderiv (𝕜 := ℝ)).comp_left (map_zero (InnerProductSpace.toDual ℝ E).symm)
