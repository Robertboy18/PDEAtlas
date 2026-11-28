/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# The norm of a Hessian from its quadratic form

## Motivation

Do the quadratic-form bounds `θ |ξ|² ≤ D²L(p)(ξ, ξ) ≤ Λ |ξ|²` give the
operator-norm bound `‖D²L(p)‖ ≤ Λ` that the regularity theorems of the library ask for?

## The idea

It does, with the same constant. A symmetric positive semidefinite bilinear
form `B` satisfies the Cauchy–Schwarz inequality `B(ξ, η)² ≤ B(ξ, ξ) B(η, η)`. If
`B(ξ, ξ) ≤ Λ |ξ|²` for every `ξ`, the right side is at most `(Λ |ξ| |η|)²`, so
`|B(ξ, η)| ≤ Λ |ξ| |η|`. The Hessian of a `C²` function is symmetric, so this applies to it.

## Main results

* `opNorm_le_of_quadratic_le` (all symmetric positive semidefinite continuous bilinear forms
  on a real seminormed space): `B ξ ξ ≤ Λ ‖ξ‖²` for every `ξ` gives `‖B‖ ≤ Λ.toNNReal`.
* `norm_hessian_le_of_quadratic_le` (all real functions that are `C²` at a point of a real
  normed space): `θ ‖ξ‖² ≤ D²L(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for every `ξ`, with `θ ≥ 0`, gives
  `‖D²L(p)‖ ≤ Λ.toNNReal`.

The bound is `Λ.toNNReal = max Λ 0` and not `Λ`, so that no sign condition on `Λ` is needed.
The two agree as soon as the space has a vector of nonzero norm. On the zero space the norm
of every form is `0`, and the hypotheses hold for every real `Λ`.

## Relations

* The proof is Mathlib's `LinearMap.BilinForm.apply_sq_le_of_symm` with
  `ContinuousLinearMap.opNorm_le_bound₂`.
* `ContDiffAt.isSymmSndFDerivAt` gives the symmetry of the Hessian.
* `PDE.Analysis.lipschitzWith_gradient_of_hessian_bound` and the theorems of the modules under
  `PDE/Elliptic/Regularity/Quasilinear/Interior/HigherOrder/` take the norm bound proved here.
  `PDE.CalculusOfVariations.LocalMinimizer.Smooth` and
  `PDE.CalculusOfVariations.LocalMinimizer.Holder` use this module to state their theorems
  with the quadratic-form bounds.
* `PDE.Analysis.Operator.norm_le_of_abs_inner_le` is the analogous bound for a symmetric
  operator on a real inner product space, from the two-sided bound `|⟪f, T f⟫| ≤ t ‖f‖²`.

## What stays open

The form must be positive semidefinite. A symmetric form with `|B ξ ξ| ≤ Λ ‖ξ‖²` and no
sign condition is not treated here. On an inner product space,
`PDE.Analysis.Operator.norm_le_of_abs_inner_le` gives the bound for symmetric operators.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.3.1, for the growth condition `|D²L(p)| ≤ C` and
  the uniform convexity condition that the two bounds express.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open scoped NNReal

/-- A symmetric positive semidefinite continuous bilinear form `B` on a real seminormed
space with `B ξ ξ ≤ Λ ‖ξ‖²` for every `ξ` has operator norm at most `Λ.toNNReal`, which is
`max Λ 0`. The Cauchy–Schwarz inequality `B(ξ, η)² ≤ B(ξ, ξ) B(η, η)` bounds the mixed
values by the diagonal ones. -/
theorem opNorm_le_of_quadratic_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ ξ η, B ξ η = B η ξ) (hpos : ∀ ξ, 0 ≤ B ξ ξ)
    {Λ : ℝ} (hle : ∀ ξ, B ξ ξ ≤ Λ * ‖ξ‖ ^ 2) : ‖B‖ ≤ Λ.toNNReal := by
  have hm : (0 : ℝ) ≤ Λ.toNNReal := NNReal.coe_nonneg _
  have hdiag (ξ : E) : B ξ ξ ≤ Λ.toNNReal * ‖ξ‖ ^ 2 :=
    (hle ξ).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal Λ) (sq_nonneg _))
  refine B.opNorm_le_bound₂ hm fun ξ η ↦ ?_
  rw [Real.norm_eq_abs]
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc
    B ξ η ^ 2 ≤ B ξ ξ * B η η := B.toBilinForm.apply_sq_le_of_symm hpos ⟨hsymm⟩ ξ η
    _ ≤ (Λ.toNNReal * ‖ξ‖ ^ 2) * (Λ.toNNReal * ‖η‖ ^ 2) :=
      mul_le_mul (hdiag ξ) (hdiag η) (hpos η) (by positivity)
    _ = (Λ.toNNReal * ‖ξ‖ * ‖η‖) ^ 2 := by ring

/-- If `L` is `C²` at `p` and its Hessian there satisfies
`θ ‖ξ‖² ≤ D²L(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for every `ξ`, with `θ ≥ 0`, then
`‖D²L(p)‖ ≤ Λ.toNNReal`. The Hessian is symmetric, so this is `opNorm_le_of_quadratic_le`.
This turns the quadratic-form statement of ellipticity into the norm bound that the
regularity theorems use. With `θ = 0` the lower bound says that the Hessian is positive
semidefinite. -/
theorem norm_hessian_le_of_quadratic_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : E → ℝ} {p : E} (hL : ContDiffAt ℝ 2 L p) {θ Λ : ℝ} (hθ : 0 ≤ θ)
    (hlower : ∀ ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p ξ ξ)
    (hupper : ∀ ξ, fderiv ℝ (fderiv ℝ L) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2) :
    ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ.toNNReal :=
  opNorm_le_of_quadratic_le _ (fun ξ η ↦ (hL.isSymmSndFDerivAt (by simp)).eq ξ η)
    (fun ξ ↦ (mul_nonneg hθ (sq_nonneg _)).trans (hlower ξ)) hupper

end PDE.Analysis
