/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import PDE.FDeriv.PartialDeriv
public import PDE.Notation.Divergence

/-!
# Differential operators

Advection, divergence, and the coordinate Laplacian on `ℝ^n`.

Scalar gradients use Mathlib's `gradient` directly. The theorem
`gradient_apply_eq_partialDeriv` identifies its coordinates with LeanPDE's
`partialDeriv`, so no second gradient definition is needed.

Use `open scoped Gradient Laplacian` for `∇ f x` and `Δ f x`.
The gradient and `Δ` notations are Mathlib's. The shared global notation `∇· F`
selects the coordinate divergence defined here for ordinary vector fields,
and `∂[i] f` selects their coordinate partial derivatives.
Each notation returns a function before evaluation at `x`.
The coordinate Laplacian retains the explicit spelling `PDE.laplacian`.

Like the underlying `partialDeriv`, these operators are total Lean expressions.
The coordinate operator `PDE.laplacian` is the iterated-coordinate expression
`∑ i, ∂ᵢ (∂ᵢ f)`, whereas Mathlib's canonical `Laplacian.laplacian` is defined from the total
second Fréchet derivative. The two need not agree on nonsmooth functions;
`ContDiffAt.coordinate_laplacian_eq_laplacian` proves equality under local `C²` regularity.

For vector fields, `PDE.inner_fderiv_apply_eq_sum` writes `a · (Dφ(x) b)` in coordinates, and
`PDE.laplacian_apply_of_contDiff` computes the coordinate Laplacian of a `C²` field
componentwise.

For `C²` functions, `PDE.laplacian` is `Δu = Σ u_{xᵢxᵢ}` of Evans, Appendix A, notation for
derivatives (v), and `PDE.divergence` is `div u = Σ uⁱ_{xᵢ}` of Appendix A.4 (iii). With a
constant field `b`, `advectiveDerivative` gives the term `b · Du` of the transport equation
(1) in Evans, §2.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.1, (1), p. 18, and Appendix A, notation for
  derivatives (v), p. 701, and A.4 (iii), p. 703.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

variable {n : ℕ}

open PDE
open scoped Gradient Laplacian RealInnerProductSpace

namespace PDE

/-- The `i`th coordinate of Mathlib's gradient is LeanPDE's `i`th partial derivative.

Both sides are total expressions built from `fderiv`. Reading them as classical derivatives
requires the usual differentiability hypothesis. -/
@[simp]
theorem gradient_apply_eq_partialDeriv
    (f : ℝ^n → ℝ) (x : ℝ^n) (i : Fin n) :
    ∇ f x i = (∂[i] f) x := by
  rw [← EuclideanSpace.inner_basisFun_real (Fin n) (∇ f x) i,
    inner_gradient_left]
  simp only [partialDeriv, EuclideanSpace.basisFun_apply]

/-- Applying the Fréchet derivative in the `i`th coordinate direction gives the `i`th
coordinate of the gradient. -/
theorem fderiv_apply_single_one_eq_gradient_apply
    (f : ℝ^n → ℝ) (x : ℝ^n) (i : Fin n) :
    (fderiv ℝ f x) (EuclideanSpace.single i (1 : ℝ)) = ∇ f x i := by
  rw [gradient_apply_eq_partialDeriv]
  rfl

/-- Advective derivative of a field `f` along a velocity field `u`.

At `x`, this is the Fréchet derivative of `f` applied to the local velocity
`u x`. The codomain is arbitrary, so the same operator covers transported
scalars and vector-valued momentum equations. As with `fderiv`, this is a
total Lean term. It is the classical directional derivative only where `f`
is differentiable. -/
noncomputable def advectiveDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ^n → ℝ^n) (f : ℝ^n → E) (x : ℝ^n) : E :=
  fderiv ℝ f x (u x)

/-- Divergence of a vector field, `∑ᵢ ∂ᵢ Fᵢ`.

Each scalar component is differentiated using the total `fderiv` expression.
Differentiability of the components at `x` gives the classical divergence there.
The trace formula for the derivative of the whole field requires differentiability of `F`;
without that hypothesis, these two total expressions need not agree. -/
noncomputable def divergence (F : ℝ^n → ℝ^n)
    (x : ℝ^n) : ℝ :=
  ∑ i : Fin n, partialDeriv (n := n) i (fun y ↦ F y i) x

/-- For an ordinary Euclidean vector field, the shared divergence notation selects
the coordinate divergence. Its classical interpretation requires differentiability. -/
noncomputable instance _root_.instDivergenceEuclidean :
    PDE.Divergence (ℝ^n → ℝ^n) (ℝ^n → ℝ) where
  divergence := PDE.divergence

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Display classical divergence, retaining the target type of ordinary coercions.
The notation infers its operator from the input, so `↑` needs this type even when
the classical divergence would have supplied it. Function coercions `⇑` infer their own type. -/
@[delab app.PDE.divergence]
public meta def delabDivergence : Delab := whenPPOption getPPNotation do
  guard <| !(← getPPOption getPPExplicit)
  withOverApp 2 do
    let v ← withAppArg do
      let e := (← getExpr).consumeMData
      let needsType ← match e.getAppFn with
        | .const name _ => do
          let info ← Meta.getCoeFnInfo? name
          pure (info.any (fun info ↦ info.type matches .coe))
        | _ => pure false
      withTypeAscription delab (cond := needsType)
    `(∇· $v)

end PDE

/-- The coordinate Laplacian, `∑ᵢ ∂ᵢ(∂ᵢ f)`, of a map into a real normed space.

The same definition covers scalar fields, vector fields, and complex-valued functions.

This is a total Lean term, and on nonsmooth functions it can differ from Mathlib's
canonical `Laplacian.laplacian`. They agree for `C²` functions by
`ContDiffAt.coordinate_laplacian_eq_laplacian`. -/
noncomputable def PDE.laplacian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ^n → E) (x : ℝ^n) : E :=
  ∑ i : Fin n, partialDeriv (n := n) i (fun y ↦ partialDeriv (n := n) i f y) x

namespace EuclideanLaplacian

private theorem coordinate_laplacian_eq_laplacian_of_differentiableAt_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ^n → E) (x : ℝ^n)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    laplacian f x = Δ f x := by
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (EuclideanSpace.basisFun (Fin n) ℝ)) x]
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [secondPartialDeriv_eq_fderiv i i hf, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.basisFun_apply]

end EuclideanLaplacian

/-- Under local `C²` regularity, the coordinate Laplacian agrees with Mathlib's canonical
Laplacian. -/
theorem ContDiffAt.coordinate_laplacian_eq_laplacian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x) :
    laplacian f x = Δ f x :=
  EuclideanLaplacian.coordinate_laplacian_eq_laplacian_of_differentiableAt_fderiv f x
    ((hf.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)).differentiableAt
      (by norm_num))

namespace PDE

/-- The coordinate Laplacian is the divergence of Mathlib's gradient. -/
theorem laplacian_eq_divergence_gradient
    (f : ℝ^n → ℝ) (x : ℝ^n) :
    laplacian (n := n) f x = ∇· (∇ f) x := by
  unfold laplacian divergence
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext y
  exact (gradient_apply_eq_partialDeriv f y i).symm

/-! ### Vector calculus identities -/

/-- The gradient of a sum is the sum of the gradients at a common differentiability point. -/
theorem gradient_add_of_differentiableAt (f g : ℝ^n → ℝ) (x : ℝ^n)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ∇ (f + g) x = ∇ f x + ∇ g x := by
  ext i
  simp only [WithLp.ofLp_add, Pi.add_apply, gradient_apply_eq_partialDeriv]
  change (∂[i] (fun y ↦ f y + g y)) x = _
  exact partialDeriv_add hf hg

end PDE

/-! ### Coordinate formulas for vector fields -/

namespace PDE

/-- Coordinate form of the pairing `a · (Dφ(x) b) = Σᵢⱼ aᵢ bⱼ ∂ⱼφᵢ(x)` at a point where `φ`
is differentiable. -/
theorem inner_fderiv_apply_eq_sum {φ : ℝ^n → ℝ^n} {x : ℝ^n}
    (hφ : DifferentiableAt ℝ φ x) (a b : ℝ^n) :
    ⟪a, fderiv ℝ φ x b⟫ = ∑ i, ∑ j, a i * b j * (∂[j] (fun y ↦ φ y i)) x := by
  rw [fderiv_apply_eq_sum_smul_partialDeriv, inner_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_smul_right, PiLp.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [partialDeriv_apply j i hφ, RCLike.inner_apply, conj_trivial]
  ring

/-- For a twice differentiable vector field, each component of the coordinate Laplacian is the
coordinate Laplacian of that component. -/
theorem laplacian_apply_of_contDiff {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ 2 φ) (x : ℝ^n)
    (i : Fin n) : laplacian φ x i = laplacian (fun y ↦ φ y i) x := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hdk (k : Fin n) : Differentiable ℝ (∂[k] φ) :=
    (hφ.partialDeriv k (k := 1)).differentiable (by norm_num)
  unfold laplacian
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [partialDeriv_apply k i (hdk k x)]
  congr 1
  funext y
  exact partialDeriv_apply k i (hd y)

end PDE
