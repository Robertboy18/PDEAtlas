/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Calculus.Derivation
public import CAS.Calculus.Euclidean
public import CAS.Calculus.Partial
public import PDE.FDeriv.Operators

/-!
# PDE operator bridges for checked expressions

At a point where a checked expression is valid, its symbolic derivatives compute the
analytic operators of `PDE.FDeriv.Operators`:

* `partialDeriv_eval_eq`: the coordinate derivative `∂[i]` is evaluation of `expr.diff i`;
* `closedPartial_eval_eq_partialDeriv`: the same for the simplified partial `closedPartial`;
* `laplacian_eval_eq`: the Laplacian is the sum of evaluated second symbolic partials, given
  validity of `expr` and of its first partials at the point;
* `DiffDerivation.partialDeriv_eq_eval_rawDerivative` and
  `DiffDerivation.partialDeriv_eq_eval_simplifiedDerivative`: the derivatives displayed by a
  derivation tree are the coordinate derivative `∂[i]`.

This module imports `PDE.FDeriv.Operators`; the definitions of the symbolic operators do not.
-/

@[expose] public section

namespace CAS

open PDE
open scoped BigOperators Gradient Topology

namespace Verified.Expr

/--
The analytic `i`-th partial derivative of expression evaluation equals evaluation of the
symbolic partial derivative `expr.diff i`.
-/
theorem partialDeriv_eval_eq {n : ℕ}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n)
    (h : expr.ValidAt x) :
    (∂[i] (fun y : ℝ^n ↦ expr.eval y)) x = (expr.diff i).eval x := by
  simp only [partialDeriv]
  rw [fderiv_eval_eq expr x h]
  exact symbolicFDeriv_apply_single_eq_diff_eval expr x i

/--
The Laplacian of expression evaluation is the sum of its evaluated symbolic second partial
derivatives, provided the expression and every first symbolic derivative are valid at `x`.
-/
theorem laplacian_eval_eq {n : ℕ}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n)
    (h0 : expr.ValidAt x) (h1 : ∀ i : Fin n, (expr.diff i).ValidAt x) :
    laplacian (fun y : ℝ^n ↦ expr.eval y) x =
      ∑ i : Fin n, ((expr.diff i).diff i).eval x := by
  classical
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  -- Validity persists near `x`, so the first analytic partial derivative agrees locally
  -- with evaluation of the first symbolic derivative.
  have hEq :
      (fun y : ℝ^n ↦ (∂[i] (fun z : ℝ^n ↦ expr.eval z)) y) =ᶠ[𝓝 x]
        (fun y : ℝ^n ↦ (expr.diff i).eval y) := by
    filter_upwards [eventually_validAt expr x h0] with y hy
    exact partialDeriv_eval_eq (expr := expr) (x := y) (i := i) hy
  have hfderivEq :
      fderiv ℝ (fun y : ℝ^n ↦ (∂[i] (fun z : ℝ^n ↦ expr.eval z)) y) x =
        fderiv ℝ (fun y : ℝ^n ↦ (expr.diff i).eval y) x := by
    -- Fréchet derivatives depend only on the germ of a function at the base point.
    exact (hEq.fderiv.eq_of_nhds)
  -- The bridge applied to `expr.diff i` computes the second coordinate derivative.
  have hSecond :
      (∂[i] (fun y : ℝ^n ↦ (expr.diff i).eval y)) x =
        ((expr.diff i).diff i).eval x :=
    partialDeriv_eval_eq (expr := (expr.diff i)) (x := x) (i := i) (h1 i)
  have hOuter :
      (∂[i]
          (fun y : ℝ^n ↦
            (∂[i] (fun z : ℝ^n ↦ expr.eval z)) y)) x =
        (∂[i] (fun y : ℝ^n ↦ (expr.diff i).eval y)) x := by
    -- Unfold only the outer coordinate derivative, exposing the two locally equal
    -- Fréchet derivatives without changing the inner partial derivative.
    change (fderiv ℝ
        (fun y : ℝ^n ↦
          (∂[i] (fun z : ℝ^n ↦ expr.eval z)) y) x)
            (EuclideanSpace.single i (1 : ℝ)) =
          (fderiv ℝ (fun y : ℝ^n ↦ (expr.diff i).eval y) x) (EuclideanSpace.single i (1 : ℝ))
    exact congrArg (fun L ↦ L (EuclideanSpace.single i (1 : ℝ))) hfderivEq
  exact hOuter.trans hSecond

/-- At a valid point, a checked symbolic partial evaluates to the analytic coordinate
derivative. -/
theorem closedPartial_eval_eq_partialDeriv {n : Nat}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n)
    (h : expr.ValidAt x) :
    (closedPartial i expr).eval x =
      (∂[i] (fun y : ℝ^n ↦ expr.eval y)) x := by
  rw [closedPartial, eval_trigSimplify]
  exact (partialDeriv_eval_eq (expr := expr) (x := x) (i := i) h).symm

namespace DiffDerivation

/-- A derivation node computes the analytic Euclidean partial derivative at every valid point. -/
theorem partialDeriv_eq_eval_rawDerivative {n : Nat}
    {i : Fin n} {input output : Verified.Expr (Fin n)}
    (derivation : DiffDerivation i input output) (x : ℝ^n)
    (hvalid : input.ValidAt x) :
    (∂[i] (fun y : ℝ^n ↦ input.eval y)) x =
      derivation.rawDerivative.eval x :=
  derivation.fderiv_apply_single_eq_eval_rawDerivative x hvalid

/-- The simplified derivative projection computes the same analytic Euclidean partial derivative. -/
theorem partialDeriv_eq_eval_simplifiedDerivative {n : Nat}
    {i : Fin n} {input output : Verified.Expr (Fin n)}
    (derivation : DiffDerivation i input output) (x : ℝ^n)
    (hvalid : input.ValidAt x) :
    (∂[i] (fun y : ℝ^n ↦ input.eval y)) x =
      derivation.simplifiedDerivative.eval x :=
  derivation.fderiv_apply_single_eq_eval_simplifiedDerivative x hvalid

end DiffDerivation

end Verified.Expr

end CAS
