/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Calculus.TensorOperators
public import PDE.Symbolic.Calculus.Operators

/-!
# Analytic semantics of symbolic tensor operators

At a point where the differentiated expressions are valid, the operators of
`CAS.Calculus.TensorOperators` evaluate to their analytic formulas:

* `hessian_eval_eq_mixedSecondPartial`: the `(i, j)` Hessian entry is `∂ᵢ ∂ⱼ (eval u)`, given
  validity of `u` and of the checked partial `∂ⱼ u` at the point;
* `jacobian_eval_eq_partialDeriv`: the `(i, j)` Jacobian entry is `∂ⱼ Fᵢ`;
* `symmetricGradient_eval_eq_partialDeriv_average`: the small-strain tensor
  `(∂ⱼ Fᵢ + ∂ᵢ Fⱼ)/2`;
* `tensorDivergence_eval_eq_sum_partialDeriv`: the row-wise divergence `∑ⱼ ∂ⱼ Aᵢⱼ`;
* `vectorLaplacian_eval_eq_laplacian`: each component of the vector Laplacian is the
  Laplacian of that component, given validity of the component and its first partials.
-/

@[expose] public section

namespace CAS

open PDE
open scoped BigOperators

/-- A symbolic Hessian entry evaluates to the corresponding mixed analytic partial derivative. -/
theorem hessian_eval_eq_mixedSecondPartial {n : Nat}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n) (i j : Fin n)
    (houter : (Verified.Expr.closedPartial j expr).ValidAt x)
    (hvalid : expr.ValidAt x) :
    (hessian expr i j).eval x =
      (∂[i]
        (fun y : ℝ^n ↦
          (∂[j] (fun z : ℝ^n ↦ expr.eval z)) y))
        x := by
  unfold hessian
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k)
        (Verified.Expr.closedPartial i (Verified.Expr.closedPartial j expr)) =
      (∂[i]
        (fun y : ℝ^n ↦
          (∂[j] (fun z : ℝ^n ↦ expr.eval z)) y))
        x
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := Verified.Expr.closedPartial j expr) (x := x) (i := i) houter,
    Verified.Expr.mixedSecondPartial_eval_eq_partialDeriv_diff expr x i j hvalid]
  simp [Verified.Expr.closedPartial, Verified.Expr.eval_trigSimplify]

/-- A symbolic Jacobian entry evaluates to the corresponding analytic partial derivative. -/
theorem jacobian_eval_eq_partialDeriv {n m : Nat}
    (field : Fin m → Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin m) (j : Fin n)
    (h : (field i).ValidAt x) :
    (jacobian field i j).eval x =
      (∂[j] (fun y : ℝ^n ↦ (field i).eval y)) x := by
  unfold jacobian
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k) (Verified.Expr.closedPartial j (field i)) =
      (∂[j] (fun y : ℝ^n ↦ (field i).eval y)) x
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := field i) (x := x) (i := j) h]

/-- A symbolic symmetric-gradient entry evaluates to the average of its analytic partials. -/
theorem symmetricGradient_eval_eq_partialDeriv_average {n : Nat}
    (field : Fin n → Verified.Expr (Fin n)) (x : ℝ^n) (i j : Fin n)
    (h : ∀ k : Fin n, (field k).ValidAt x) :
    (symmetricGradient field i j).eval x =
      ((∂[j] (fun y : ℝ^n ↦ (field i).eval y)) x +
        (∂[i] (fun y : ℝ^n ↦ (field j).eval y)) x) / 2 := by
  unfold symmetricGradient
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k)
        (Verified.Expr.Alg.normalize
          ((Verified.Expr.closedPartial j (field i) +
              Verified.Expr.closedPartial i (field j)) / 2)) =
      ((∂[j]
          (fun y : ℝ^n ↦ (field i).eval y)) x +
        (∂[i]
          (fun y : ℝ^n ↦ (field j).eval y)) x) / 2
  rw [Verified.Expr.Alg.eval_normalize]
  change
    ((Verified.Expr.closedPartial j (field i)).eval x +
        (Verified.Expr.closedPartial i (field j)).eval x) / 2 =
      ((∂[j]
          (fun y : ℝ^n ↦ (field i).eval y)) x +
        (∂[i]
          (fun y : ℝ^n ↦ (field j).eval y)) x) / 2
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := field i) (x := x) (i := j) (h i)]
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := field j) (x := x) (i := i) (h j)]

/-- Symbolic row-wise divergence evaluates to the sum `∑ⱼ ∂ⱼ Aᵢⱼ`. -/
theorem tensorDivergence_eval_eq_sum_partialDeriv {n : Nat}
    (A : Fin n → Fin n → Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n)
    (h : ∀ j : Fin n, (A i j).ValidAt x) :
    (tensorDivergence A i).eval x =
      ∑ j : Fin n,
        (∂[j] (fun y : ℝ^n ↦ (A i j).eval y)) x := by
  unfold tensorDivergence
  rw [Verified.Expr.Alg.eval_normalize]
  rw [Verified.Expr.eval_sumFin]
  apply Finset.sum_congr rfl
  intro j _
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := A i j) (x := x) (i := j) (h j)]

/-- Each symbolic vector-Laplacian component evaluates to its analytic Euclidean Laplacian. -/
theorem vectorLaplacian_eval_eq_laplacian {n : Nat}
    (u : Fin n → Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n)
    (h0 : (u i).ValidAt x) (h1 : ∀ j : Fin n, ((u i).diff j).ValidAt x) :
    (vectorLaplacian u i).eval x =
      laplacian (fun y : ℝ^n ↦ (u i).eval y) x := by
  simpa [vectorLaplacian] using
    Verified.Expr.closedLaplacian_eval_eq_laplacian
      (expr := u i) (x := x) h0 h1

end CAS
