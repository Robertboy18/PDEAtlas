/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus
public import CAS.Calculus.SymbolicOperators
public import PDE.Symbolic.Calculus.EuclideanOperators
public import CAS.Calculus.FDeriv
public import CAS.Calculus.Gradient

/-!
# Symbolic differential operators

The symbolic gradient, divergence, curl, and Laplacian of
`CAS.Calculus.SymbolicOperators` evaluate to the analytic operators of
`PDE.FDeriv`. The gradient, divergence, and curls are built from the checked partial
derivative `closedPartial`
(the symbolic derivative followed by normalization); the Laplacian applies the raw symbolic
derivative `diff` twice in each coordinate and normalizes the sum. In every case the derivative
formulas themselves come from `Verified.Expr.diff`.

The bridge theorems hold at points where the differentiated expressions are valid
(`Verified.Expr.ValidAt`): denominators and logarithm arguments nonzero, square-root arguments
positive, inverse sine and cosine arguments different from `±1`. The Laplacian additionally
needs validity of the first symbolic partials at the point, since it differentiates them again.

## Main results

* `closedDivergence_eval_eq_divergence`, `closedLaplacian_eval_eq_laplacian`: agreement with
  the analytic `divergence` and `laplacian` at valid points; the gradient theorem
  `closedGradient_eval_eq_gradient` is in `CAS.Calculus.Gradient`.
* `closedCurl2_eval_eq_partialDeriv`, `closedCurl3_zero_eval_eq_partialDeriv` and its two
  companions: the curl formulas in terms of `partialDeriv`, since `PDE.FDeriv` has no curl
  operator.
* `secondPartial_eval_eq_partialDeriv_diff`, `mixedSecondPartial_eval_eq_partialDeriv_diff`:
  at a point where `expr` is valid, the analytic second partial of `eval expr` equals the
  analytic partial of `eval (expr.diff j)`. Symbolic Hessians and second-order residuals are
  built on this.
-/

@[expose] public section

namespace CAS

open PDE
open scoped BigOperators Gradient

namespace Verified.Expr

/--
At a point where the expression is valid, an outer analytic partial `∂ᵢ` of the analytic
partial `∂ⱼ u` agrees with `∂ᵢ` of the raw symbolic partial `expr.diff j`.

Validity holds on a neighborhood of `x`, where the inner partials agree, so the outer partial
sees the same function locally. Symbolic Hessian entries use this.
-/
theorem mixedSecondPartial_eval_eq_partialDeriv_diff {n : Nat}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n) (i j : Fin n)
    (hvalid : expr.ValidAt x) :
    (∂[i]
        (fun y : ℝ^n ↦
          (∂[j] (fun z : ℝ^n ↦ expr.eval z)) y))
        x =
      (∂[i]
        (fun y : ℝ^n ↦ (expr.diff j).eval y))
        x := by
  apply partialDeriv_congr_nhds
  filter_upwards [eventually_validAt expr x hvalid] with y hy
  have h :=
    closedPartial_eval_eq_partialDeriv
      (expr := expr) (x := y) (i := j) hy
  simpa [closedPartial, eval_trigSimplify] using h.symm

/--
At a point where the expression is valid, the analytic second coordinate partial agrees
with differentiating the raw symbolic first partial.

Symbolic residuals store the first derivative as `expr.diff i`, while analytic
PDE statements write second derivatives as iterated `partialDeriv`; this
identifies the two. It is the diagonal case `j = i` of
`mixedSecondPartial_eval_eq_partialDeriv_diff`.
-/
theorem secondPartial_eval_eq_partialDeriv_diff {n : Nat}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n)
    (hvalid : expr.ValidAt x) :
    (∂[i]
        (fun y : ℝ^n ↦
          (∂[i] (fun z : ℝ^n ↦ expr.eval z)) y))
        x =
      (∂[i]
        (fun y : ℝ^n ↦ (expr.diff i).eval y))
        x :=
  mixedSecondPartial_eval_eq_partialDeriv_diff expr x i i hvalid

/-- Symbolic divergence agrees with the analytic coordinate divergence for vector fields whose
components are denoted by valid symbolic expressions. -/
theorem closedDivergence_eval_eq_divergence {n : Nat}
    (field : Fin n → Verified.Expr (Fin n)) (x : ℝ^n)
    (h : ∀ i : Fin n, (field i).ValidAt x) :
  (closedDivergence field).eval x =
      ∇· (fun y : ℝ^n ↦
        WithLp.toLp 2 (fun i : Fin n ↦ (field i).eval y)) x := by
  unfold closedDivergence
  rw [eval_simplify]
  rw [eval_sumFin]
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  change (closedPartial i (field i)).eval x =
    (∂[i]
      (fun y : ℝ^n ↦
        (WithLp.toLp 2 (fun j : Fin n ↦ (field j).eval y) :
          ℝ^n) i)) x
  rw [closedPartial_eval_eq_partialDeriv (expr := field i) (x := x) (i := i) (h i)]

/-- Symbolic two-dimensional scalar curl agrees with its analytic partial-derivative formula.

`PDE.FDeriv` has no curl operator, so the theorem states `∂ₓ F_y - ∂ᵧ F_x` directly in
terms of `partialDeriv`. -/
theorem closedCurl2_eval_eq_partialDeriv {field : Fin 2 → Verified.Expr (Fin 2)}
    (x : ℝ^2)
    (h : ∀ i : Fin 2, (field i).ValidAt x) :
    (closedCurl2 field).eval x =
    (∂[(0 : Fin 2)] (fun y : ℝ^2 ↦ (field 1).eval y)) x -
      (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ (field 0).eval y)) x := by
  have : Fact (0 < 2) := ⟨by decide⟩
  unfold closedCurl2
  change (simplify (closedPartial (0 : Fin 2) (field 1) -
      closedPartial (1 : Fin 2) (field 0))).eval x =
    (∂[(0 : Fin 2)] (fun y : ℝ^2 ↦ (field 1).eval y)) x -
      (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ (field 0).eval y)) x
  rw [eval_simplify]
  change
    (closedPartial (0 : Fin 2) (field 1)).eval x -
        (closedPartial (1 : Fin 2) (field 0)).eval x =
      (∂[(0 : Fin 2)]
          (fun y : ℝ^2 ↦ (field 1).eval y)) x -
        (∂[(1 : Fin 2)]
          (fun y : ℝ^2 ↦ (field 0).eval y)) x
  rw [closedPartial_eval_eq_partialDeriv (expr := field 1) (x := x) (i := (0 : Fin 2)) (h 1)]
  rw [closedPartial_eval_eq_partialDeriv (expr := field 0) (x := x) (i := (1 : Fin 2)) (h 0)]

/-- First component of the symbolic three-dimensional curl, transported to analytic partial
derivatives: `(curl F)_x = ∂ᵧ F_z - ∂ᶻ F_y`. -/
theorem closedCurl3_zero_eval_eq_partialDeriv {field : Fin 3 → Verified.Expr (Fin 3)}
    (x : ℝ^3)
    (h : ∀ i : Fin 3, (field i).ValidAt x) :
    (closedCurl3 field 0).eval x =
      (∂[(1 : Fin 3)] (fun y : ℝ^3 ↦ (field 2).eval y)) x -
        (∂[(2 : Fin 3)] (fun y : ℝ^3 ↦ (field 1).eval y)) x := by
  have : Fact (0 < 3) := ⟨by decide⟩
  unfold closedCurl3
  change (simplify (closedPartial (1 : Fin 3) (field 2) -
      closedPartial (2 : Fin 3) (field 1))).eval x =
    (∂[(1 : Fin 3)] (fun y : ℝ^3 ↦ (field 2).eval y)) x -
      (∂[(2 : Fin 3)] (fun y : ℝ^3 ↦ (field 1).eval y)) x
  rw [eval_simplify]
  change
    (closedPartial (1 : Fin 3) (field 2)).eval x -
        (closedPartial (2 : Fin 3) (field 1)).eval x =
      (∂[(1 : Fin 3)]
          (fun y : ℝ^3 ↦ (field 2).eval y)) x -
        (∂[(2 : Fin 3)]
          (fun y : ℝ^3 ↦ (field 1).eval y)) x
  rw [closedPartial_eval_eq_partialDeriv (expr := field 2) (x := x) (i := (1 : Fin 3)) (h 2)]
  rw [closedPartial_eval_eq_partialDeriv (expr := field 1) (x := x) (i := (2 : Fin 3)) (h 1)]

/-- Second component of the symbolic three-dimensional curl, transported to analytic partial
derivatives: `(curl F)_y = ∂ᶻ F_x - ∂ₓ F_z`. -/
theorem closedCurl3_one_eval_eq_partialDeriv {field : Fin 3 → Verified.Expr (Fin 3)}
    (x : ℝ^3)
    (h : ∀ i : Fin 3, (field i).ValidAt x) :
    (closedCurl3 field 1).eval x =
      (∂[(2 : Fin 3)] (fun y : ℝ^3 ↦ (field 0).eval y)) x -
        (∂[(0 : Fin 3)] (fun y : ℝ^3 ↦ (field 2).eval y)) x := by
  have : Fact (0 < 3) := ⟨by decide⟩
  unfold closedCurl3
  change (simplify (closedPartial (2 : Fin 3) (field 0) -
      closedPartial (0 : Fin 3) (field 2))).eval x =
    (∂[(2 : Fin 3)] (fun y : ℝ^3 ↦ (field 0).eval y)) x -
      (∂[(0 : Fin 3)] (fun y : ℝ^3 ↦ (field 2).eval y)) x
  rw [eval_simplify]
  change
    (closedPartial (2 : Fin 3) (field 0)).eval x -
        (closedPartial (0 : Fin 3) (field 2)).eval x =
      (∂[(2 : Fin 3)]
          (fun y : ℝ^3 ↦ (field 0).eval y)) x -
        (∂[(0 : Fin 3)]
          (fun y : ℝ^3 ↦ (field 2).eval y)) x
  rw [closedPartial_eval_eq_partialDeriv (expr := field 0) (x := x) (i := (2 : Fin 3)) (h 0)]
  rw [closedPartial_eval_eq_partialDeriv (expr := field 2) (x := x) (i := (0 : Fin 3)) (h 2)]

/-- Third component of the symbolic three-dimensional curl, transported to analytic partial
derivatives: `(curl F)_z = ∂ₓ F_y - ∂ᵧ F_x`. -/
theorem closedCurl3_two_eval_eq_partialDeriv {field : Fin 3 → Verified.Expr (Fin 3)}
    (x : ℝ^3)
    (h : ∀ i : Fin 3, (field i).ValidAt x) :
    (closedCurl3 field 2).eval x =
      (∂[(0 : Fin 3)] (fun y : ℝ^3 ↦ (field 1).eval y)) x -
        (∂[(1 : Fin 3)] (fun y : ℝ^3 ↦ (field 0).eval y)) x := by
  have : Fact (0 < 3) := ⟨by decide⟩
  unfold closedCurl3
  change (simplify (closedPartial (0 : Fin 3) (field 1) -
      closedPartial (1 : Fin 3) (field 0))).eval x =
    (∂[(0 : Fin 3)] (fun y : ℝ^3 ↦ (field 1).eval y)) x -
      (∂[(1 : Fin 3)] (fun y : ℝ^3 ↦ (field 0).eval y)) x
  rw [eval_simplify]
  change
    (closedPartial (0 : Fin 3) (field 1)).eval x -
        (closedPartial (1 : Fin 3) (field 0)).eval x =
      (∂[(0 : Fin 3)]
          (fun y : ℝ^3 ↦ (field 1).eval y)) x -
        (∂[(1 : Fin 3)]
          (fun y : ℝ^3 ↦ (field 0).eval y)) x
  rw [closedPartial_eval_eq_partialDeriv (expr := field 1) (x := x) (i := (0 : Fin 3)) (h 1)]
  rw [closedPartial_eval_eq_partialDeriv (expr := field 0) (x := x) (i := (1 : Fin 3)) (h 0)]

/-- At a point where the expression and its first symbolic partials are valid, evaluating the
checked symbolic Laplacian agrees with the analytic Laplacian. -/
theorem closedLaplacian_eval_eq_laplacian {n : Nat}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n)
    (h0 : expr.ValidAt x) (h1 : ∀ i : Fin n, (expr.diff i).ValidAt x) :
    (closedLaplacian expr).eval x =
      laplacian (fun y : ℝ^n ↦ expr.eval y) x := by
  change
    (Verified.Expr.eval (fun i : Fin n ↦ x i)
      (trigSimplify (sumFin fun i : Fin n ↦
        trigSimplify ((expr.diff i).diff i)))) =
      laplacian (fun y : ℝ^n ↦ expr.eval y) x
  rw [eval_trigSimplify]
  change (sumFin fun i : Fin n ↦ trigSimplify ((expr.diff i).diff i)).eval x =
    laplacian (fun y : ℝ^n ↦ expr.eval y) x
  rw [eval_sumFin]
  rw [Verified.Expr.laplacian_eval_eq (expr := expr) (x := x) h0 h1]
  apply Finset.sum_congr rfl
  intro i _
  simp [eval_trigSimplify]

end Verified.Expr

end CAS
