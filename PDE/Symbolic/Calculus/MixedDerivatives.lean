/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Symbolic.Calculus.EuclideanOperators
import PDE.FDeriv.Calculus

/-!
# Mixed coordinate derivatives of verified expressions

A word of coordinate directions specifies a mixed derivative of an expression
on `ℝ^n`. Its head is the outermost derivative, as in `iteratedPartialDeriv`.
Validity of each intermediate expression supplies the analytic derivative
identity; the final expression need not itself be differentiated.

This extends the one-variable `iteratedDerivWithin_univariateEval_eq` of
`IteratedDifferentiation` to arbitrary coordinate words.

## Main definitions and results

* `mixedDiff expr word`: the symbolic derivative along a word, outermost direction first.
* `ValidMixedAt expr word x`: validity of every differentiated intermediate expression.
* `iteratedPartialDeriv_eval`: `iteratedPartialDeriv word (eval expr) x` is
  `(mixedDiff expr word).eval x` under `ValidMixedAt`.
-/

@[expose] public section

namespace CAS.Verified.Expr

open PDE
open scoped Topology

/-- Symbolically differentiate in the order used by `iteratedPartialDeriv`. -/
def mixedDiff {n : ℕ} (expr : Expr (Fin n)) : List (Fin n) → Expr (Fin n)
  | [] => expr
  | i :: rest => (mixedDiff expr rest).diff i

/-- Every intermediate expression that is differentiated must be analytically valid.
The final value need not itself be differentiated. -/
def ValidMixedAt {n : ℕ} (expr : Expr (Fin n)) :
    List (Fin n) → ℝ^n → Prop
  | [], _ => True
  | _ :: rest, x => ValidMixedAt expr rest x ∧ (mixedDiff expr rest).ValidAt x

/-- The finite collection of analytic validity conditions holds on a neighborhood. -/
theorem ValidMixedAt.eventually {n : ℕ} {expr : Expr (Fin n)}
    {indices : List (Fin n)} {x : ℝ^n} (h : ValidMixedAt expr indices x) :
    ∀ᶠ y in 𝓝 x, ValidMixedAt expr indices y := by
  induction indices generalizing x with
  | nil => exact Filter.Eventually.of_forall fun _ ↦ trivial
  | cons i rest ih =>
      exact (ih h.1).and ((mixedDiff expr rest).eventually_validAt x h.2)

/-- Evaluation of the symbolic derivative word equals the actual mixed partial derivative. -/
theorem iteratedPartialDeriv_eval {n : ℕ} (expr : Expr (Fin n))
    (indices : List (Fin n)) (x : ℝ^n) (hvalid : ValidMixedAt expr indices x) :
    iteratedPartialDeriv indices (fun y : ℝ^n ↦ expr.eval y) x =
      (mixedDiff expr indices).eval x := by
  induction indices generalizing x with
  | nil => rfl
  | cons i rest ih =>
      have heq :
          (fun y : ℝ^n ↦ iteratedPartialDeriv rest (fun p : ℝ^n ↦ expr.eval p) y)
            =ᶠ[𝓝 x] (fun y : ℝ^n ↦ (mixedDiff expr rest).eval y) := by
        filter_upwards [hvalid.1.eventually] with y hy
        exact ih y hy
      exact (partialDeriv_congr_nhds i heq).trans
        ((mixedDiff expr rest).partialDeriv_eval_eq x i hvalid.2)

end CAS.Verified.Expr
