/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.ClosedForm.Differential.Requirements
public import PDE.Symbolic.Calculus.Operators -- shake: keep

/-!
# Semantics of symbolic differential expressions

A closed-form ansatz has two related interpretations. `analyticEval` uses Lean's Euclidean
derivatives, while `lower` produces an executable symbolic expression. The main theorem proves
that these interpretations agree wherever the extracted analytic requirements hold.

`semanticEval` extends the same differential language to arbitrary Lean functions, including
functions defined by integrals or infinite series that cannot be reflected into `Verified.Expr`.

## Main definitions

* `analyticEval`: evaluation of a `DiffExpr` after substituting a symbolic ansatz, where
  `pderiv` and `laplacian` denote the library's Euclidean `partialDeriv` and `laplacian`
  (defined in `PDE.FDeriv`, distinct from Mathlib's `Laplacian.laplacian`).
* `semanticEval`: the same interpretation with the unknowns assigned arbitrary functions
  `ℝ^n → ℝ`.

## Main results

* `analyticEval_eq_lower_eval`: under `AnalyticSideCondition`, analytic evaluation equals the
  real evaluation of the lowered symbolic expression. This is the theorem that lets a purely
  symbolic residual computation certify an analytic PDE identity.

## Implementation notes

In `analyticEval` the derivative nodes differentiate the *lowered* operand, that is
`fun y => (lower ansatz a).eval y`, rather than `fun y => analyticEval ansatz y a`. The two
functions coincide wherever the side conditions hold, and this choice keeps the induction in
`analyticEval_eq_lower_eval` local to one node: each derivative case reduces to the soundness
theorem of the symbolic differentiator (`closedPartial_eval_eq_partialDeriv`,
`closedLaplacian_eval_eq_laplacian`) applied to the lowered operand. `semanticEval`, which has no
symbolic lowering available, differentiates its own recursive interpretation instead.

`AnalyticSideCondition` asks for `ValidAt` of the lowered operand at each derivative node (and of
its first derivatives at each Laplacian node); this is exactly what the symbolic differentiation
soundness theorems require, and nothing is asked at nodes without derivatives.
-/

@[expose] public section

namespace CAS

namespace DiffExpr

/-- Interpret differential nodes using Lean's Euclidean derivative operators after substituting a
closed-form ansatz for every unknown field. -/
noncomputable def analyticEval {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) : DiffExpr n σ → ℝ
  | .atom expr => expr.eval x
  | .unknown u => (ansatz u).eval x
  | .add a b => analyticEval ansatz x a + analyticEval ansatz x b
  | .mul a b => analyticEval ansatz x a * analyticEval ansatz x b
  | .sub a b => analyticEval ansatz x a - analyticEval ansatz x b
  | .div a b => analyticEval ansatz x a / analyticEval ansatz x b
  | .neg a => -(analyticEval ansatz x a)
  | .pow a k => analyticEval ansatz x a ^ k
  | .sin a => Real.sin (analyticEval ansatz x a)
  | .cos a => Real.cos (analyticEval ansatz x a)
  | .atan a => Real.arctan (analyticEval ansatz x a)
  | .asin a => Real.arcsin (analyticEval ansatz x a)
  | .acos a => Real.arccos (analyticEval ansatz x a)
  | .exp a => Real.exp (analyticEval ansatz x a)
  | .log a => Real.log (analyticEval ansatz x a)
  | .sqrt a => Real.sqrt (analyticEval ansatz x a)
  | .pderiv i a => (∂[i] (fun y : ℝ^n ↦ (lower ansatz a).eval y)) x
  | .laplacian a => PDE.laplacian (fun y : ℝ^n ↦ (lower ansatz a).eval y) x

/-- Analytic evaluation is additive on formal sums. -/
@[simp] theorem analyticEval_add {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (a b : DiffExpr n σ) :
    analyticEval ansatz x (a + b) = analyticEval ansatz x a + analyticEval ansatz x b :=
  rfl

/-- Analytic evaluation is multiplicative on formal products. -/
@[simp] theorem analyticEval_mul {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (a b : DiffExpr n σ) :
    analyticEval ansatz x (a * b) = analyticEval ansatz x a * analyticEval ansatz x b :=
  rfl

/-- Analytic evaluation commutes with formal subtraction. -/
@[simp] theorem analyticEval_sub {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (a b : DiffExpr n σ) :
    analyticEval ansatz x (a - b) = analyticEval ansatz x a - analyticEval ansatz x b :=
  rfl

/-- Analytic evaluation commutes with formal division (real division, so `x / 0 = 0`). -/
@[simp] theorem analyticEval_div {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (a b : DiffExpr n σ) :
    analyticEval ansatz x (a / b) = analyticEval ansatz x a / analyticEval ansatz x b :=
  rfl

/-- Analytic evaluation commutes with formal negation. -/
@[simp] theorem analyticEval_neg {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (a : DiffExpr n σ) :
    analyticEval ansatz x (-a) = -analyticEval ansatz x a :=
  rfl

/-- Analytic evaluation commutes with formal natural powers. -/
@[simp] theorem analyticEval_pow {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (a : DiffExpr n σ) (k : Nat) :
    analyticEval ansatz x (a ^ k) = analyticEval ansatz x a ^ k :=
  rfl

/-- `D v a` evaluates to the Euclidean partial derivative in coordinate `v.idx` of the real
function defined by the lowered operand `lower ansatz a`. -/
@[simp] theorem analyticEval_D {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n)
    (v : Verified.Expr.SymVar n) (a : DiffExpr n σ) :
    analyticEval ansatz x (D v a) =
      (∂[v.idx] (fun y : ℝ^n ↦ (lower ansatz a).eval y)) x :=
  rfl

/-- `Lap a` evaluates to the Euclidean Laplacian of the real function defined by the lowered
operand `lower ansatz a`. -/
@[simp] theorem analyticEval_Lap {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (a : DiffExpr n σ) :
    analyticEval ansatz x (Lap a) =
      PDE.laplacian (fun y : ℝ^n ↦ (lower ansatz a).eval y) x :=
  rfl

/-- Interpret a differential expression under arbitrary Lean-function ansatzes.

Unlike `analyticEval`, this interpretation does not require the unknown fields to have symbolic
representatives. Differential nodes still denote actual Euclidean derivatives. -/
noncomputable def semanticEval {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) : DiffExpr n σ → ℝ
  | .atom expr => expr.eval x
  | .unknown u => ansatz u x
  | .add a b => semanticEval ansatz x a + semanticEval ansatz x b
  | .mul a b => semanticEval ansatz x a * semanticEval ansatz x b
  | .sub a b => semanticEval ansatz x a - semanticEval ansatz x b
  | .div a b => semanticEval ansatz x a / semanticEval ansatz x b
  | .neg a => -(semanticEval ansatz x a)
  | .pow a k => semanticEval ansatz x a ^ k
  | .sin a => Real.sin (semanticEval ansatz x a)
  | .cos a => Real.cos (semanticEval ansatz x a)
  | .atan a => Real.arctan (semanticEval ansatz x a)
  | .asin a => Real.arcsin (semanticEval ansatz x a)
  | .acos a => Real.arccos (semanticEval ansatz x a)
  | .exp a => Real.exp (semanticEval ansatz x a)
  | .log a => Real.log (semanticEval ansatz x a)
  | .sqrt a => Real.sqrt (semanticEval ansatz x a)
  | .pderiv i a => (∂[i] (fun y : ℝ^n ↦ semanticEval ansatz y a)) x
  | .laplacian a => PDE.laplacian (fun y : ℝ^n ↦ semanticEval ansatz y a) x

/-- An unknown field evaluates to the assigned function at the point. -/
@[simp] theorem semanticEval_unknown {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) (u : σ) :
    semanticEval ansatz x (.unknown u) = ansatz u x :=
  rfl

/-- Semantic evaluation is additive on formal sums. -/
@[simp] theorem semanticEval_add {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) (a b : DiffExpr n σ) :
    semanticEval ansatz x (a + b) = semanticEval ansatz x a + semanticEval ansatz x b :=
  rfl

/-- Semantic evaluation is multiplicative on formal products. -/
@[simp] theorem semanticEval_mul {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) (a b : DiffExpr n σ) :
    semanticEval ansatz x (a * b) = semanticEval ansatz x a * semanticEval ansatz x b :=
  rfl

/-- Semantic evaluation commutes with formal subtraction. -/
@[simp] theorem semanticEval_sub {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) (a b : DiffExpr n σ) :
    semanticEval ansatz x (a - b) = semanticEval ansatz x a - semanticEval ansatz x b :=
  rfl

/-- Semantic evaluation commutes with formal division (real division, so `x / 0 = 0`). -/
@[simp] theorem semanticEval_div {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) (a b : DiffExpr n σ) :
    semanticEval ansatz x (a / b) = semanticEval ansatz x a / semanticEval ansatz x b :=
  rfl

/-- Semantic evaluation commutes with formal negation. -/
@[simp] theorem semanticEval_neg {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) (a : DiffExpr n σ) :
    semanticEval ansatz x (-a) = -semanticEval ansatz x a :=
  rfl

/-- Semantic evaluation commutes with formal natural powers. -/
@[simp] theorem semanticEval_pow {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) (a : DiffExpr n σ) (k : Nat) :
    semanticEval ansatz x (a ^ k) = semanticEval ansatz x a ^ k :=
  rfl

/-- `D v a` evaluates to the Euclidean partial derivative in coordinate `v.idx` of the function
`y ↦ semanticEval ansatz y a`. -/
@[simp] theorem semanticEval_D {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n)
    (v : Verified.Expr.SymVar n) (a : DiffExpr n σ) :
    semanticEval ansatz x (D v a) =
      (∂[v.idx] (fun y : ℝ^n ↦ semanticEval ansatz y a)) x :=
  rfl

/-- `Lap a` evaluates to the Euclidean Laplacian of the function `y ↦ semanticEval ansatz y a`. -/
@[simp] theorem semanticEval_Lap {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) (a : DiffExpr n σ) :
    semanticEval ansatz x (Lap a) =
      PDE.laplacian (fun y : ℝ^n ↦ semanticEval ansatz y a) x :=
  rfl

/-- Analytic evaluation agrees with symbolic lowering wherever all required operations are valid.

The hypothesis `AnalyticSideCondition ansatz x e` collects, node by node, the `ValidAt`
conditions under which the symbolic differentiator is known to compute the true Euclidean
derivative of the lowered operand; away from those points the two sides may differ (for
example at a zero of a denominator, where `Verified.Expr.eval` uses totalized division). -/
theorem analyticEval_eq_lower_eval {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (e : DiffExpr n σ)
    (h : AnalyticSideCondition ansatz x e) :
    analyticEval ansatz x e = (lower ansatz e).eval x := by
  induction e with
  | atom expr => simp [analyticEval, lower]
  | unknown u => simp [analyticEval, lower]
  | add a b ha hb =>
      rcases h with ⟨haS, hbS⟩
      simp [analyticEval, lower, ha haS, hb hbS]
  | mul a b ha hb =>
      rcases h with ⟨haS, hbS⟩
      simp [analyticEval, lower, ha haS, hb hbS]
  | sub a b ha hb =>
      rcases h with ⟨haS, hbS⟩
      simp [analyticEval, lower, ha haS, hb hbS]
  | div a b ha hb =>
      rcases h with ⟨haS, hbS⟩
      simp [analyticEval, lower, ha haS, hb hbS]
  | neg a ha => simp [analyticEval, lower, ha h]
  | pow a _ ha => simp [analyticEval, lower, ha h]
  | sin a ha => simp [analyticEval, lower, ha h]
  | cos a ha => simp [analyticEval, lower, ha h]
  | atan a ha => simp [analyticEval, lower, ha h]
  | asin a ha => simp [analyticEval, lower, ha h]
  | acos a ha => simp [analyticEval, lower, ha h]
  | exp a ha => simp [analyticEval, lower, ha h]
  | log a ha => simp [analyticEval, lower, ha h]
  | sqrt a ha => simp [analyticEval, lower, ha h]
  | pderiv i a _ha =>
      rcases h with ⟨_haS, hvalid⟩
      simpa [analyticEval, lower, Verified.Expr.closedPartial] using
        (Verified.Expr.closedPartial_eval_eq_partialDeriv
          (expr := lower ansatz a) (x := x) (i := i) hvalid).symm
  | laplacian a _ha =>
      rcases h with ⟨_haS, hvalid, hfirst⟩
      simpa [analyticEval, lower] using
        (Verified.Expr.closedLaplacian_eval_eq_laplacian
          (expr := lower ansatz a) (x := x) hvalid hfirst).symm

end DiffExpr

end CAS
