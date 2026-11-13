/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.IntervalEnclosure
public import CAS.Polynomial.Sparse.Semantics
public import CAS.Polynomial.Horner

/-!
# Checked conversion of spline branches to Horner form

The sparse rational normalizer compares two polynomial expressions exactly.
Success identifies their real values everywhere, so external coefficient conversion
is only a proposal: the kernel checks the conversion before interval evaluation.
Horner evaluation can substantially reduce cancellation and repeated dependence
compared with the original Cox–de Boor expression.
-/

@[expose] public section
namespace CAS.Splines
open CAS.Verified CAS.Polynomial

/-- Horner expression with coefficients in ascending order of degree. -/
def hornerExpr {ι : Type*} (argument : Expr ι) : List ℚ → Expr ι
  | [] => .nat 0
  | coefficient :: rest =>
      .add (Expr.mkRatConst coefficient) (.mul argument (hornerExpr argument rest))

/-- The expression implements the library's ordinary real Horner evaluator. -/
theorem hornerExpr_eval {ι : Type*} (argument : Expr ι) (coefficients : List ℚ) (ρ : ι → ℝ) :
    (hornerExpr argument coefficients).eval ρ =
      listHornerEval (argument.eval ρ) (coefficients.map Rat.cast) := by
  induction coefficients with
  | nil => simp [hornerExpr, Expr.eval]
  | cons a rest ih =>
      simp [hornerExpr, Expr.eval, ih, mul_comm, add_comm]

/-- Compare successful canonical polynomial normalizations; unsupported inputs fail closed. -/
def polynomialIdentityCheck {n : ℕ} (left right : Expr (Fin n)) : Bool :=
  match Expr.Alg.mvNormalizeExpr? left, Expr.Alg.mvNormalizeExpr? right with
  | some a, some b => decide (a = b)
  | _, _ => false

/-- A successful executable polynomial comparison proves equality of real expressions. -/
theorem polynomialIdentityCheck_sound {n : ℕ} (left right : Expr (Fin n))
    (hcheck : polynomialIdentityCheck left right = true) (x : ℝ^n) :
    left.eval x = right.eval x := by
  unfold polynomialIdentityCheck at hcheck
  cases hl : Expr.Alg.mvNormalizeExpr? left with
  | none => simp [hl] at hcheck
  | some a =>
      cases hr : Expr.Alg.mvNormalizeExpr? right with
      | none => simp [hr] at hcheck
      | some b =>
          have hab : a = b := by simpa [hl, hr] using hcheck
          calc
            left.eval x = a.eval x := (Expr.Alg.eval_mvNormalizeExpr?_eq x hl).symm
            _ = b.eval x := congrArg (fun expr : Expr (Fin n) ↦ expr.eval x) hab
            _ = right.eval x := Expr.Alg.eval_mvNormalizeExpr?_eq x hr

/-- Check coefficients for a branch expanded around an exact rational center. -/
def branchHornerCheck (q : ℕ → ℚ) (cell degree index : ℕ)
    (center : ℚ) (coefficients : List ℚ) : Bool :=
  polynomialIdentityCheck (branchExpr q (0 : Fin 1) cell degree index)
    (hornerExpr (.sub (.var 0) (Expr.mkRatConst center)) coefficients)

/-- Kernel-checked coefficients in Horner form denote the original real spline branch. -/
theorem branchHornerCheck_sound (q : ℕ → ℚ) (knots : KnotSequence)
    (hknots : ∀ i, knots i = (q i : ℝ)) (cell degree index : ℕ)
    (center : ℚ) (coefficients : List ℚ)
    (hcheck : branchHornerCheck q cell degree index center coefficients = true) (x : ℝ) :
    listHornerEval (x - (center : ℝ)) (coefficients.map Rat.cast) =
      coxDeBoorBranch knots cell degree index x := by
  have h := polynomialIdentityCheck_sound _ _ hcheck (WithLp.toLp 2 (fun _ : Fin 1 ↦ x))
  simpa [branchExpr_eval q (0 : Fin 1) _ knots hknots, hornerExpr_eval, Expr.eval] using h.symm

end CAS.Splines
