/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.BranchHorner
public import CAS.Polynomial.Sparse.UnivariateCalculus

/-!
# Exact matching of polynomial jets

Horner coefficients are reflected into sparse rational polynomials, whose
formal derivative and rational evaluator compute the jets. Successful exact
comparison proves equality of the real iterated derivatives at the rational cut.
-/

@[expose] public section
namespace CAS.Splines
open CAS.Verified
open CAS.Polynomial

/-- Reflect an ascending Horner coefficient list into the shared sparse polynomial carrier. -/
def hornerPolynomial? (coefficients : List ℚ) : Option Sparse.Univariate :=
  Expr.Alg.mvPolyOf? (hornerExpr (.var (0 : Fin 1)) coefficients)

/-- Successful reflection preserves the real Horner function. -/
theorem hornerPolynomial?_eval (coefficients : List ℚ) (polynomial : Sparse.Univariate)
    (hpoly : hornerPolynomial? coefficients = some polynomial) (x : ℝ) :
    Sparse.evalReal polynomial x = listHornerEval x (coefficients.map Rat.cast) := by
  rw [Sparse.evalReal_eq_mvPolyVal]
  have h := Expr.Alg.mvPolyVal_eq_eval_of_mvPolyOf? (EuclideanSpace.single (0 : Fin 1) x)
    (hornerExpr (.var 0) coefficients) polynomial hpoly
  simpa [hornerExpr_eval, Expr.eval] using h

/-- Compare one exact rational jet of two proposed polynomial branches. -/
def hornerJetMatchCheck (left right : List ℚ) (cut : ℚ) (order : ℕ) : Bool :=
  match hornerPolynomial? left, hornerPolynomial? right with
  | some a, some b => decide
      (Sparse.evalRat ((Sparse.derivative (0 : Fin 1))^[order] a) cut =
        Sparse.evalRat ((Sparse.derivative (0 : Fin 1))^[order] b) cut)
  | _, _ => false

/-- Exact rational jet matching identifies iterated derivatives at the cut. -/
theorem hornerJetMatchCheck_sound (left right : List ℚ) (cut : ℚ) (order : ℕ)
    (hcheck : hornerJetMatchCheck left right cut order = true) :
    iteratedDeriv order (fun x : ℝ ↦ listHornerEval x (left.map Rat.cast)) (cut : ℝ) =
      iteratedDeriv order (fun x : ℝ ↦ listHornerEval x (right.map Rat.cast)) (cut : ℝ) := by
  unfold hornerJetMatchCheck at hcheck
  cases hl : hornerPolynomial? left with
  | none => simp [hl] at hcheck
  | some a =>
      cases hr : hornerPolynomial? right with
      | none => simp [hr] at hcheck
      | some b =>
          have hab : Sparse.evalRat ((Sparse.derivative (0 : Fin 1))^[order] a) cut =
              Sparse.evalRat ((Sparse.derivative (0 : Fin 1))^[order] b) cut := by
            simpa [hl, hr] using hcheck
          have hleft : (fun x : ℝ ↦ listHornerEval x (left.map Rat.cast)) =
              Sparse.evalReal a := funext fun x ↦ (hornerPolynomial?_eval left a hl x).symm
          have hright : (fun x : ℝ ↦ listHornerEval x (right.map Rat.cast)) =
              Sparse.evalReal b := funext fun x ↦ (hornerPolynomial?_eval right b hr x).symm
          rw [hleft, hright, Sparse.iteratedDeriv_evalReal, Sparse.iteratedDeriv_evalReal,
            Sparse.evalReal_ratCast, Sparse.evalReal_ratCast, hab]

end CAS.Splines
