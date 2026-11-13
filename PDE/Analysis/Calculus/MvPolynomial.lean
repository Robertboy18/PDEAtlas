/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Coordinate derivatives of multivariable polynomials

Algebraic partial differentiation agrees with differentiation of polynomial
evaluation along a coordinate line.
-/

@[expose] public section

namespace MvPolynomial

variable {ι : Type*} [DecidableEq ι]

/-- Polynomial evaluation along a coordinate line has the algebraic partial derivative. -/
theorem hasDerivAt_eval_update (P : MvPolynomial ι ℝ) (x : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun s ↦ eval (Function.update x i s) P)
      (eval (Function.update x i t) (pderiv i P)) t := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [pderiv_C, map_zero, eval_C] using hasDerivAt_const t c
  | add P Q hP hQ =>
    simpa only [map_add] using! HasDerivAt.add hP hQ
  | mul_X P j hP =>
    by_cases h : j = i
    · subst j
      simpa only [pderiv_mul, pderiv_X_self, eval_add, eval_mul, eval_X, map_one,
        Function.update_self, mul_one, id_eq] using! hP.mul (hasDerivAt_id t)
    · simpa only [pderiv_mul, pderiv_X_of_ne h, eval_add, eval_mul, eval_X, map_zero,
        mul_zero, add_zero, Function.update_of_ne h] using hP.mul_const (x j)

variable [Finite ι]

/-- The Fréchet derivative of polynomial evaluation on a coordinate vector is the
evaluation of its algebraic partial derivative. -/
theorem fderiv_eval_single (P : MvPolynomial ι ℝ) (x : ι → ℝ) (i : ι) :
    fderiv ℝ (fun y ↦ eval y P) x (Pi.single i 1) = eval x (pderiv i P) := by
  let := Fintype.ofFinite ι
  have hP := (AnalyticOnNhd.eval_mvPolynomial P x (Set.mem_univ x)).differentiableAt
  have hd := hP.hasFDerivAt.comp_hasDerivAt_of_eq (x i)
    (hasDerivAt_update x i (x i)) (by simp)
  simpa only [Function.update_eq_self] using hd.unique (P.hasDerivAt_eval_update x i (x i))

end MvPolynomial
