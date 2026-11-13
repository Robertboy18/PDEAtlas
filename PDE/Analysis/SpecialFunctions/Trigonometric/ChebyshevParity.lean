/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Odd Chebyshev polynomials

Chebyshev polynomials of both kinds of odd degree are odd functions, and the derivative of an
odd real polynomial is an even function.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Polynomial

/-- Chebyshev polynomials of the first kind of odd degree are odd functions. -/
theorem eval_neg_chebyshevT_two_mul_add_one (j : ℕ) (c : ℝ) :
    (Chebyshev.T ℝ (2 * (j : ℤ) + 1)).eval (-c) = -(Chebyshev.T ℝ (2 * (j : ℤ) + 1)).eval c := by
  rw [Chebyshev.T_eval_neg, Int.negOnePow_odd _ (odd_two_mul_add_one _)]
  simp

/-- Chebyshev polynomials of the second kind of odd degree are odd functions. -/
theorem eval_neg_chebyshevU_two_mul_add_one (l : ℕ) (c : ℝ) :
    (Chebyshev.U ℝ (2 * (l : ℤ) + 1)).eval (-c) = -(Chebyshev.U ℝ (2 * (l : ℤ) + 1)).eval c := by
  have hcast : (2 * (l : ℤ) + 1) = ((2 * l + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, Chebyshev.U_eval_neg,
    Int.negOnePow_odd _ (by rw [← hcast]; exact odd_two_mul_add_one _)]
  simp

/-- The derivative of an odd real polynomial is an even function. -/
theorem derivative_eval_neg_of_odd {P : ℝ[X]} (hP : ∀ c, P.eval (-c) = -P.eval c) (c : ℝ) :
    P.derivative.eval (-c) = P.derivative.eval c := by
  have h1 : HasDerivAt (fun y ↦ P.eval (-y)) (P.derivative.eval (-c) * -1) c :=
    (P.hasDerivAt (-c)).comp c (hasDerivAt_neg c)
  have h2 : (fun y ↦ P.eval (-y)) = fun y ↦ -P.eval y := funext hP
  rw [h2] at h1
  have := h1.unique (P.hasDerivAt c).fun_neg
  linarith

end PDE.Analysis
