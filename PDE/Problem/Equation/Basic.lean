/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Data.Set.Defs

/-!
# Residual data for PDE problems

A `PDEEquation` stores an operator, right-hand side, and domain. A `PDEProblem`
collects finitely many such equations and designated side conditions.

The input, field, and residual codomains are arbitrary types. Regularity, traces, and weak
formulations enter through the operators and solution classes used to build these records.

The satisfaction predicate is defined in `PDE.Problem.Equation.Satisfaction`.

Compare Evans, §1.1: a `k`th-order PDE there is an expression `F(Dᵏu, ..., Du, u, x) = 0` on an
open set `U`, (1), and a system is the vector-valued form (2). A `PDEEquation` instead stores
the operator and the right-hand side separately and allows any domain, and the side conditions
of a `PDEProblem` play the role of the auxiliary boundary conditions mentioned after (1).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §1.1, Definitions (1) and (2), pp. 1-2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

universe uE uF uG

namespace PDE

/-- One equation `P u = g` on a specified domain.

The residual codomain is stored in the equation, so a single problem may combine equations with
different output types. -/
structure PDEEquation (E : Type uE) (F : Type uF) where
  /-- Codomain in which this equation is evaluated. -/
  Output : Type uG
  /-- Differential or residual operator. -/
  operator : (E → F) → E → Output
  /-- Right-hand side. -/
  rhs : E → Output
  /-- Set on which the equation is imposed. -/
  domain : Set E

/-- A finite collection of residual equations and designated side conditions. -/
structure PDEProblem (E : Type uE) (F : Type uF) where
  /-- Interior equations. -/
  eqns : List (PDEEquation.{uE, uF, uG} E F)
  /-- Initial, boundary, normalization, or other designated side equations. -/
  sideConditions : List (PDEEquation.{uE, uF, uG} E F)

end PDE
