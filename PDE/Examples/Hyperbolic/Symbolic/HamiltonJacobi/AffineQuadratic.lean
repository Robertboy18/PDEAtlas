/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.ExactTactic
public import PDE.Common.Euclidean
public import PDE.Symbolic.Calculus.EuclideanOperators
public import PDE.Symbolic.ClosedForm.Differential.Equation

/-!
# An affine solution of a quadratic Hamilton-Jacobi equation

In spacetime coordinates `(t, x)`, the profile `u(t, x) = x - t` satisfies
`u_t + (u_x)^2 = 0`. It is given here as a symbolic expression. The same solution in
ordinary notation is `HamiltonJacobi1D.affineQuadraticSolution_satisfiesPDEProblem`.
-/

@[expose] public section

open PDE (partialDeriv)

namespace HamiltonJacobi1D.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2

noncomputable section

/--
Affine classical solution `u(t,x)=x-t`.

In the two-coordinate symbolic convention, `x` is time and `y` is the spatial
coordinate, so the expression is `y - x`.
-/
def affineQuadraticHamiltonianAnsatz : Verified.Expr (Fin 2) :=
  y - x

end

end HamiltonJacobi1D.Symbolic
