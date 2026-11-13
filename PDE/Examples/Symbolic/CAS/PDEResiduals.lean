/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Symbolic.Helmholtz
public import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.Stationary
public import PDE.Examples.Hyperbolic.Symbolic.HamiltonJacobi.AffineQuadratic
public import PDE.Examples.Hyperbolic.Symbolic.Wave.TravelingSine
public import PDE.Parabolic.Symbolic.Heat.Gaussian
public import CAS.CEGA
public import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Exact symbolic PDE residuals

The first section checks that `cega` transports certificates to set-builder domains written
with `Set.Icc` or with reordered inequalities.

The last two sections apply `cas` to statements about imported checked-expression
constants: the Hamilton-Jacobi residual and the differentiability of the affine
Hamilton-Jacobi ansatz, stated through `Verified.Expr.eval`, and the stationary Cole-Hopf
residual of the Burgers equation, whose denominators are sums of exponentials and so are
structurally nonzero.
-/

@[expose] public section

namespace PDE.Examples.SymbolicPDE

open CAS
open CAS.Certificate

/-! ## Ordinary theorem domains -/

/-- Generated CEGA certificates transport to ordinary one-dimensional set-builder domains. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0)
      {p : ℝ^1 | p 0 ∈ Set.Icc (0 : ℝ) 1} 0 1 := by
  cega [enclose x in [0, 1]] x

/-- Equivalent reordered inequalities require no public interval, route, or registry object. -/
example :
    BoundOn (fun p : ℝ^2 ↦ p 1 * p 0)
      {p : ℝ^2 | p 1 ≤ 3 ∧ 0 ≤ p 0 ∧ 2 ≤ p 1 ∧ p 0 ≤ 1} 4 := by
  cega [enclose x in [0, 1], y in [2, 3]] (x * y)

/-! ## Imported checked-expression constants

A closed checked expression under the evaluator, such as an imported constant of type
`Verified.Expr _` or a lowered residual, is read back from one kernel evaluation, replaced by
its explicit constructor tree with a kernel-certified equation, and unfolded to ordinary real
syntax before the derivative and identity routes reflect the goal. Imported definitions of
real functions stay folded. -/

/-- The Hamilton-Jacobi residual `u_t + (u_x)^2 = 0` of the imported ansatz, as a sum of two
ordinary partial derivatives (`PDE.Hyperbolic.HamiltonJacobi.Quadratic.AffineSolution`). -/
example (p : ℝ^2) :
    (∂[(0 : Fin 2)]
        (fun q : SpaceTime 1 ↦
          HamiltonJacobi1D.Symbolic.affineQuadraticHamiltonianAnsatz.eval q)) p +
      ((∂[(1 : Fin 2)]
        (fun q : SpaceTime 1 ↦
          HamiltonJacobi1D.Symbolic.affineQuadraticHamiltonianAnsatz.eval q)) p) ^ 2 = 0 := by
  cas

/-- Differentiability of the imported ansatz on `ℝ^2`. -/
example (p : ℝ^2) :
    DifferentiableAt ℝ
      (fun q : SpaceTime 1 ↦
        HamiltonJacobi1D.Symbolic.affineQuadraticHamiltonianAnsatz.eval q) p := by
  cas

/-! ## The stationary Cole-Hopf residual

`coleHopfStationaryBurgersResidual` is the lowered residual of the unit-viscosity Burgers
equation at the velocity `-2 + 4 / (exp (2 y) + 1)`
(`PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.Stationary`). Its denominators are sums of
exponentials, which the structural sign checker proves nonzero, so the side-conditioned
pipeline is certified by one kernel evaluation and no hypothesis is needed. -/

/-- The reflected residual vanishes at every point. -/
example (p : ℝ^2) :
    BurgersEquation.ColeHopf.coleHopfStationaryBurgersResidual.eval p = 0 := by
  cas

/-- The same residual as a semantic zero statement. -/
example :
    Set.EqOn
      (Exact.exprFn BurgersEquation.ColeHopf.coleHopfStationaryBurgersResidual)
      Exact.zeroFn Set.univ := by
  cas

end PDE.Examples.SymbolicPDE
