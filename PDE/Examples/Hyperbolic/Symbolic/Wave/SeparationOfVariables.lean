/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Symbolic.Wave.Equation
public import CAS.ExactTactic
public import PDE.Symbolic.ClosedForm.Differential.Equation

/-!
# Symbolic separated wave mode

The separated mode `u(t,x) = sin(t) sin(x)` solves `u_tt - u_xx = 0`: both second
derivatives equal `-sin(t) sin(x)`. The symbolic residual vanishes, and so does the
analytic residual built from Euclidean partial derivatives.
-/

@[expose] public section

namespace WaveEquation.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2

noncomputable section

/--
The elementary separated wave mode `u(t,x)=sin(t) sin(x)`.
Symbolic `x` is time and symbolic `y` is space.
-/
def separatedWaveMode1DAnsatz : Verified.Expr (Fin 2) :=
  .sin (x : Verified.Expr (Fin 2)) *
    .sin (y : Verified.Expr (Fin 2))

/-- The symbolic wave residual of the separated mode. -/
def separatedWaveMode1DResidual : Verified.Expr (Fin 2) :=
  Scalar.residual travelingWave1DEquation separatedWaveMode1DAnsatz

private theorem separatedWaveMode1D_residual_bound :
    ResidualBound
      (fun p : ℝ^2 ↦ separatedWaveMode1DResidual.eval fun i ↦ p i)
      Set.univ 0 := by
  cas

/-- The symbolic residual vanishes identically. -/
theorem separatedWaveMode1D_closed_residual_eq_zero :
    Set.EqOn (fun p : ℝ^2 ↦ separatedWaveMode1DResidual.eval fun i ↦ p i)
      (fun _ : ℝ^2 ↦ (0 : ℝ)) Set.univ :=
  eqOn_zero_of_residualBound_zero separatedWaveMode1D_residual_bound

/-- The mode has no analytic side conditions. -/
private theorem separatedWaveMode1D_analytic_side_condition
    (p : ℝ^2) (_hp : p ∈ Set.univ) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz separatedWaveMode1DAnsatz)
      p
      WaveEquation.Symbolic.travelingWave1DEquation.residual := by
  apply DiffExpr.analyticSideCondition_of_requirements
  refine Verified.Expr.ValidityRequirements.holds_of_eq
    (computed := { nonzero := [], positive := [] }) ?_ ?_
  · rfl
  · simp [Verified.Expr.ValidityRequirements.Holds]

/-- The analytic residual of the mode vanishes at every point. -/
theorem separatedWaveMode1D_analytic_residual_eq_zero :
    ∀ p, p ∈ Set.univ →
      DiffExpr.Equation.analyticResidual
        (Scalar.ansatz separatedWaveMode1DAnsatz)
        p
        WaveEquation.Symbolic.travelingWave1DEquation = 0 := by
  intro p hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    (by
      change separatedWaveMode1DResidual.eval p = 0
      exact separatedWaveMode1D_closed_residual_eq_zero hp)
    (separatedWaveMode1D_analytic_side_condition p hp)

end

end WaveEquation.Symbolic
