/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Operator
public import PDE.Hyperbolic.Symbolic.Wave.Equation
public import PDE.Examples.Hyperbolic.Symbolic.Transport.RightMovingSine
public import CAS.ExactTactic

/-!
# A traveling sine wave

The right-moving profile `u(t, x) = sin(x - t)` is a d'Alembert solution `F(x - t)` of the
one-dimensional wave equation `u_tt - u_xx = 0`; both second derivatives equal `-sin(x - t)`
and cancel. In the symbolic convention of this directory the first coordinate `x` is time
and the second `y` is space, so the ansatz is written `sin (y - x)`.

The symbolic residual of the profile vanishes identically. This transfers to the analytic
residual built from Euclidean partial derivatives, and the profile satisfies the
`WaveEquation.waveEquation` problem on all of `ℝ^2`.

## Main results

* `travelingWave1DResidual`: the compiled residual of the shared right-moving profile
  `rightMovingSineAnsatz` under `travelingWave1DEquation`.
* `travelingWave1D_residual_bound`, `travelingWave1D_residual_eq_zero`: the symbolic residual
  vanishes identically.
* `travelingWave1D_analyticResidual_zero`: the analytic residual vanishes, with side
  conditions from `travelingWave1D_analytic_side_condition` (none are needed for a sine of an
  affine argument).
* `travelingWave1D_waveOperator_zero`: `WaveEquation.waveOperator` of the profile is `0` at
  every point.
* `travelingWave1D_is_solution_waveEquation`: the bundled `SatisfiesPDEProblem` statement.

## Implementation notes

Second derivatives are obtained by applying the Euclidean partial to the checked first
derivative (`Verified.Expr.secondPartial_eval_eq_partialDeriv_diff`), which needs validity of
the ansatz at the evaluation point.
-/

@[expose] public section

open PDE (SatisfiesPDEProblem)

namespace WaveEquation.Symbolic

open TransportEquation.Symbolic (rightMovingSineAnsatz)

open CAS
open CAS.Certificate
open CAS.Euclid2
open scoped CAS

noncomputable section

/-- The symbolic residual of `sin(x - t)` under `u_tt - u_xx = 0`. -/
def travelingWave1DResidual : Verified.Expr (Fin 2) :=
  Scalar.residual travelingWave1DEquation rightMovingSineAnsatz

/-- The symbolic residual is bounded by `0` on all of spacetime. -/
theorem travelingWave1D_residual_bound :
    ResidualBound
      (fun p : ℝ^2 ↦ travelingWave1DResidual.eval fun i ↦ p i)
      Set.univ 0 := by
  cas

/-- The symbolic residual vanishes on all of spacetime. -/
theorem travelingWave1D_residual_eq_zero :
    Set.EqOn (fun p : ℝ^2 ↦ travelingWave1DResidual.eval fun i ↦ p i)
      (fun _ : ℝ^2 ↦ (0 : ℝ)) Set.univ :=
  eqOn_zero_of_residualBound_zero travelingWave1D_residual_bound

/-- The profile has no analytic side conditions. -/
theorem travelingWave1D_analytic_side_condition
    (p : ℝ^2) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz rightMovingSineAnsatz) p travelingWave1DEquation.residual := by
  apply DiffExpr.analyticSideCondition_of_requirements
  refine Verified.Expr.ValidityRequirements.holds_of_eq
    (computed := { nonzero := [], positive := [] }) ?_ ?_
  · rfl
  · simp [Verified.Expr.ValidityRequirements.Holds]

/-- The analytic residual of the profile vanishes at every point. -/
theorem travelingWave1D_analyticResidual_zero :
    ∀ p, p ∈ Set.univ →
      DiffExpr.Equation.analyticResidual
        (Scalar.ansatz rightMovingSineAnsatz) p travelingWave1DEquation = 0 := by
  intro p hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    (by
      change travelingWave1DResidual.eval p = 0
      exact travelingWave1D_residual_eq_zero hp)
    (travelingWave1D_analytic_side_condition p)

/-- The wave operator of `sin(x - t)` vanishes at every point. -/
theorem travelingWave1D_waveOperator_zero
    (p : ℝ^2) :
    WaveEquation.waveOperator (n := 1)
      (fun q : ℝ^2 ↦ rightMovingSineAnsatz.eval q) p = 0 := by
  have hvalid : rightMovingSineAnsatz.ValidAt p := by
    unfold rightMovingSineAnsatz
    symbolic_assumptions
  have ht :
      (∂[(0 : Fin 2)]
          (fun y : ℝ^2 ↦
            (∂[(0 : Fin 2)]
              (fun q : ℝ^2 ↦ rightMovingSineAnsatz.eval q)) y))
          p =
        (∂[(0 : Fin 2)]
          (fun y : ℝ^2 ↦ (rightMovingSineAnsatz.diff 0).eval y))
          p :=
    Verified.Expr.secondPartial_eval_eq_partialDeriv_diff
      rightMovingSineAnsatz p (0 : Fin 2) hvalid
  have hx :
      (∂[(1 : Fin 2)]
          (fun y : ℝ^2 ↦
            (∂[(1 : Fin 2)]
              (fun q : ℝ^2 ↦ rightMovingSineAnsatz.eval q)) y))
          p =
        (∂[(1 : Fin 2)]
          (fun y : ℝ^2 ↦ (rightMovingSineAnsatz.diff 1).eval y))
          p :=
    Verified.Expr.secondPartial_eval_eq_partialDeriv_diff
      rightMovingSineAnsatz p (1 : Fin 2) hvalid
  rw [WaveEquation.waveOperator, ht]
  rw [Fintype.sum_unique]
  change
    (∂[(0 : Fin 2)]
        (fun y : ℝ^2 ↦ (rightMovingSineAnsatz.diff 0).eval y))
        p -
      (∂[(1 : Fin 2)]
        (fun y : ℝ^2 ↦
          (∂[(1 : Fin 2)]
            (fun q : ℝ^2 ↦ rightMovingSineAnsatz.eval q)) y))
        p =
      0
  rw [hx]
  have htvalid : (rightMovingSineAnsatz.diff (0 : Fin 2)).ValidAt p := by
    unfold rightMovingSineAnsatz
    symbolic_assumptions
  have hxvalid : (rightMovingSineAnsatz.diff (1 : Fin 2)).ValidAt p := by
    unfold rightMovingSineAnsatz
    symbolic_assumptions
  have hdt := Verified.Expr.partialDeriv_eval_eq
    (expr := rightMovingSineAnsatz.diff (0 : Fin 2)) (x := p) (i := (0 : Fin 2)) htvalid
  have hdx := Verified.Expr.partialDeriv_eval_eq
    (expr := rightMovingSineAnsatz.diff (1 : Fin 2)) (x := p) (i := (1 : Fin 2)) hxvalid
  rw [hdt, hdx]
  simp [rightMovingSineAnsatz, Verified.Expr.diff, Verified.Expr.eval,
    Verified.Expr.SymVar.expr]

/-- `sin(x - t)` solves the wave equation on all of `ℝ^2`. -/
theorem travelingWave1D_is_solution_waveEquation :
    SatisfiesPDEProblem
      (WaveEquation.waveEquation (n := 1) Set.univ)
      (fun q : ℝ^2 ↦ rightMovingSineAnsatz.eval q) := by
  apply WaveEquation.nonhomogeneousWaveEquation.of_residual (n := 1)
  intro p _hp
  exact travelingWave1D_waveOperator_zero p
end

end WaveEquation.Symbolic
