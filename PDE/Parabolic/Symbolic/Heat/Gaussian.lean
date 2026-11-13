/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Gaussian
public import PDE.Parabolic.Symbolic.Heat.Equations
public import PDE.Parabolic.Symbolic.Heat.SpatialSlice
public import PDE.Symbolic.ClosedForm.Tactic.Residual
public import CAS.ExactTactic

/-!
# The symbolic planar Gaussian heat kernel

The checked CAS differentiates the Gaussian formula and proves its residual is
zero for positive time. The denominator conditions of the CAS certificate all
follow from `0 < t`. A closing example turns the coordinate calculation into the
spacetime heat equation `HeatEquation.heatEquation` on positive time, the
statement proved analytically in `PDE.Parabolic.Heat.Gaussian`.
-/

@[expose] public section

open PDE (laplacian SatisfiesPDEProblem)

namespace HeatEquation.Symbolic.Space2

open PDE.Common
open CAS
open CAS.Certificate
open scoped CAS
open CAS.Euclid3
open _root_.HeatEquation.Space2
open MeasureTheory

noncomputable section

/-! ## Planar Gaussian heat kernel -/

/-- The planar Gaussian heat kernel in symbolic spacetime coordinates `(t,x,y)`.

This is the usual positive-time formula. The restriction `0 < t` enters as the
nonzero-denominator conditions of the residual certificate.
-/
def heatKernel2DAnsatz : Verified.Expr (Fin 3) :=
  .exp
      (-(((y : Verified.Expr (Fin 3)) ^ 2 + (z : Verified.Expr (Fin 3)) ^ 2) / (4 * x))) /
    ((4 : Verified.Expr (Fin 3)) * (.pi : Verified.Expr (Fin 3)) * x)

/--
At positive time, the symbolic planar Gaussian has the same value as the
analytic heat kernel `fundamentalSolutionHeat` used in
`PDE.Parabolic.Heat.Kernel.Equation`.
-/
theorem heatKernel2DAnsatz_eval_timeSpaceCons_eq_fundamentalSolutionHeat
    (ξ : ℝ^2) (t : ℝ) (ht : 0 < t) :
    heatKernel2DAnsatz.eval (PDE.Common.timeSpaceCons (n := 2) t ξ) =
      fundamentalSolutionHeat (n := 2) ξ t := by
  have hnorm : ‖ξ‖ ^ 2 = (ξ 0) ^ 2 + (ξ 1) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_two]
  simp [heatKernel2DAnsatz, fundamentalSolutionHeat, not_le_of_gt ht, hnorm,
    Verified.Expr.eval, Verified.Expr.SymVar.expr,
    PDE.Common.timeSpaceCons,
    Real.rpow_neg_one, div_eq_mul_inv,
    mul_assoc, mul_comm]

/-- The same value identity at a spacetime point `p` with `0 < p 0`. -/
theorem heatKernel2DAnsatz_eval_eq_fundamentalSolutionHeat_spacetime
    (p : ℝ^3) (ht : 0 < p 0) :
    heatKernel2DAnsatz.eval p =
      fundamentalSolutionHeat (n := 2) (spatialPartCLM 2 p) (p 0) := by
  have hp :
      PDE.Common.timeSpaceCons (n := 2) (p 0) (spatialPartCLM 2 p) = p := by
    exact timeSpaceCons_spatialPartCLM p
  rw [← hp]
  exact heatKernel2DAnsatz_eval_timeSpaceCons_eq_fundamentalSolutionHeat
    (spatialPartCLM 2 p) (p 0) ht

/-- The symbolic heat residual of the planar Gaussian. -/
def heatKernel2DResidual : Verified.Expr (Fin 3) :=
  Scalar.residual heat2DEquation heatKernel2DAnsatz

-- `cas using` asks for the generated nonzero conditions.
-- For this residual they are `π ≠ 0` and `t ≠ 0`.
private theorem heatKernel2D_cas_side_conditions
    (Ω : Set (ℝ^3))
    (hΩ : ∀ p ∈ Ω, 0 < p 0) :
    (Exact.SymbolicClaimRoute.withSideConditions
      heatKernel2DResidual).SideHoldsOn Ω := by
  intro p hp
  unfold Verified.Expr.Alg.SideHolds
  rw [show
    (Exact.SymbolicClaimRoute.withSideConditions heatKernel2DResidual).nonzero =
      [(.pi : Verified.Expr (Fin 3)), (x : Verified.Expr (Fin 3))] by
        decide +kernel]
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · change Real.pi ≠ 0
    exact Real.pi_ne_zero
  · change p 0 ≠ 0
    exact ne_of_gt (hΩ p hp)

/-- The planar Gaussian has zero symbolic heat residual on any positive-time domain. -/
theorem gaussianHeatKernel_symbolicResidual_eq_zero_on
    (Ω : Set (ℝ^3))
    (hΩ : ∀ p ∈ Ω, 0 < p 0) :
    Set.EqOn
      (Exact.exprFn heatKernel2DResidual)
      Exact.zeroFn
      Ω := by
  cas using (heatKernel2D_cas_side_conditions Ω hΩ)

/-- The symbolic Gaussian heat residual vanishes throughout positive time. -/
theorem heatKernel2D_eqOn_zero_positiveTime :
    Set.EqOn
      (Exact.exprFn heatKernel2DResidual)
      Exact.zeroFn
      (positiveTimeDomain (n := 2)) :=
  gaussianHeatKernel_symbolicResidual_eq_zero_on (positiveTimeDomain (n := 2))
    (fun _p hp ↦ hp)

/-- Residual-bound form of the exact Gaussian heat identity. -/
theorem heatKernel2D_residualBound_positiveTime :
    ResidualBound
      (Exact.exprFn heatKernel2DResidual)
      (positiveTimeDomain (n := 2))
      0 := by
  exact approxOn_of_eqOn heatKernel2D_eqOn_zero_positiveTime

/-- Pointwise form of the symbolic Gaussian heat identity. -/
theorem heatKernel2D_symbolicResidual_zero_of_time_pos
    (p : ℝ^3) (ht : 0 < p 0) :
    heatKernel2DResidual.eval p = 0 := by
  simpa [Exact.exprFn, Exact.zeroFn] using
    heatKernel2D_eqOn_zero_positiveTime ht

/-- The analytic operations in the Gaussian residual are valid when time is positive. -/
theorem heatKernel2D_analyticRequirements_holds_of_time_pos
    (p : ℝ^3) (ht : 0 < p 0) :
    (Scalar.CheckedResidual.analyticRequirements
      heat2DEquation heatKernel2DAnsatz).Holds p := by
  symbolic_residual

/-- Analytic side condition obtained from the checked Gaussian requirements. -/
theorem heatKernel2D_analyticSideCondition_of_time_pos
    (p : ℝ^3) (ht : 0 < p 0) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz heatKernel2DAnsatz) p heat2DEquation.residual :=
  Scalar.CheckedResidual.analyticSideCondition_of_requirements
    (eqn := heat2DEquation) (candidate := heatKernel2DAnsatz) (x := p)
    (heatKernel2D_analyticRequirements_holds_of_time_pos p ht)

/-- The symbolic Gaussian expression is valid at every positive-time point. -/
private theorem heatKernel2D_validAt_of_time_pos
    (p : ℝ^3) (ht : 0 < p 0) :
    heatKernel2DAnsatz.ValidAt p := by
  simp [heatKernel2DAnsatz, Verified.Expr.ValidAt, Verified.Expr.SymVar.expr,
    Verified.Expr.eval,
    ne_of_gt ht, Real.pi_ne_zero]

/-- Spatial first derivatives of the Gaussian are valid on positive time. -/
private theorem heatKernel2D_spatialDiff_validAt_of_time_pos
    (i : Fin 2) (p : ℝ^3) (ht : 0 < p 0) :
    (heatKernel2DAnsatz.diff i.succ).ValidAt p := by
  fin_cases i <;>
    simp [heatKernel2DAnsatz, Verified.Expr.ValidAt, Verified.Expr.diff,
      Verified.Expr.SymVar.expr, Verified.Expr.eval,
      ne_of_gt ht, Real.pi_ne_zero]

/-- The analytic Gaussian heat residual vanishes at every positive-time point. -/
theorem heatKernel2D_analyticResidual_zero_of_time_pos
    (p : ℝ^3) (ht : 0 < p 0) :
    DiffExpr.Equation.analyticResidual
      (Scalar.ansatz heatKernel2DAnsatz) p heat2DEquation = 0 := by
  have hclosed :
      (Scalar.residual heat2DEquation heatKernel2DAnsatz).eval p = 0 := by
    simpa [heatKernel2DResidual] using
      heatKernel2D_symbolicResidual_zero_of_time_pos p ht
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    hclosed (heatKernel2D_analyticSideCondition_of_time_pos p ht)

/--
The planar heat-kernel equation in spacetime partial derivatives, proved by the CAS.

This is the coordinate residual of `heat2DEquation`: time is coordinate `0`,
and the spatial second derivatives are in coordinates `1` and `2`. The version
with the Laplacian of the time slice is in `PDE.Parabolic.Heat.Kernel.Equation`.
-/
theorem heatKernel2D_spacetime_coordinate_residual_zero_of_time_pos
    (p : ℝ^3) (ht : 0 < p 0) :
    (∂[0]
        (fun q : ℝ^3 ↦ heatKernel2DAnsatz.eval q)) p -
      ((∂[1]
          (fun q : ℝ^3 ↦ (heatKernel2DAnsatz.diff 1).eval q)) p +
        (∂[2]
          (fun q : ℝ^3 ↦ (heatKernel2DAnsatz.diff 2).eval q)) p) = 0 := by
  have h := heatKernel2D_analyticResidual_zero_of_time_pos p ht
  simpa [heat2DEquation, Scalar.heatSpatial, Scalar.spatialLaplacian,
    Scalar.u, DiffExpr.D, DiffExpr.D2,
    DiffExpr.lower, Verified.Expr.eval, DiffExpr.Equation.analyticResidual,
    DiffExpr.analyticEval, DiffExpr.Equation.residual] using h

/-- The CAS route to the heat equation for the symbolic Gaussian: the coordinate residual
above, turned into the `heatEquation` operator by the slice-Laplacian identity
`laplacian_timeSpaceCons_slice2_eval_eq`. On positive time the expression is
`gaussianHeatKernel`, and the analytic statement is
`gaussianHeatKernel_satisfies_heatResidual_on_positiveTime`. -/
example :
    SatisfiesPDEProblem
      (HeatEquation.heatEquation (n := 2) (positiveTimeDomain (n := 2)))
      (fun p : ℝ^3 ↦ heatKernel2DAnsatz.eval p) := by
  apply HeatEquation.heatEquation.of_residual (n := 2)
  intro p ht
  change 0 < p 0 at ht
  have hcoord := heatKernel2D_spacetime_coordinate_residual_zero_of_time_pos p ht
  have hlap :
      laplacian (n := 2)
          (fun y : ℝ^2 ↦
            heatKernel2DAnsatz.eval (PDE.Common.timeSpaceCons (n := 2) (p 0) y))
          (spatialPartCLM 2 p) =
        (∂[(1 : Fin 3)]
            (fun q : ℝ^3 ↦ (heatKernel2DAnsatz.diff (1 : Fin 3)).eval q)) p +
          (∂[(2 : Fin 3)]
            (fun q : ℝ^3 ↦ (heatKernel2DAnsatz.diff (2 : Fin 3)).eval q)) p :=
    laplacian_timeSpaceCons_slice2_eval_eq heatKernel2DAnsatz p
      (by
        intro y
        apply heatKernel2D_validAt_of_time_pos
        simpa using ht)
      (by
        intro i y
        apply heatKernel2D_spatialDiff_validAt_of_time_pos i
        simpa using ht)
  simpa [HeatEquation.heatOperator, hlap] using hcoord

end

end HeatEquation.Symbolic.Space2
