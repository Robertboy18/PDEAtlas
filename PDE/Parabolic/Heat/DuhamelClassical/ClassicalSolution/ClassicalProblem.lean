/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.Equation
import Mathlib.Analysis.Convolution -- shake: keep
import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.JointDifferentiability
import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.ResidualAndInitialTrace

/-!
# Projecting the classical Duhamel formula to the forced heat problem

For a globally `C²`, compactly supported source, Duhamel's formula solves the forced heat
`PDEProblem`: it is jointly differentiable, has the forced residual, and takes the value zero at the
initial time. Evans's §2.3.1(c), Theorem 2 needs only `f ∈ C²₁(ℝⁿ × [0, ∞))` with compact support.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(c), Theorem 2 (Solution of nonhomogeneous problem),
  pp. 49-50.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SatisfiesPDEProblem)

namespace HeatEquation

open scoped Pointwise Topology Interval Convolution
open PDE.Common
open MeasureTheory

variable {n : ℕ}


/-- A globally `C²`, compactly supported source makes Duhamel's formula satisfy the
forced-heat residual and zero initial value.

`SatisfiesPDEProblem` is pointwise and does not include convergence to the initial value as
`t ↓ 0`; that convergence is part of the residual-and-trace theorem. -/
theorem nonhomogeneousSolution_satisfiesPDEProblem_of_contDiff_two_compactSupport
    (f : ℝ^(n + 1) → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n) f
        (fun _ : ℝ^n ↦ 0))
      (fun xt : ℝ^(n + 1) ↦
        nonhomogeneousSolution (n := n) f
          (spatialPartCLM n xt) (xt 0)) := by
  refine nonhomogeneousSolution_satisfiesPDEProblem_of_residual (n := n) f
    (nonhomogeneousSolution_forced_heat_residual_and_initial_trace
      (n := n) f hf2 hfc).1 ?_
  intro xt hxt
  exact
    (differentiableAt_nonhomogeneousSolution_timeSpace_classical
      (n := n) f hf2 hfc
      (xt 0, spatialPartCLM n xt) hxt).comp xt
      ((EuclideanSpace.proj (0 : Fin (n + 1))).differentiableAt.prodMk
        (spatialPartCLM n).differentiableAt)

end HeatEquation
