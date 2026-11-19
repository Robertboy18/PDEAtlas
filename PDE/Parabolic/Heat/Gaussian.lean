/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Equation
public import PDE.Parabolic.Heat.Kernel.Basic
import PDE.Parabolic.Heat.Kernel.Equation

/-!
# The planar Gaussian heat kernel on spacetime

The two-dimensional heat kernel, written as a function of `(t, x, y)`, has zero heat residual on
every domain inside `{t > 0}`. This is the case `n = 2` of the remark in Evans's §2.3.1(b) that the
fundamental solution solves the heat equation away from `(0, 0)`. The proof reads the residual off
the kernel identity `fundamentalSolutionHeat_satisfies_equation` from
`PDE.Parabolic.Heat.Kernel.Equation`, where the derivative formulas are proved.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(a), (4)-(7) and the definition of the fundamental
  solution, pp. 45-46, and §2.3.1(b), p. 47.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SatisfiesPDEProblem)

namespace HeatEquation

open PDE (time time_apply)
open PDE.Common

noncomputable section

/-! ## Gaussian heat kernel -/

namespace Space2

/-- The planar Gaussian heat kernel as a function on spacetime `ℝ^3`. -/
def gaussianHeatKernel : ℝ^3 → ℝ :=
  fun p ↦ fundamentalSolutionHeat (n := 2) (spatialPartCLM 2 p) (time p)

/-- The Gaussian heat kernel satisfies the heat equation, as a residual identity, on the
positive-time domain. -/
theorem gaussianHeatKernel_satisfies_heatResidual_on_positiveTime :
    SatisfiesPDEProblem
      (HeatEquation.heatEquation (n := 2) (positiveTimeDomain (n := 2))) gaussianHeatKernel := by
  apply HeatEquation.heatEquation.of_residual (n := 2)
  intro p hp
  have hpcons :
      PDE.Common.timeSpaceCons (n := 2) (p 0) (spatialPartCLM 2 p) = p := by
    exact timeSpaceCons_spatialPartCLM p
  have h :=
    fundamentalSolutionHeat_satisfies_equation
      (n := 2) (spatialPartCLM 2 p) (p 0) hp
  have hslice :
      (fun y : ℝ^2 ↦
        fundamentalSolutionHeat (n := 2)
          (spatialPartCLM 2 (PDE.Common.timeSpaceCons (n := 2) (p 0) y)) (p 0)) =
        fun y : ℝ^2 ↦ fundamentalSolutionHeat (n := 2) y (p 0) := by
    simp
  unfold HeatEquation.heatOperator gaussianHeatKernel
  simp only [time_apply, PDE.Common.timeSpaceCons_zero]
  rw [hslice]
  simpa [hpcons] using h

/-- The Gaussian heat kernel has zero heat residual on any domain contained in positive
time. -/
theorem gaussianHeatKernel_satisfies_heatResidual_on
    (Ω : Set (ℝ^3))
    (hΩ : ∀ p ∈ Ω, 0 < time p) :
    SatisfiesPDEProblem
      (HeatEquation.heatEquation (n := 2) Ω) gaussianHeatKernel :=
  HeatEquation.heatEquation.of_residual (n := 2) fun p hp ↦
    HeatEquation.heatEquation.residual_eq (n := 2)
      gaussianHeatKernel_satisfies_heatResidual_on_positiveTime (hΩ p hp)

attribute [aesop safe apply]
  gaussianHeatKernel_satisfies_heatResidual_on_positiveTime
  gaussianHeatKernel_satisfies_heatResidual_on

end Space2

end

end HeatEquation
