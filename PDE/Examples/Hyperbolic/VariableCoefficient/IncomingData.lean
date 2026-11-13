/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import PDE.Hyperbolic.Models.Wave.Kirchhoff.ClassicalSolution
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smooth incoming data for the Kirchhoff potential

The velocity `exp(p 1) * expNegInvGlue(p 0 - 2)` vanishes on the half-space
`p 0 ≤ 2`, but its Kirchhoff potential is strictly positive at time three
and spatial origin. Positivity follows from the continuous nonnegative
integrand on the unit sphere and its positive value at the first coordinate
unit vector. The data are neither compactly supported nor integrable on `ℝ³`.

These data give the incoming wave of `IncomingWave`. On an unbounded domain,
compact optical sublevels prevent a wave from entering from spatial infinity (cf. the finite
propagation speed of Evans, §7.2.4, Theorem 8).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.4, Theorem 8 (Finite propagation speed),
  pp. 416-417.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory
open PDE.Analysis PDE.Common
open WaveEquation
open scoped ContDiff

namespace PDE.Examples.VariableCoefficient

/-- Smooth velocity data supported in the closed half-space `p 0 ≥ 2`. -/
def incomingData (p : ℝ^3) : ℝ :=
  Real.exp (p 1) * expNegInvGlue (p 0 - 2)

/-- The incoming data are smooth. -/
theorem contDiff_incomingData {k : ℕ∞} : ContDiff ℝ k incomingData := by
  exact (Real.contDiff_exp.comp (contDiff_piLp_apply 2)).mul
    (expNegInvGlue.contDiff.comp ((contDiff_piLp_apply 2).sub contDiff_const))

/-- The incoming data are nonnegative everywhere. -/
theorem incomingData_nonneg (p : ℝ^3) : 0 ≤ incomingData p :=
  mul_nonneg (Real.exp_pos _).le (expNegInvGlue.nonneg _)

/-- The data vanish on the closed half-space `p 0 ≤ 2`. -/
theorem incomingData_eq_zero {p : ℝ^3} (hp : p 0 ≤ 2) : incomingData p = 0 := by
  simp only [incomingData, expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr hp), mul_zero]

/-- The incoming velocity is strictly positive beyond the separating plane. -/
theorem incomingData_pos {p : ℝ^3} (hp : 2 < p 0) : 0 < incomingData p :=
  mul_pos (Real.exp_pos _) (expNegInvGlue.pos_of_pos (sub_pos.mpr hp))

/-- The Kirchhoff potential is positive at time three and the origin. -/
theorem kirchhoffPotential_incomingData_pos :
    0 < kirchhoffPotential incomingData (timeSpaceCons 3 0) := by
  let e : Metric.sphere (0 : ℝ^3) 1 :=
    ⟨EuclideanSpace.single 0 1, by
      simp [PiLp.norm_single]⟩
  have hc : Continuous
      (fun w : Metric.sphere (0 : ℝ^3) 1 ↦ incomingData ((3 : ℝ) • (w : ℝ^3))) :=
    (contDiff_incomingData (k := ⊤)).continuous.comp (by fun_prop)
  have hi : Integrable
      (fun w : Metric.sphere (0 : ℝ^3) 1 ↦ incomingData ((3 : ℝ) • (w : ℝ^3)))
      ((volume : Measure (ℝ^3)).toSphere) :=
    hc.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ Set.mem_univ _))
  have he : 0 < incomingData ((3 : ℝ) • (e : ℝ^3)) := by
    apply incomingData_pos
    norm_num [e, PiLp.single_apply]
  have hpos := integral_pos_of_integrable_nonneg_nonzero hc hi
    (fun w ↦ incomingData_nonneg _) he.ne'
  rw [kirchhoffPotential_timeSpaceCons, unitSphereAverage]
  simp only [zero_add]
  exact mul_pos (by norm_num) (div_pos hpos unitSphereArea_pos)

end PDE.Examples.VariableCoefficient
