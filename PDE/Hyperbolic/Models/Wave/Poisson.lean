/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Common.Euclidean
import PDE.Analysis.Integration.EuclideanBall -- shake: keep
import PDE.FDeriv.Operators

/-!
# Poisson formula for the two-dimensional wave equation

We define the Poisson candidate representation, Poisson's formula (27) of Evans, §2.4.1, and
rewrite it in its standard positive-time form. `Poisson.Representation` identifies the disk
integral with Hadamard descent from Kirchhoff's formula. `Poisson.ClassicalSolution`
proves joint `C²` regularity, the wave equation, and both limiting Cauchy traces
for `C³` displacement and `C²` velocity data. The propagation speed is `c = 1`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1, equation (27).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

namespace WaveEquation

open PDE.Analysis

/-- Candidate right-hand side of Poisson's formula for the two-dimensional wave equation.

The formula uses `|t|` as the disk radius and returns the displacement at `t = 0`.
The square-root kernel is integrable for continuous numerators, as proved in
`Poisson.Representation`. `Poisson.ClassicalSolution` proves that this total expression
constructs a classical Cauchy solution for `C³` displacement and `C²` velocity data,
including the joint limiting traces. -/
noncomputable def poissonFormula
    (g h : ℝ^2 → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  let r := |t|
  if _hr : r = 0 then g x else
    (1 / (2 * Real.pi * r)) * ∫ y in Metric.ball x r,
      (g y + t * h y + ∑ i, (∇ g y) i * (y i - x i)) /
        Real.sqrt (t^2 - ‖y - x‖^2)

/-- On positive times, `poissonFormula` is `1 / (2πt)` times the ordinary disk integral, which is
Poisson's formula (27) of Evans, §2.4.1. -/
theorem poissonFormula_of_pos (g h : ℝ^2 → ℝ) (x : ℝ^2) {t : ℝ} (ht : 0 < t) :
    poissonFormula g h x t = (1 / (2 * Real.pi * t)) * ∫ y in Metric.ball x t,
      (g y + t * h y + ∑ i, (∇ g y) i * (y i - x i)) / Real.sqrt (t^2 - ‖y - x‖^2) := by
  simp [poissonFormula, abs_of_pos ht, ht.ne']


end WaveEquation
