/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Data
public import PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Exponential.Coordinates
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Compact-data blowup for the coupled conservative exponential system

Both physical components equal the compact compression bump. The first
invariant has initial slope `-1`, and the second is the constant `-2`. The theorem
`not_exists_global_of_compressive_invariant` therefore rules out a solution of
`∂ₜu + ∂ₓ flux(u) = 0` with continuous second jet on `t > 0` and these initial values
(`not_exists_global_solution`).
-/

@[expose] public noncomputable section

open PDE.Analysis PDE.Hyperbolic.ConservationLaw.System
open scoped ContDiff

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Exponential

/-- Nonzero smooth compactly supported physical initial data. -/
def initialData (x : ℝ) : ℝ^2 := !₂[compression x, compression x]

/-- The initial data are smooth. -/
theorem contDiff_initialData : ContDiff ℝ ∞ initialData := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> exact contDiff_compression

/-- The initial data have compact support. -/
theorem hasCompactSupport_initialData : HasCompactSupport initialData :=
  hasCompactSupport_compression.comp_left (g := fun r : ℝ ↦ (!₂[r, r] : ℝ^2))
    (by ext i; fin_cases i <;> rfl)

/-- The first invariant has a compressive initial derivative. -/
theorem initial_invariant_slope :
    deriv (fun x ↦ coordinates (initialData x) 0) 0 = -1 := by
  exact (hasDerivAt_compression_zero.add_const 1).deriv

/-- No solution with continuous second jet on `t > 0` has the initial data
`initialData`. -/
theorem not_exists_global_solution :
    ¬ ∃ u : ℝ^2 → ℝ^2,
      Nonempty (ContinuousSecondJetOn u PDE.Common.positiveTimeDomain) ∧
      (∀ x, u !₂[0, x] = initialData x) ∧
      (∀ p ∈ PDE.Common.positiveTimeDomain, fluxResidual flux u p = 0) := by
  apply not_exists_global_of_compressive_invariant
    (contDiff_flux.of_le (by simp)) isStrictlyHyperbolicAt_flux coordinates
    coordinate_covectors positive_speed_derivative
    contDiff_initialData.continuous hasCompactSupport_initialData
    (i := 0) (x₀ := 0)
  rw [initial_invariant_slope]
  norm_num

end PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Exponential
