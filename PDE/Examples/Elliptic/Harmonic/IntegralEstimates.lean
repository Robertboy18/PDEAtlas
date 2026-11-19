/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.DerivativeEstimates.Integral
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# An interior derivative estimate for an explicit harmonic function

The function `exp(2x) cos(2y) + xy` is harmonic on the plane. Its third derivative
in the first coordinate is eight at the origin, so the interior estimate gives
a nonzero lower bound on its integral over every ball centered there. The estimate is
`norm_iteratedPartialDeriv_le_integral_abs`, which bounds derivatives at the center by
the `L¹` norm on the ball.
-/

@[expose] public section

namespace PDE.Examples.HarmonicIntegral

open LaplacianEquation MeasureTheory Metric

/-- A separated harmonic mode with a mixed polynomial term. -/
noncomputable def profile (p : ℝ^2) : ℝ :=
  Real.exp (2 * p 0) * Real.cos (2 * p 1) + p 0 * p 1

/-- The profile is smooth. -/
theorem contDiff_profile : ContDiff ℝ ⊤ profile := by
  unfold profile
  fun_prop

/-- The profile is harmonic on the plane. -/
theorem isHarmonicPDE_profile : IsHarmonicPDE 2 profile Set.univ := by
  refine ⟨contDiff_profile.of_le (by simp) |>.contDiffOn, ?_⟩
  intro p _
  cas

/-- `∂₀³ profile = 8 exp(2x₀) cos(2x₁)`. -/
theorem iteratedPartialDeriv_profile (p : ℝ^2) :
    iteratedPartialDeriv [0, 0, 0] profile p =
      8 * Real.exp (2 * p 0) * Real.cos (2 * p 1) := by
  have hsecond : iteratedPartialDeriv [0, 0] profile =
      fun q : ℝ^2 ↦ 4 * Real.exp (2 * q 0) * Real.cos (2 * q 1) := by
    funext q
    simp only [iteratedPartialDeriv]
    cas
  change (∂[0] (iteratedPartialDeriv [0, 0] profile)) p = _
  rw [hsecond]
  cas

/-- The profile is integrable on every ball. -/
theorem integrableOn_profile_ball (x : ℝ^2) (r : ℝ) :
    IntegrableOn profile (ball x r) volume :=
  (contDiff_profile.continuous.continuousOn.integrableOn_compact
    (isCompact_closedBall x r)).mono_set ball_subset_closedBall

/-- The third-derivative estimate at the origin, whose left side is `8`. -/
theorem eight_le_integral_abs {r : ℝ} (hr : 0 < r) :
    (8 : ℝ) ≤ interiorDerivativeConstant 2 3 / r ^ 5 *
      ∫ p in ball (0 : ℝ^2) r, |profile p| := by
  have h := isHarmonicPDE_profile.norm_iteratedPartialDeriv_le_integral_abs
    [0, 0, 0] hr (Set.subset_univ _) (integrableOn_profile_ball 0 r)
  simpa [iteratedPartialDeriv_profile] using h

end PDE.Examples.HarmonicIntegral
