/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.Definition

/-!
# Literal data values of a smooth wave

The smoothness hypothesis determines canonical closure values from the
interior. When the supplied forcing and initial functions are themselves
continuous on the relevant closures, these canonical values are their literal
values, including at the initial and terminal times.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

namespace Hyperbolic.HigherRegularity.SmoothWave.IsClassicalSolution

open Set PDE.Common SobolevSpace SobolevSpace.GraphSpace.BoundaryRegularity
open SobolevSpace.Evolution.Classical

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {P : SmoothFullCoefficients n Ω}
  {hopen : IsOpen Ω} {f U : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
  {hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))}
  {hg : ∀ k, ContDiffUpToBoundary k g Ω} {hh : ∀ k, ContDiffUpToBoundary k h Ω}
  (hU : IsClassicalSolution P hopen hf hg hh U)

/-- Literal continuous forcing satisfies the full equation at every
closed-interval time, including the final time. -/
theorem equation_of_continuousOn (hab : a < b)
    (hc : ContinuousOn f (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^n} (hx : x ∈ Ω) :
    derivativeSlice hopen hU.smooth [0, 0] t x +
      P.classicalLoad (fun y ↦ U (timeSpaceCons t y)) x = f (timeSpaceCons t x) :=
  (hU.equation t ht x hx).trans (derivativeSlice_nil hopen hab hf hc ht (subset_closure hx))

include hU in
/-- The initial position equals the literal continuous datum. -/
theorem initial_value_of_continuousOn (hc : ContinuousOn g (closure Ω))
    {x : ℝ^n} (hx : x ∈ closure Ω) : U (timeSpaceCons a x) = g x :=
  (hU.initial_value x hx).trans ((hg 0).continuousRepresentative_eqOn_closure hc (fun _ _ ↦ rfl) hx)

/-- The initial velocity equals the literal continuous datum. -/
theorem initial_velocity_of_continuousOn (hc : ContinuousOn h (closure Ω))
    {x : ℝ^n} (hx : x ∈ closure Ω) : derivativeSlice hopen hU.smooth [0] a x = h x :=
  (hU.initial_velocity x hx).trans
    ((hh 0).continuousRepresentative_eqOn_closure hc (fun _ _ ↦ rfl) hx)

end Hyperbolic.HigherRegularity.SmoothWave.IsClassicalSolution
