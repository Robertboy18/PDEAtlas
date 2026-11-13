/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.AffineInterface.Geometry
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Positivity.Finset

/-!
# Planar two-state profiles

We define the piecewise-constant profile separated by the affine
interface `x = speed * t`. The definition is shared by scalar conservation
laws and systems.

The right state is assigned on the interface. This convention does not affect
distributional identities.
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw

noncomputable section

/-- The two-state profile with left state `uL`, right state `uR`, and interface
`x = speed * t`. -/
def planarShock {E : Type*} [AddCommGroup E]
    (uL uR : E) (speed : ℝ) : ℝ^2 → E :=
  fun p ↦
    uR + (AffineInterface.leftHalfSpace speed).indicator
      (fun _ : ℝ^2 ↦ uL - uR) p

/-- Strictly to the left of the interface, `x < speed * t`, the profile takes the left state. -/
@[simp]
theorem planarShock_apply_of_mem {E : Type*} [AddCommGroup E] {uL uR : E} {speed : ℝ} {p : ℝ^2}
    (hp : p ∈ AffineInterface.leftHalfSpace speed) :
    planarShock uL uR speed p = uL := by
  simp [planarShock, hp]

/-- On the interface and to its right, `speed * t ≤ x`, the profile takes the right state. -/
@[simp]
theorem planarShock_apply_of_not_mem {E : Type*} [AddCommGroup E] {uL uR : E} {speed : ℝ} {p : ℝ^2}
    (hp : p ∉ AffineInterface.leftHalfSpace speed) :
    planarShock uL uR speed p = uR := by
  simp [planarShock, hp]

/-- A planar two-state profile is invariant under positive spacetime
dilation. -/
theorem planarShock_smul_of_pos {E : Type*} [AddCommGroup E] {a : ℝ} (ha : 0 < a) (uL uR : E)
    (speed : ℝ) (p : ℝ^2) :
    planarShock uL uR speed (a • p) = planarShock uL uR speed p := by
  by_cases hp : p ∈ AffineInterface.leftHalfSpace speed
  · have hscaled : a • p ∈ AffineInterface.leftHalfSpace speed :=
      (AffineInterface.smul_mem_leftHalfSpace_iff ha p).2 hp
    rw [planarShock_apply_of_mem hscaled, planarShock_apply_of_mem hp]
  · have hscaled : a • p ∉ AffineInterface.leftHalfSpace speed :=
      fun hmem ↦ hp <| (AffineInterface.smul_mem_leftHalfSpace_iff ha p).1 hmem
    rw [planarShock_apply_of_not_mem hscaled, planarShock_apply_of_not_mem hp]

/-- Applying a function to a planar two-state profile only changes its two
states. -/
theorem comp_planarShock {E F : Type*} [AddCommGroup E] [AddCommGroup F] (g : E → F) (uL uR : E)
    (speed : ℝ) :
    (fun p : ℝ^2 ↦ g (planarShock uL uR speed p)) = planarShock (g uL) (g uR) speed := by
  funext p
  by_cases hp : p ∈ AffineInterface.leftHalfSpace speed
  · simp [hp]
  · simp [hp]

section Integrability

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The norm of a planar shock is bounded by the larger endpoint norm. -/
theorem norm_planarShock_le_max (uL uR : E) (speed : ℝ) (p : ℝ^2) :
    ‖planarShock uL uR speed p‖ ≤ max ‖uL‖ ‖uR‖ := by
  by_cases hp : p ∈ AffineInterface.leftHalfSpace speed
  · rw [planarShock_apply_of_mem hp]
    exact le_max_left _ _
  · rw [planarShock_apply_of_not_mem hp]
    exact le_max_right _ _

/-- A planar shock takes two values on measurable half-spaces, so it is strongly
measurable in any normed codomain. -/
theorem stronglyMeasurable_planarShock (uL uR : E) (speed : ℝ) :
    StronglyMeasurable (planarShock uL uR speed) :=
  stronglyMeasurable_const.add <|
    stronglyMeasurable_const.indicator (AffineInterface.measurableSet_leftHalfSpace speed)

/-- A planar shock is measurable. -/
theorem measurable_planarShock [MeasurableSpace E] [BorelSpace E] (uL uR : E) (speed : ℝ) :
    Measurable (planarShock uL uR speed) :=
  (stronglyMeasurable_planarShock uL uR speed).measurable

/-- A composition with a planar shock is measurable even when the outer function is not,
because only its values at the two states are used. -/
theorem measurable_comp_planarShock {G : Type*} [AddCommGroup G] [MeasurableSpace F]
    [BorelSpace F] (g : G → F) (uL uR : G) (speed : ℝ) :
    Measurable (fun p : ℝ^2 ↦ g (planarShock uL uR speed p)) := by
  rw [comp_planarShock]
  exact measurable_planarShock (g uL) (g uR) speed

/-- A planar shock is locally integrable. -/
theorem locallyIntegrable_planarShock (uL uR : E) (speed : ℝ) :
    LocallyIntegrable (planarShock uL uR speed) volume := by
  refine (locallyIntegrable_const (μ := (volume : Measure ℝ^2)) (max ‖uL‖ ‖uR‖)).mono
    (stronglyMeasurable_planarShock uL uR speed).aestronglyMeasurable ?_
  filter_upwards with p
  exact (norm_planarShock_le_max uL uR speed p).trans (Real.le_norm_self _)

/-- Every composition with a planar shock is locally integrable. -/
theorem locallyIntegrable_comp_planarShock {G : Type*} [AddCommGroup G]
    (g : G → F) (uL uR : G) (speed : ℝ) :
    LocallyIntegrable (fun p : ℝ^2 ↦ g (planarShock uL uR speed p)) volume := by
  rw [comp_planarShock]
  exact locallyIntegrable_planarShock (g uL) (g uR) speed

end Integrability

end

end PDE.Hyperbolic.ConservationLaw
