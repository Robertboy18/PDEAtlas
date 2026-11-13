/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.HarmonicPart

/-!
# Green potentials are smooth outside the support of the source

The planar half-space Green potential `G[Z]` of a continuous compactly supported source `Z` is
harmonic, hence smooth, on every open set where the odd extension of `Z` vanishes
(`contDiffOn_halfSpaceGreenPotential_of_eqOn_zero`). For a source vanishing on the open
upper half-plane outside the disc of radius `ρ`, the odd extension vanishes outside the closed
disc, so the potential is smooth there, up to and across the boundary line. This is the
regularity of the commutator of a cutoff whose gradient lives in an annulus around the support
of the source.

## Main results

* `oddHalfSpaceExtension_eq_zero_outside`: a source vanishing on the open upper half-plane outside
  the disc of radius `ρ` has an odd extension vanishing outside the closed disc.
* `contDiffOn_halfSpaceGreenPotential_of_eq_zero_outside`: for such a source the Green potential
  is smooth on the complement of the closed disc.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set SobolevSpace
open scoped Topology Convolution

namespace GreenFunction

set_option linter.missingDocs true

/-- The odd extension of a source vanishing on the open upper half-plane outside the disc of
radius `ρ` vanishes outside the closed disc. -/
theorem oddHalfSpaceExtension_eq_zero_outside {Z : ℝ^2 → ℝ} {ρ : ℝ}
    (h0 : ∀ y ∈ HalfSpace.upper 2, ρ < ‖y‖ → Z y = 0) {y : ℝ^2} (hy : ρ < ‖y‖) :
    oddHalfSpaceExtension Z y = 0 := by
  unfold oddHalfSpaceExtension
  have hu : (HalfSpace.upper 2).indicator Z y = 0 := by
    by_cases h : y ∈ HalfSpace.upper 2
    · rw [indicator_of_mem h, h0 y h hy]
    · rw [indicator_of_notMem h]
  have hl : (HalfSpace.lower 2).indicator (fun y ↦ Z (HalfSpace.reflect 2 y)) y = 0 := by
    by_cases h : y ∈ HalfSpace.lower 2
    · rw [indicator_of_mem h]
      refine h0 _ ?_ (by rwa [HalfSpace.norm_reflect])
      have h1 : y (PDE.Common.lastIndex (n := 2)) < 0 := h
      change 0 < (HalfSpace.reflect 2 y) (PDE.Common.lastIndex (n := 2))
      simp [HalfSpace.reflect, PDE.Common.lastIndex] at h1 ⊢
      linarith
    · rw [indicator_of_notMem h]
  rw [Pi.sub_apply, hu, hl, sub_zero]

/-- **Smoothness outside the support.** For a continuous compactly supported source vanishing on
the open upper half-plane outside the disc of radius `ρ`, the half-space Green potential is smooth
on the complement of the closed disc of radius `ρ`, across the boundary line. -/
theorem contDiffOn_halfSpaceGreenPotential_of_eq_zero_outside {Z : ℝ^2 → ℝ} (hZ : Continuous Z)
    (hc : HasCompactSupport Z) {ρ : ℝ} (h0 : ∀ y ∈ HalfSpace.upper 2, ρ < ‖y‖ → Z y = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (halfSpaceGreenPotential Z) {y | ρ < ‖y‖} :=
  contDiffOn_halfSpaceGreenPotential_of_eqOn_zero hZ hc (isOpen_lt continuous_const
    continuous_norm) fun _ hy ↦ oddHalfSpaceExtension_eq_zero_outside h0 hy

end GreenFunction
