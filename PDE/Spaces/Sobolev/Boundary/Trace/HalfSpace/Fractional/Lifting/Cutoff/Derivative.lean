/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Cutoff

/-!
# The derivative of the height cutoff

The cutoff contributes an extra term to the normal derivative of the
mollified extension. Its derivative is bounded and vanishes outside the
same compact interval, so this term costs only the boundary `Lᵖ` norm.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace SobolevSpace.Trace.HalfSpace

/-- The smooth height cutoff has a continuous derivative. -/
theorem continuous_deriv_heightCutoff : Continuous (deriv heightCutoff) :=
  contDiff_heightCutoff.continuous_deriv (by simp)

/-- A fixed positive constant bounds the derivative of the height cutoff. -/
theorem exists_pos_bound_deriv_heightCutoff :
    ∃ C > 0, ∀ t : ℝ, ‖deriv heightCutoff t‖ ≤ C := by
  obtain ⟨C, hC⟩ := hasCompactSupport_heightCutoff.deriv.exists_bound_of_continuous
    continuous_deriv_heightCutoff
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun t ↦ (hC t).trans (le_max_left _ _)⟩

/-- The cutoff derivative vanishes beyond the cutoff's support. -/
theorem deriv_heightCutoff_eq_zero_of_two_lt {t : ℝ} (ht : 2 < |t|) :
    deriv heightCutoff t = 0 := by
  have he : heightCutoff =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) ht]
      with r hr
    exact heightCutoff_eq_zero hr.le
  simpa using he.deriv_eq

end SobolevSpace.Trace.HalfSpace
