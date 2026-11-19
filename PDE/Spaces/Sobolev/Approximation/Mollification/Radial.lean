/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core

/-!
# Existence of a radial mollifier

The standard mollifier has a continuous radial profile vanishing beyond radius two.
Its construction in `Core` normalizes the explicit inner-product-space bump.
-/

@[expose] public section

open MeasureTheory Set

namespace SobolevSpace.Approximation

/-- There is a mollifier with a continuous radial profile supported in radius two.

The usual scaling and `Lᵖ` approximation theorems for `Mollifier` apply to this witness. -/
theorem exists_radial_mollifier (n : ℕ) :
    ∃ μ : Mollifier n, ∃ w : ℝ → ℝ,
      Continuous w ∧ (∀ x, μ.ρ x = w ‖x‖) ∧ (∀ r, 2 ≤ r → w r = 0) := by
  let w : ℝ → ℝ := fun r ↦ Real.smoothTransition (2 - r) /
    ∫ y : ℝ^n, Real.smoothTransition (2 - ‖y‖)
  refine ⟨standardMollifier n, w, ?_, standardMollifier_eq_norm, ?_⟩
  · exact (Real.smoothTransition.continuous.comp
      (continuous_const.sub continuous_id)).div_const _
  · intro r hr
    change Real.smoothTransition (2 - r) / _ = 0
    rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hr), zero_div]

end SobolevSpace.Approximation
