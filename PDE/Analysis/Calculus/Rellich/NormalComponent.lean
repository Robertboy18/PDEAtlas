/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Rellich.Field

/-!
# The normal component of the Rellich field

If the gradient is normal to the boundary, its stress-energy flux is one
half of its squared norm times the signed radial normal component.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {n : ℕ}

/-- The normal Rellich flux when the vector field is purely normal. -/
theorem inner_rellichField_of_normal
    (c x ν : ℝ^n) {G : ℝ^n → ℝ^n} (hG : G x = inner ℝ (G x) ν • ν) :
    inner ℝ (rellichField c G x) ν =
      (‖G x‖ ^ 2 / 2) * inner ℝ (x - c) ν := by
  have hr : inner ℝ (x - c) (G x) =
      inner ℝ (G x) ν * inner ℝ (x - c) ν := by
    exact (congrArg (fun z ↦ inner ℝ (x - c) z) hG).trans (inner_smul_right _ _ _)
  have hn : ‖G x‖ ^ 2 = inner ℝ (G x) ν ^ 2 := by
    have h := congrArg (fun z ↦ inner ℝ (G x) z) hG
    simpa only [real_inner_self_eq_norm_sq, inner_smul_right, pow_two] using h
  rw [rellichField, inner_sub_left]
  simp only [inner_smul_left, starRingEnd_apply, star_trivial]
  rw [hr, hn]
  ring

end PDE.Analysis
