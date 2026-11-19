/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Operator norms of finite ℓᵖ coordinate projections

Coordinate evaluation has norm at most one for every `1 ≤ p ≤ ∞`. If the selected
coordinate space is nontrivial, a vector supported in that coordinate attains this
bound. The coordinate spaces and their universes need not coincide with the scalar field.
-/

@[expose] public noncomputable section

open scoped ENNReal

namespace PiLp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {F : ι → Type*}
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

/-- Every coordinate evaluation is a contraction for the finite ℓᵖ norm. -/
theorem norm_proj_le (i : ι) : ‖proj p (𝕜 := 𝕜) F i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, proj_apply] using norm_apply_le x i

/-- Evaluation at a nontrivial coordinate has operator norm exactly one. -/
@[simp]
theorem norm_proj (i : ι) [Nontrivial (F i)] : ‖proj p (𝕜 := 𝕜) F i‖ = 1 := by
  classical
  obtain ⟨b, hb⟩ := exists_ne (0 : F i)
  apply le_antisymm (norm_proj_le i)
  have h := (proj p (𝕜 := 𝕜) F i).le_opNorm (single p i b)
  simp only [proj_apply, ofLp_single, Pi.single_eq_same, norm_single] at h
  exact le_of_mul_le_mul_right (by simpa only [one_mul] using h) (norm_pos_iff.mpr hb)

end PiLp
