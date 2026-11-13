/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A common weight below finitely many nonzero diagonal rates

For finitely many real rates and any `c`, there is `η > 0` with `c η < |rate i|`
for every nonzero rate. Zero rates impose no condition, so the statement also
holds when every rate is zero.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE.Analysis.Evolution

/-- A positive exponential weight can be chosen so that any prescribed finite
multiple of it lies below every nonzero rate of a finite diagonal system. -/
theorem exists_pos_mul_lt_abs_rate {ι : Type*} [Finite ι] (rate : ι → ℝ) (c : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ i, rate i ≠ 0 → c * η < |rate i| := by
  have he : ∀ᶠ η : ℝ in 𝓝 0, ∀ i, rate i ≠ 0 → c * η < |rate i| := by
    apply eventually_all.mpr
    intro i
    by_cases hi : rate i = 0
    · exact Eventually.of_forall fun _ h ↦ (h hi).elim
    · exact ((continuous_const.mul continuous_id).continuousAt.eventually_lt
        continuousAt_const (by simpa using abs_pos.mpr hi)).mono fun _ h _ ↦ h
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r / 2, by linarith, hbound ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < r / 2)]
  linarith

end PDE.Analysis.Evolution
