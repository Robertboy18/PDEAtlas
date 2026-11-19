/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Closed-cell coverage by a uniform grid

Every point of the unit interval belongs to a closed cell of any positive
uniform subdivision. The right endpoint is assigned to the last cell.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Approximation

/-- Every point belongs to a closed cell of a positive uniform subdivision of `[0,1]`. -/
theorem exists_uniform_unit_cell (N : ℕ) (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Set.Icc 0 1) :
    ∃ i : Fin N, x ∈ Set.Icc ((i.val : ℝ) / N) (((i.val : ℝ) + 1) / N) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  by_cases hright : x = 1
  · subst x
    refine ⟨⟨N - 1, by omega⟩, ?_, ?_⟩
    · apply (div_le_iff₀ hNreal).mpr
      simpa only [one_mul] using (show ((N - 1 : ℕ) : ℝ) ≤ N by
        exact_mod_cast Nat.sub_le N 1)
    · apply (le_div_iff₀ hNreal).mpr
      have hlast : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        exact_mod_cast Nat.sub_add_cancel (show 1 ≤ N by omega)
      linarith
  · have hlt : x < 1 := lt_of_le_of_ne hx.2 hright
    let i : ℕ := Nat.floor (x * N)
    have hnonneg : 0 ≤ x * (N : ℝ) := mul_nonneg hx.1 hNreal.le
    have hi : i < N := (Nat.floor_lt hnonneg).mpr (by nlinarith)
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · exact (div_le_iff₀ hNreal).mpr (Nat.floor_le hnonneg)
    · exact (le_div_iff₀ hNreal).mpr (Nat.lt_floor_add_one (x * (N : ℝ))).le

end PDE.Analysis.Approximation
