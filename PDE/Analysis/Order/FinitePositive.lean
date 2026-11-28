/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max

/-!
# A positive number below finitely many positive numbers

If `f i > 0` for every `i` in a finite set `s`, some `r > 0` lies strictly below every `f i`
(`Finset.exists_pos_forall_lt`). The spectral decomposition of a semigroup generator uses this to
choose one radius for discs around finitely many eigenvalues, small enough that the discs are
disjoint and stay in a half-plane. Half of the least value works; Mathlib's
`Finset.exists_min_image` finds the least value.
-/

@[expose] public section

/-- A positive number below finitely many positive numbers: if `f i > 0` for every `i` in the
finite set `s`, there is `r > 0` with `r < f i` for every `i` in `s`. For a nonempty `s`, half of
the least `f i` works. -/
theorem Finset.exists_pos_forall_lt {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ r, 0 < r ∧ ∀ i ∈ s, r < f i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image f hs
  exact ⟨f j / 2, half_pos (hf j hj), fun i hi ↦ (half_lt_self (hf j hj)).trans_le (hmin i hi)⟩
