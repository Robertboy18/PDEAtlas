/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Data.Finset.Sort

/-!
# Separation and coverage by adjacent finite intervals

Consecutive points in a sorted finite set separate every member of that
set. Adjacent closed intervals of any monotone finite sequence cover
its complete endpoint span, including all subdivision points.

## Main results

* `orderEmbOfFin_adjacent_separates`: no member of a finite set lies strictly between two adjacent
  points of its sorted enumeration.
* `Monotone.exists_mem_Icc_adjacent`: for a monotone `f : Fin (n + 2) → α`, every point of
  `[f 0, f (n + 1)]` lies in some `[f i, f (i + 1)]`.
-/

@[expose] public section

namespace Finset

/-- Every member of a finite set lies outside the open gap between two adjacent sorted points. -/
theorem orderEmbOfFin_adjacent_separates {α : Type*} [LinearOrder α]
    (s : Finset α) {n : ℕ} (h : s.card = n + 2) (i : Fin (n + 1))
    {x : α} (hx : x ∈ s) :
    x ≤ s.orderEmbOfFin h i.castSucc ∨ s.orderEmbOfFin h i.succ ≤ x := by
  let j : Fin (n + 2) := (s.orderIsoOfFin h).symm ⟨x, hx⟩
  have hj : s.orderEmbOfFin h j = x :=
    congrArg Subtype.val ((s.orderIsoOfFin h).apply_symm_apply ⟨x, hx⟩)
  rcases le_or_gt j i.castSucc with hji | hij
  · left
    rw [← hj]
    exact (s.orderEmbOfFin h).monotone hji
  · right
    rw [← hj]
    apply (s.orderEmbOfFin h).monotone
    change i.val + 1 ≤ j.val
    change i.val < j.val at hij
    omega

end Finset

/-- Adjacent closed intervals of a finite monotone sequence cover the whole endpoint span. -/
theorem Monotone.exists_mem_Icc_adjacent {α : Type*} [LinearOrder α]
    {n : ℕ} {f : Fin (n + 2) → α} (hf : Monotone f) {x : α}
    (hx : x ∈ Set.Icc (f 0) (f (Fin.last (n + 1)))) :
    ∃ i : Fin (n + 1), x ∈ Set.Icc (f i.castSucc) (f i.succ) := by
  classical
  have hex : ∃ j : Fin (n + 2), x ≤ f j := ⟨Fin.last (n + 1), hx.2⟩
  let j := Fin.find (fun j ↦ x ≤ f j) hex
  have hj : x ≤ f j := Fin.find_spec hex
  by_cases hjzero : j = 0
  · refine ⟨0, hx.1, ?_⟩
    have hzero : x ≤ f 0 := by simpa only [hjzero] using hj
    exact hzero.trans (hf (Fin.zero_le _))
  · have hjpos : 0 < j.val := by
      have hne : j.val ≠ 0 := fun h ↦ hjzero (Fin.ext h)
      omega
    let i : Fin (n + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hsucc : i.succ = j := by
      apply Fin.ext
      change j.val - 1 + 1 = j.val
      omega
    have hprev : i.castSucc < j := by
      change j.val - 1 < j.val
      omega
    have hleft : f i.castSucc < x := lt_of_not_ge (Fin.find_min hex hprev)
    refine ⟨i, hleft.le, ?_⟩
    simpa only [hsucc] using hj
