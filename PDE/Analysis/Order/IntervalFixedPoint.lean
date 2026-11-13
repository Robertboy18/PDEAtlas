/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.FixedPoints

/-!
# Monotone fixed points on order intervals

Knaster–Tarski on a nonempty closed order interval in a conditionally complete
lattice. If a monotone map sends the lower barrier upward and the upper barrier
downward, it preserves this interval. Lattice completeness then gives least and
greatest fixed points there, stated for the original map and ambient order.
-/

@[expose] public section

namespace PDE.OrderInterval

variable {α : Type*}

private def restrictToIcc
    [Preorder α]
    (T : α → α) (hT : Monotone T)
    (lower upper : α)
    (hlower : lower ≤ T lower) (hupper : T upper ≤ upper) :
    Set.Icc lower upper →o Set.Icc lower upper where
  toFun u :=
    ⟨T u, hlower.trans (hT u.2.1), (hT u.2.2).trans hupper⟩
  monotone' _ _ huv := hT huv

/-- In a conditionally complete lattice, a monotone self-map of a nonempty
closed order interval has a least fixed point in that interval. -/
theorem exists_least_fixed_point_Icc
    [ConditionallyCompleteLattice α]
    (T : α → α) (hT : Monotone T)
    (lower upper : α) (hlowerupper : lower ≤ upper)
    (hlower : lower ≤ T lower) (hupper : T upper ≤ upper) :
    ∃ u ∈ Set.Icc lower upper,
      Function.IsFixedPt T u ∧
        ∀ v ∈ Set.Icc lower upper, Function.IsFixedPt T v → u ≤ v := by
  let : Fact (lower ≤ upper) := ⟨hlowerupper⟩
  let S := restrictToIcc T hT lower upper hlower hupper
  let u : Set.Icc lower upper := S.lfp
  have hufixed : Function.IsFixedPt S u :=
    S.isFixedPt_lfp
  refine ⟨u, u.2, ?_, ?_⟩
  · exact congrArg Subtype.val hufixed
  · intro v hv hvfixed
    let v' : Set.Icc lower upper := ⟨v, hv⟩
    have hvfixed' : Function.IsFixedPt S v' := by
      apply Subtype.ext
      exact hvfixed
    exact S.isLeast_lfp.2 hvfixed'

/-- In a conditionally complete lattice, a monotone self-map of a nonempty
closed order interval has a greatest fixed point in that interval. -/
theorem exists_greatest_fixed_point_Icc
    [ConditionallyCompleteLattice α]
    (T : α → α) (hT : Monotone T)
    (lower upper : α) (hlowerupper : lower ≤ upper)
    (hlower : lower ≤ T lower) (hupper : T upper ≤ upper) :
    ∃ u ∈ Set.Icc lower upper,
      Function.IsFixedPt T u ∧
        ∀ v ∈ Set.Icc lower upper, Function.IsFixedPt T v → v ≤ u := by
  let : Fact (lower ≤ upper) := ⟨hlowerupper⟩
  let S := restrictToIcc T hT lower upper hlower hupper
  let u : Set.Icc lower upper := S.gfp
  have hufixed : Function.IsFixedPt S u :=
    S.isFixedPt_gfp
  refine ⟨u, u.2, ?_, ?_⟩
  · exact congrArg Subtype.val hufixed
  · intro v hv hvfixed
    let v' : Set.Icc lower upper := ⟨v, hv⟩
    have hvfixed' : Function.IsFixedPt S v' := by
      apply Subtype.ext
      exact hvfixed
    exact S.isGreatest_gfp.2 hvfixed'

end PDE.OrderInterval
