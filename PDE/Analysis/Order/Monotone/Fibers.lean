/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Countably many nonsingleton fibres of an ordered relation

If every point in an earlier fibre is at most every point in a later fibre,
the open intervals between two points of a nonsingleton fibre are disjoint.
Separability of the real line makes this family countable. Empty fibres are
allowed; neither attainment nor a particular selection is needed here.
-/

@[expose] public section

open Set Function

namespace PDE.Analysis

/-- A real ordered relation has at most countably many nonsingleton fibres.
The order hypothesis compares every pair of elements, not just a selection. -/
theorem countable_not_subsingleton_of_ordered_fibers {S : ℝ → Set ℝ}
    (horder : ∀ ⦃x z⦄, x < z → ∀ a ∈ S x, ∀ b ∈ S z, a ≤ b) :
    {x | ¬ (S x).Subsingleton}.Countable := by
  classical
  let E := {x | ¬ (S x).Subsingleton}
  have hex : ∀ x : E, ∃ a ∈ S x, ∃ b ∈ S x, a < b := by
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp x.property
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact ⟨a, ha, b, hb, hab⟩
    · exact ⟨b, hb, a, ha, hba⟩
  choose a ha b hb hab using hex
  have hdisjoint : Pairwise (Disjoint on fun x : E ↦ Ioo (a x) (b x)) := by
    intro x z hxz
    apply disjoint_left.mpr
    intro r hr hs
    have hne : (x : ℝ) ≠ z := fun h ↦ hxz (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (not_lt_of_ge (horder hlt (b x) (hb x) (a z) (ha z)))
        (hs.1.trans hr.2)
    · exact (not_lt_of_ge (horder hgt (b z) (hb z) (a x) (ha x)))
        (hr.1.trans hs.2)
  exact (hdisjoint.countable_of_isOpen_disjoint
    (fun _ ↦ isOpen_Ioo) (fun x ↦ nonempty_Ioo.mpr (hab x))).to_set

end PDE.Analysis
