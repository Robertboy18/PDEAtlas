/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Rational rectangle subdivision covers

A binary tree records horizontal or vertical split coordinates and a list of rational
payload values at each leaf. `Tree.records` reconstructs the closed leaf rectangles
from a root box, and `Tree.covers` puts every real point of the root in some leaf.

The coverage theorem does not require ordered box endpoints or a split coordinate
inside its parent box. Consequently it gives coverage, not disjointness or
containment of every leaf in the root. The payload values play no role.
-/

@[expose] public section
namespace PDE.Analysis.RectangleCover

/-- Rational rectangle endpoints, interpreted as a closed real-coordinate box. -/
structure Box where
  /-- Lower endpoint of the first coordinate. -/
  xlo : ℚ
  /-- Upper endpoint of the first coordinate. -/
  xhi : ℚ
  /-- Lower endpoint of the second coordinate. -/
  ylo : ℚ
  /-- Upper endpoint of the second coordinate. -/
  yhi : ℚ
  deriving DecidableEq

/-- Membership uses real coordinates and closed sides. -/
def Box.Contains (b : Box) (x y : ℝ) : Prop :=
  (b.xlo : ℝ) ≤ x ∧ x ≤ (b.xhi : ℝ) ∧ (b.ylo : ℝ) ≤ y ∧ y ≤ (b.yhi : ℝ)

/-- Binary subdivisions retain a list of rational bounds at each terminal leaf. -/
inductive Tree where
  | leaf (bounds : List ℚ)
  | splitX (midpoint : ℚ) (left right : Tree)
  | splitY (midpoint : ℚ) (left right : Tree)

/-- Recover the leaf rectangles from their ancestors' shared split endpoints. -/
def Tree.records : Tree → Box → List (Box × List ℚ)
  | .leaf bounds, b => [(b, bounds)]
  | .splitX m l r, b => l.records { b with xhi := m } ++ r.records { b with xlo := m }
  | .splitY m l r, b => l.records { b with yhi := m } ++ r.records { b with ylo := m }

/-- Every point of the root lies in a terminal rectangle. -/
theorem Tree.covers (t : Tree) (b : Box) (x y : ℝ) (h : b.Contains x y) :
    ∃ entry ∈ t.records b, entry.1.Contains x y := by
  induction t generalizing b with
  | leaf bounds => exact ⟨(b, bounds), by simp [records], h⟩
  | splitX m l r ihl ihr =>
    by_cases hm : x ≤ (m : ℝ)
    · obtain ⟨entry, he, hp⟩ := ihl { b with xhi := m } ⟨h.1, hm, h.2.2⟩
      exact ⟨entry, List.mem_append_left _ he, hp⟩
    · obtain ⟨entry, he, hp⟩ := ihr { b with xlo := m } ⟨(le_of_not_ge hm), h.2⟩
      exact ⟨entry, List.mem_append_right _ he, hp⟩
  | splitY m l r ihl ihr =>
    by_cases hm : y ≤ (m : ℝ)
    · obtain ⟨entry, he, hp⟩ := ihl { b with yhi := m } ⟨h.1, h.2.1, h.2.2.1, hm⟩
      exact ⟨entry, List.mem_append_left _ he, hp⟩
    · obtain ⟨entry, he, hp⟩ := ihr { b with ylo := m }
        ⟨h.1, h.2.1, le_of_not_ge hm, h.2.2.2⟩
      exact ⟨entry, List.mem_append_right _ he, hp⟩

end PDE.Analysis.RectangleCover
