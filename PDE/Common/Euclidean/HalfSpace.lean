/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Closed coordinate half-spaces

The set `{x | 0 ≤ x i}` includes its boundary hyperplane and is preserved by positive
dilations. Coordinate charts and integration on a half-space both use these facts.

-/

@[expose] public section

namespace PDE.Common

/-- The closed half-space on the nonnegative side of coordinate hyperplane `i`. -/
def coordinateClosedHalfSpace {n : ℕ} (i : Fin n) : Set (ℝ^n) :=
  {x | 0 ≤ x i}

/-- Membership in a closed coordinate half-space means that coordinate is nonnegative. -/
@[simp]
theorem mem_coordinateClosedHalfSpace {n : ℕ} {i : Fin n} {x : ℝ^n} :
    x ∈ coordinateClosedHalfSpace i ↔ 0 ≤ x i :=
  Iff.rfl

/-- A closed coordinate half-space is a closed subset of Euclidean space. -/
theorem isClosed_coordinateClosedHalfSpace {n : ℕ} (i : Fin n) :
    IsClosed (coordinateClosedHalfSpace i) :=
  isClosed_le continuous_const (EuclideanSpace.proj i).continuous

/-- Closed coordinate half-spaces are Lebesgue measurable. -/
theorem measurableSet_coordinateClosedHalfSpace {n : ℕ} (i : Fin n) :
    MeasurableSet (coordinateClosedHalfSpace i) :=
  (isClosed_coordinateClosedHalfSpace i).measurableSet

/-- Positive dilation preserves membership, including points on the boundary. -/
theorem smul_mem_coordinateClosedHalfSpace_iff {n : ℕ} (i : Fin n)
    {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    t • x ∈ coordinateClosedHalfSpace i ↔ x ∈ coordinateClosedHalfSpace i := by
  change 0 ≤ (t • x : ℝ^n) i ↔ 0 ≤ x i
  simp [smul_eq_mul, mul_nonneg_iff_of_pos_left ht]

end PDE.Common
