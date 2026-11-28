/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# A union of two balls for the weak Stokes pressure theorem

In `ℝ³`, the union of the overlapping open balls of radius `3/2` centered at `(−1, 0, 0)` and
`(1, 0, 0)` is a bounded open set.
-/

@[expose] public noncomputable section

namespace PDE.Examples.StokesPressure

open Set Metric TopologicalSpace

/-- The point `(a, 0, 0)` on the first coordinate axis. -/
def center (a : ℝ) : ℝ^3 := WithLp.toLp 2 ![a, 0, 0]

/-- The union of two balls of radius `3/2`, whose centers are two units apart. -/
def domain : Opens (ℝ^3) :=
  ⟨ball (center (-1)) (3 / 2) ∪ ball (center 1) (3 / 2), isOpen_ball.union isOpen_ball⟩

/-- The domain is bounded. -/
theorem isBounded_domain : Bornology.IsBounded (domain : Set (ℝ^3)) :=
  (isBounded_ball (x := center (-1)) (r := 3 / 2)).union
    (isBounded_ball (x := center 1) (r := 3 / 2))

end PDE.Examples.StokesPressure
