/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# A union of two balls for the weak Stokes pressure theorem

Two overlapping balls form a bounded open domain.
-/

@[expose] public noncomputable section

namespace PDE.Examples.StokesPressure

open Set Metric TopologicalSpace

/-- The centers of the two overlapping balls. -/
def center (a : ℝ) : ℝ^3 := WithLp.toLp 2 ![a, 0, 0]

/-- The union of two balls of radius `3/2`, whose centers are two units apart. -/
def domain : Opens (ℝ^3) :=
  ⟨ball (center (-1)) (3 / 2) ∪ ball (center 1) (3 / 2), isOpen_ball.union isOpen_ball⟩

/-- The domain is bounded. -/
theorem isBounded_domain : Bornology.IsBounded (domain : Set (ℝ^3)) :=
  (isBounded_ball (x := center (-1)) (r := 3 / 2)).union
    (isBounded_ball (x := center 1) (r := 3 / 2))

end PDE.Examples.StokesPressure
