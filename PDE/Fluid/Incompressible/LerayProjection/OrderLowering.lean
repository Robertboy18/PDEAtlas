/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.Sobolev
public import PDE.Spaces.Sobolev.Evolution.VectorL2Triple

/-!
# The Sobolev Leray projection at different orders

The whole-space Leray projection `leraySobolev n k` on vector `Hᵏ(ℝ^n)` applies the `L²` Leray
projection to every derivative row. Forgetting the rows of order above `r ≤ k` therefore commutes
with it, so the projections on vector `Hᵏ(ℝ^n)` and on vector `Hʳ(ℝ^n)` are compatible.
-/

@[expose] public section

open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

namespace IncompressibleFlow

variable {n : ℕ}

/-- Lowering the order commutes with the whole-space Sobolev Leray projection. -/
theorem vectorLowerOrderCLM_leraySobolev {r k : ℕ} (hrk : r ≤ k) (U : VectorH n k) :
    vectorLowerOrderCLM hrk (leraySobolev n k U) =
      leraySobolev n r (vectorLowerOrderCLM hrk U) := by
  apply PiLp.ext
  intro j
  apply Subtype.ext
  apply PiLp.ext
  intro a
  change wkpCoordinateCLM a (lowerOrderCLM hrk (leraySobolev n k U j)) =
    wkpCoordinateCLM a (leraySobolev n r (vectorLowerOrderCLM hrk U) j)
  rw [leraySobolev_coordinate]
  have hrow : l2SobolevRow a (vectorLowerOrderCLM hrk U) =
      l2SobolevRow (a.castOrder hrk) U := by
    simp only [l2SobolevRow_apply, vectorLowerOrderCLM_apply, wkpCoordinateCLM_apply,
      lowerOrderCLM_apply]
  rw [hrow, ← leraySobolev_coordinate]
  rfl

end IncompressibleFlow
