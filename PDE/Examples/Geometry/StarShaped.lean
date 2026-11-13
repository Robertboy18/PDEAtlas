/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.StarConvex
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.Topology

/-!
# Star centers and boundary normals

On a domain with smooth graph boundary, a star center lies on the inward side of
every tangent hyperplane; the atlas is built from the graph geometry. On a ball,
any point in the closed ball is a star center, including points on its boundary.
The example below includes the one-dimensional interval and does not require the
center to be the origin.
-/

@[expose] public noncomputable section

open Set Metric SobolevSpace

namespace PDE.Examples.StarShaped

/-- Every point of the closed unit ball lies on the inward side of each tangent
hyperplane. The normal comes from the smooth graph boundary of the ball. -/
theorem unitBall_inner_sub_outwardUnitNormal_nonneg
    (m : ℕ) {c : ℝ^(m + 1)} (hc : ‖c‖ ≤ 1)
    (x : frontier (ball (0 : ℝ^(m + 1)) 1)) :
    letI : Boundary.C1ExtensionAtlas (m + 1) (ball (0 : ℝ^(m + 1)) 1) :=
      Boundary.HasC1GraphBoundary.c1ExtensionAtlas
      ((Boundary.Atlas.UnitBall.hasContDiffGraphBoundary (m + 1) 1).hasC1GraphBoundary
        le_rfl) isOpen_ball isBounded_ball
    0 ≤ inner ℝ ((x : ℝ^(m + 1)) - c)
      (Trace.C1.outwardUnitNormal (Ω := ball (0 : ℝ^(m + 1)) 1) x) := by
  let : Boundary.C1ExtensionAtlas (m + 1) (ball (0 : ℝ^(m + 1)) 1) :=
    Boundary.HasC1GraphBoundary.c1ExtensionAtlas
    ((Boundary.Atlas.UnitBall.hasContDiffGraphBoundary (m + 1) 1).hasC1GraphBoundary
      le_rfl) isOpen_ball isBounded_ball
  apply Trace.C1.inner_sub_outwardUnitNormal_nonneg_of_starConvex_closure
  rw [closure_ball (0 : ℝ^(m + 1)) one_ne_zero]
  exact (convex_closedBall (0 : ℝ^(m + 1)) 1).starConvex
    (by simpa only [mem_closedBall, dist_zero_right] using hc)

/-- A positive contraction toward any closed-ball center preserves the open ball.
Boundary centers and the interval case are included. -/
theorem unitBall_homothety_mem
    (m : ℕ) {c x : ℝ^(m + 1)} (hc : ‖c‖ ≤ 1)
    (hx : x ∈ ball (0 : ℝ^(m + 1)) 1) {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    (1 - t) • c + t • x ∈ ball (0 : ℝ^(m + 1)) 1 := by
  have hgraph := (Boundary.Atlas.UnitBall.hasContDiffGraphBoundary
    (m + 1) 1).hasC1GraphBoundary le_rfl
  apply hgraph.homothety_mem_of_starConvex_closure isOpen_ball _ hx ht ht₁
  change StarConvex ℝ c (closure (ball (0 : ℝ^(m + 1)) 1))
  rw [closure_ball (0 : ℝ^(m + 1)) one_ne_zero]
  exact (convex_closedBall (0 : ℝ^(m + 1)) 1).starConvex
    (by simpa only [mem_closedBall, dist_zero_right] using hc)

end PDE.Examples.StarShaped
