/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Rescaling.Scalar
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.Topology
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph

/-!
# Compressing a zero-boundary function

Compress a function into the ball of half the radius and fill the surrounding
annulus with zero. The result still has zero boundary values. In three dimensions,
its Dirichlet energy is half the original energy. These statements hold for every
Sobolev function.

A negative scalar also reverses the spatial coordinates. The interval example
checks that its first derivative still has the same `L¹` norm.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.ZeroTrace
open scoped ENNReal Sobolev

namespace PDE.Examples.SobolevRescaling

/-- The ball has smooth graph boundary and is star-shaped, so dilating by two maps
its preimage into itself. -/
theorem unitBall_preimage_two_smul (m : ℕ) :
    (fun x : ℝ^(m + 1) ↦ (2 : ℝ) • x) ⁻¹' ball 0 1 ⊆ ball 0 1 := by
  have hgraph := (Boundary.Atlas.UnitBall.hasContDiffGraphBoundary
    (m + 1) 1).hasC1GraphBoundary le_rfl
  apply hgraph.preimage_smul_subset_of_starConvex_closure isOpen_ball _ (by norm_num)
  change StarConvex ℝ 0 (closure (ball (0 : ℝ^(m + 1)) 1))
  rw [closure_ball (0 : ℝ^(m + 1)) one_ne_zero]
  exact (convex_closedBall (0 : ℝ^(m + 1)) 1).starConvex (by simp)

/-- Halving the support radius in three dimensions halves the Dirichlet energy. -/
theorem unitBall_compression_energy (u : W₀^{1,2}((ball 0 1 : Set (ℝ^3)))) :
    ∃ v : W₀^{1,2}((ball 0 1 : Set (ℝ^3))),
      baseRepresentative (v : W^{1,2}(ball (0 : ℝ^3) 1)) =ᵐ[domainMeasure 3 (ball 0 1)]
        (fun x ↦ (ball (0 : ℝ^3) 1).indicator
          (baseRepresentative (u : W^{1,2}(ball (0 : ℝ^3) 1))) ((2 : ℝ) • x)) ∧
      ‖∇ (v : W^{1,2}(ball (0 : ℝ^3) 1))‖ ^ 2 =
        (1 / 2 : ℝ) * ‖∇ (u : W^{1,2}(ball (0 : ℝ^3) 1))‖ ^ 2 := by
  refine ⟨dilationW1p0CLM (by norm_num) measurableSet_ball isOpen_ball 2
    (by norm_num) (unitBall_preimage_two_smul 2) u, ?_, ?_⟩
  · exact dilationW1p0ToW1p_base_ae (by norm_num) measurableSet_ball
      measurableSet_ball 2 (by norm_num) u
  · rw [norm_wkpGradientCLM_dilationW1p0CLM_sq]
    norm_num

/-- Reflection combined with compression keeps the derivative's `L¹` norm on an interval. -/
theorem interval_reflected_compression (u : W₀^{1,1}((ball 0 1 : Set (ℝ^1)))) :
    ∃ v : W₀^{1,1}((ball 0 1 : Set (ℝ^1))),
      baseRepresentative (v : W^{1,1}(ball (0 : ℝ^1) 1)) =ᵐ[domainMeasure 1 (ball 0 1)]
        (fun x ↦ (ball (0 : ℝ^1) 1).indicator
          (baseRepresentative (u : W^{1,1}(ball (0 : ℝ^1) 1))) ((-2 : ℝ) • x)) ∧
      ‖∇ (v : W^{1,1}(ball (0 : ℝ^1) 1))‖ =
        ‖∇ (u : W^{1,1}(ball (0 : ℝ^1) 1))‖ := by
  have hsub : (fun x : ℝ^1 ↦ (-2 : ℝ) • x) ⁻¹' ball 0 1 ⊆ ball 0 1 := by
    intro x hx
    simp only [mem_preimage, mem_ball, dist_zero_right, norm_smul,
      Real.norm_eq_abs] at hx ⊢
    norm_num at hx
    linarith [norm_nonneg x]
  refine ⟨dilationW1p0CLM (by norm_num) measurableSet_ball isOpen_ball (-2)
    (by norm_num) hsub u, ?_, ?_⟩
  · exact dilationW1p0ToW1p_base_ae (by norm_num) measurableSet_ball
      measurableSet_ball (-2) (by norm_num) u
  · rw [norm_wkpGradientCLM_dilationW1p0CLM]
    norm_num

end PDE.Examples.SobolevRescaling
