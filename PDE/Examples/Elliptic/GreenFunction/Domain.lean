/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Dirichlet
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Green's representation formula on a disk and a ball

Green's representation formula `dirichlet_representation` at the center of the unit
ball, for `u = 2 - |z|²` with `-Δu = 2n` and boundary value `1`. On the disk the
corrector at the center is zero, so the boundary term is the normal derivative of the
logarithmic kernel (`disk_quadratic_representation`). In dimension three the corrector
is the nonzero constant `Φ(e₀)` (`spatial_quadratic_representation`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.GreenFunction

open Metric Set MeasureTheory SobolevSpace SobolevSpace.Boundary
open SobolevSpace.Trace.C1 Geometry.SurfaceMeasure PotentialTheory
open scoped Topology Gradient

/-- The function `2 - |z|²` on the disk, with boundary value `1`. -/
def diskQuadratic (z : ℝ^2) : ℝ := 2 - z 0 ^ 2 - z 1 ^ 2

/-- `Δ diskQuadratic = -4`, so the source `-Δ diskQuadratic` is `4`. -/
theorem laplacian_diskQuadratic (z : ℝ^2) :
    laplacian diskQuadratic z = -4 := by
  unfold diskQuadratic
  cas

/-- The logarithmic Green representation on the disk: the boundary term plus the volume
term recover the value `2` of the solution at the center. -/
theorem disk_quadratic_representation :
    let hgraph : HasC1GraphBoundary (ball (0 : ℝ^2) 1) :=
      (Atlas.UnitBall.hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl
    letI := hgraph.c1ExtensionAtlas isOpen_ball isBounded_ball
    IntegrableOn (fun z : ℝ^2 ↦ 4 * fundamentalSolution 2 z) (ball 0 1) ∧
      Integrable (normalFlux (Ω := ball (0 : ℝ^2) 1) (∇ (fundamentalSolution 2)))
        (surfaceMeasure (ball (0 : ℝ^2) 1)) ∧
      (2 : ℝ) = -(∫ z, normalFlux (Ω := ball (0 : ℝ^2) 1)
        (∇ (fundamentalSolution 2)) z ∂surfaceMeasure (ball (0 : ℝ^2) 1)) +
        ∫ z in ball (0 : ℝ^2) 1, 4 * fundamentalSolution 2 z := by
  let hgraph : HasC1GraphBoundary (ball (0 : ℝ^2) 1) :=
    (Atlas.UnitBall.hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl
  let := hgraph.c1ExtensionAtlas isOpen_ball isBounded_ball
  have hu : ContDiff ℝ 2 diskQuadratic := by
    unfold diskQuadratic
    fun_prop
  have huΩ : ContDiffUpToBoundary 2 diskQuadratic (ball 0 1) :=
    ContDiffUpToBoundary.of_contDiff hu isBounded_ball
  have hφ : ContDiffUpToBoundary 2 (fun _ : ℝ^2 ↦ (0 : ℝ)) (ball 0 1) :=
    ContDiffUpToBoundary.of_contDiff contDiff_const isBounded_ball
  have hnorm {z : ℝ^2} (hz : z ∈ frontier (ball (0 : ℝ^2) 1)) : ‖z‖ = 1 := by
    simpa only [frontier_ball _ one_ne_zero, mem_sphere, dist_zero_right] using hz
  have hcφ : EqOn (fun _ : ℝ^2 ↦ (0 : ℝ))
      (fun z ↦ fundamentalSolution 2 (z - 0)) (frontier (ball 0 1)) := by
    intro z hz
    simp only [sub_zero, fundamentalSolution_two, hnorm hz, Real.log_one, mul_zero]
  have hb : EqOn diskQuadratic (fun _ ↦ (1 : ℝ)) (frontier (ball (0 : ℝ^2) 1)) := by
    intro z hz
    have hs := EuclideanSpace.real_norm_sq_eq z
    rw [hnorm hz] at hs
    simp only [Fin.sum_univ_two, one_pow] at hs
    dsimp only [diskQuadratic]
    linarith
  have he := PotentialTheory.GreenFunction.Domain.dirichlet_representation
    (by norm_num : 2 ≤ 2) isOpen_ball isBounded_ball hgraph huΩ hu.continuous.continuousOn
    (mem_ball_self (by norm_num : (0 : ℝ) < 1)) hφ continuous_const.continuousOn
    (fun z _ ↦ laplacian_const 0 z) hcφ
    (f := fun _ ↦ 4) (by intro z _; rw [laplacian_diskQuadratic]; norm_num) hb
  have hg : EqOn (hφ.of_le (show 1 ≤ 2 by omega)).completedGradient (fun _ ↦ 0)
      (closure (ball (0 : ℝ^2) 1)) := by
    simpa only [gradient_fun_const'] using
      (hφ.of_le (show 1 ≤ 2 by omega)).completedGradient_eq_gradient_extension isOpen_ball
        contDiff_const (fun _ _ ↦ rfl)
  have hnormal : (fun z ↦ normalFlux (Ω := ball (0 : ℝ^2) 1)
      (fun w ↦ ∇ (fun y ↦ fundamentalSolution 2 (y - 0)) w -
        (hφ.of_le (show 1 ≤ 2 by omega)).completedGradient w) z)
      =ᵐ[surfaceMeasure (ball (0 : ℝ^2) 1)]
      normalFlux (Ω := ball (0 : ℝ^2) 1) (∇ (fundamentalSolution 2)) := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with z hz
    simp only [sub_zero, normalFlux_eq_inner _ hz, hg (frontier_subset_closure hz)]
  unfold PotentialTheory.GreenFunction.Domain.greenKernel
    PotentialTheory.GreenFunction.Domain.greenKernelGradient at he
  simp only [sub_zero, one_mul, diskQuadratic, PiLp.zero_apply, zero_pow two_ne_zero] at he
  simp only [sub_zero] at hnormal
  refine ⟨he.1, he.2.1.congr hnormal, ?_⟩
  rw [integral_congr_ae hnormal] at he
  exact he.2.2

/-- `Δ (2 - |w|²) = -6` in dimension three, so the source is `6`. -/
theorem laplacian_spatial_quadratic (z : ℝ^3) :
    laplacian (fun w : ℝ^3 ↦ 2 - w 0 ^ 2 - w 1 ^ 2 - w 2 ^ 2) z = -6 := by
  cas

/-- The Newtonian representation in dimension three, with source `6`, boundary value
`1`, and the nonzero center corrector `Φ(e₀)`. -/
theorem spatial_quadratic_representation :
    let hgraph : HasC1GraphBoundary (ball (0 : ℝ^3) 1) :=
      (Atlas.UnitBall.hasContDiffGraphBoundary 3 1).hasC1GraphBoundary le_rfl
    letI := hgraph.c1ExtensionAtlas isOpen_ball isBounded_ball
    let c := fundamentalSolution 3 (EuclideanSpace.single 0 1)
    IntegrableOn (fun z : ℝ^3 ↦ 6 * (fundamentalSolution 3 z - c)) (ball 0 1) ∧
      Integrable (normalFlux (Ω := ball (0 : ℝ^3) 1) (∇ (fundamentalSolution 3)))
        (surfaceMeasure (ball (0 : ℝ^3) 1)) ∧
      (2 : ℝ) = -(∫ z, normalFlux (Ω := ball (0 : ℝ^3) 1)
        (∇ (fundamentalSolution 3)) z ∂surfaceMeasure (ball (0 : ℝ^3) 1)) +
        ∫ z in ball (0 : ℝ^3) 1, 6 * (fundamentalSolution 3 z - c) := by
  let hgraph : HasC1GraphBoundary (ball (0 : ℝ^3) 1) :=
    (Atlas.UnitBall.hasContDiffGraphBoundary 3 1).hasC1GraphBoundary le_rfl
  let := hgraph.c1ExtensionAtlas isOpen_ball isBounded_ball
  let c := fundamentalSolution 3 (EuclideanSpace.single 0 1)
  let u := fun z : ℝ^3 ↦ 2 - z 0 ^ 2 - z 1 ^ 2 - z 2 ^ 2
  have hu : ContDiff ℝ 2 u := by
    dsimp only [u]
    fun_prop
  have huΩ : ContDiffUpToBoundary 2 u (ball 0 1) :=
    ContDiffUpToBoundary.of_contDiff hu isBounded_ball
  have hφ : ContDiffUpToBoundary 2 (fun _ : ℝ^3 ↦ c) (ball 0 1) :=
    ContDiffUpToBoundary.of_contDiff contDiff_const isBounded_ball
  have hnorm {z : ℝ^3} (hz : z ∈ frontier (ball (0 : ℝ^3) 1)) : ‖z‖ = 1 := by
    simpa only [frontier_ball _ one_ne_zero, mem_sphere, dist_zero_right] using hz
  have hcφ : EqOn (fun _ : ℝ^3 ↦ c)
      (fun z ↦ fundamentalSolution 3 (z - 0)) (frontier (ball 0 1)) := by
    intro z hz
    apply fundamentalSolution_eq_of_norm_eq
    simp only [PiLp.norm_single, norm_one, sub_zero, hnorm hz]
  have hb : EqOn u (fun _ ↦ (1 : ℝ)) (frontier (ball (0 : ℝ^3) 1)) := by
    intro z hz
    have hs := EuclideanSpace.real_norm_sq_eq z
    rw [hnorm hz] at hs
    simp only [Fin.sum_univ_three, one_pow] at hs
    dsimp only [u]
    linarith
  have he := PotentialTheory.GreenFunction.Domain.dirichlet_representation
    (by norm_num : 2 ≤ 3) isOpen_ball isBounded_ball hgraph huΩ hu.continuous.continuousOn
    (mem_ball_self (by norm_num : (0 : ℝ) < 1)) hφ continuous_const.continuousOn
    (fun z _ ↦ laplacian_const c z) hcφ
    (f := fun _ ↦ 6) (by intro z _; rw [laplacian_spatial_quadratic]; norm_num) hb
  have hg : EqOn (hφ.of_le (show 1 ≤ 2 by omega)).completedGradient (fun _ ↦ 0)
      (closure (ball (0 : ℝ^3) 1)) := by
    simpa only [gradient_fun_const'] using
      (hφ.of_le (show 1 ≤ 2 by omega)).completedGradient_eq_gradient_extension isOpen_ball
        contDiff_const (fun _ _ ↦ rfl)
  have hnormal : (fun z ↦ normalFlux (Ω := ball (0 : ℝ^3) 1)
      (fun w ↦ ∇ (fun y ↦ fundamentalSolution 3 (y - 0)) w -
        (hφ.of_le (show 1 ≤ 2 by omega)).completedGradient w) z)
      =ᵐ[surfaceMeasure (ball (0 : ℝ^3) 1)]
      normalFlux (Ω := ball (0 : ℝ^3) 1) (∇ (fundamentalSolution 3)) := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with z hz
    simp only [sub_zero, normalFlux_eq_inner _ hz, hg (frontier_subset_closure hz)]
  unfold PotentialTheory.GreenFunction.Domain.greenKernel
    PotentialTheory.GreenFunction.Domain.greenKernelGradient at he
  simp only [sub_zero, one_mul, u, PiLp.zero_apply, zero_pow two_ne_zero] at he
  simp only [sub_zero] at hnormal
  refine ⟨he.1, he.2.1.congr hnormal, ?_⟩
  rw [integral_congr_ae hnormal] at he
  exact he.2.2

end PDE.Examples.GreenFunction
