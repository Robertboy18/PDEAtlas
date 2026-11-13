/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff
import PDE.FDeriv.PartialDeriv.Support

/-!
# Support of the cutoff Hessian

The cutoff is constant on the inner ball and vanishes outside the outer
ball. Its second derivatives therefore live on the closed annulus.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Set
open scoped Topology

namespace SobolevSpace.Approximation

/-- The cutoff Hessian vanishes outside the closed annulus between radii `R` and `2 * R`. -/
theorem partialDeriv_partialDeriv_cutoff_eq_zero_of_notMem_annulus
    {n : ℕ} {R : ℝ} (hR : 0 < R) (i j : Fin n) {x : ℝ^n}
    (hx : x ∉ Metric.closedBall (0 : ℝ^n) (2 * R) \ Metric.ball 0 R) :
    (∂[j] (∂[i] (cutoff R))) x = 0 := by
  by_cases hinner : x ∈ Metric.ball (0 : ℝ^n) R
  · have heq : cutoff R =ᶠ[𝓝 x] (fun _ : ℝ^n ↦ (1 : ℝ)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hinner] with y hy
      exact cutoff_eq_one_of_mem_closedBall hR (Metric.ball_subset_closedBall hy)
    simpa only [iteratedPartialDeriv, PDE.partialDeriv_const] using
      (heq.iteratedPartialDeriv [j, i]).eq_of_nhds
  · have houter : x ∉ Metric.closedBall (0 : ℝ^n) (2 * R) :=
      fun hxball ↦ hx ⟨hxball, hinner⟩
    apply PDE.partialDeriv_eq_zero_of_notMem_tsupport j
    intro hxderiv
    exact houter (tsupport_cutoff_subset_closedBall hR
      (PDE.tsupport_partialDeriv_subset i hxderiv))

end SobolevSpace.Approximation
