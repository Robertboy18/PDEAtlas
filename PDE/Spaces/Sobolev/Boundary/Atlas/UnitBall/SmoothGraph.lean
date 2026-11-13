/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary
public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal.Norm

/-!
# Smooth graph geometry of the Euclidean unit ball

A linear isometry sends a chosen boundary point to the south pole. In these
coordinates the boundary is the lower hemisphere `-sqrt (1 - ‖t‖²)`, with the
ball above its graph. This constructs the raw graph data in every positive
dimension and at every differentiability order.
-/

@[expose] public noncomputable section

open Metric Set Filter
open scoped Topology

namespace SobolevSpace.Boundary.Atlas.UnitBall

open Trace.HalfSpace

/-- The unit ball has raw smooth graph boundary in every positive dimension. -/
theorem hasContDiffGraphBoundary (n : ℕ) [Fact (0 < n)] (k : ℕ∞) :
    HasContDiffGraphBoundary k (domain n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fact.out : 0 < n))
  intro x hx
  have hxnorm : ‖x‖ = 1 := by
    simpa [domain, frontier_ball (0 : ℝ^(d + 1)) one_ne_zero,
      mem_sphere, dist_zero_right] using hx
  let p : ℝ^(d + 1) := -EuclideanSpace.single (Fin.last d) (1 : ℝ)
  have hp : ‖p‖ = 1 := by simp [p, PiLp.norm_single]
  let r : ℝ^(d + 1) ≃ₗᵢ[ℝ] ℝ^(d + 1) :=
    (ℝ ∙ (x - p))ᗮ.reflection
  have hr : r x = p := Submodule.reflection_sub (hxnorm.trans hp.symm)
  let e := r.toContinuousLinearEquiv.trans tangentialNormalContinuousLinearEquiv
  have hex : e x = (0, -1) := by
    change splitTangentialNormal (r x) = _
    rw [hr]
    ext i <;> simp [p]
  let g (t : ℝ^d) := -Real.sqrt (1 - ‖t‖ ^ 2)
  have hg : ContDiffOn ℝ k g (ball 0 1) := by
    apply ((contDiffOn_const.sub (contDiff_norm_sq ℝ).contDiffOn).sqrt ?_).neg
    intro t ht
    have ht' : ‖t‖ < 1 := by simpa [mem_ball, dist_zero_right] using ht
    nlinarith [norm_nonneg t]
  refine ⟨e, g, ball 0 1, isOpen_ball, ?_, hg, ?_, ?_⟩
  · simp [hex]
  · simp [hex, g]
  · have ht : ∀ᶠ y in 𝓝 x, ‖(e y).1‖ < 1 :=
      (e.continuous.fst.norm.continuousAt.eventually_lt continuousAt_const
        (by simp [hex]))
    have hn : ∀ᶠ y in 𝓝 x, (e y).2 < 0 :=
      (e.continuous.snd.continuousAt.eventually_lt continuousAt_const
        (by simp [hex]))
    filter_upwards [ht, hn] with y hyt hyn
    have hnorm : ‖y‖ ^ 2 = ‖(e y).1‖ ^ 2 + (e y).2 ^ 2 := by
      simpa only [e, ContinuousLinearEquiv.trans_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        tangentialNormalContinuousLinearEquiv_apply, r.norm_map] using
        norm_sq_eq_splitTangentialNormal (r y)
    have hrad : 0 ≤ 1 - ‖(e y).1‖ ^ 2 := by nlinarith [norm_nonneg (e y).1]
    have hsquare := Real.sq_sqrt hrad
    have hsqrt := Real.sqrt_nonneg (1 - ‖(e y).1‖ ^ 2)
    change y ∈ ball 0 1 ↔ -Real.sqrt (1 - ‖(e y).1‖ ^ 2) < (e y).2
    rw [mem_ball, dist_zero_right]
    constructor
    · intro hy
      nlinarith [norm_nonneg y]
    · intro hy
      nlinarith [norm_nonneg y]

end SobolevSpace.Boundary.Atlas.UnitBall
