/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Rigid-coordinate boundary graphs

The usual description of differentiable boundary uses rotations and translations, with
a differentiable graph height on a tangential ball and a strict epigraph condition on
an ambient ball. It implies the local graph predicate at the same order: the translation
is absorbed into the height, leaving the linear isometry as the coordinate change.

The center is proved to lie on the graph. Indeed, every neighborhood of a boundary
point meets both the domain and its complement, so continuity forces the signed
height to vanish there. This equality is not an extra hypothesis.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology
open SobolevSpace.Trace.HalfSpace

namespace SobolevSpace.Boundary

variable {n : ℕ} {Ω : Set (ℝ^(n + 1))}

/-- Local strict epigraphs in rigid coordinates give `C^m` graph boundary.
The graph height needs regularity only on its tangential ball, also at infinite order. -/
theorem hasContDiffGraphBoundary_of_rigid_local_graph {m : ℕ∞}
    (hgraph : ∀ x ∈ frontier Ω,
      ∃ R : (ℝ^(n + 1)) ≃ᵃⁱ[ℝ] (ℝ^(n + 1)), ∃ r : ℝ, ∃ g : ℝ^n → ℝ,
        0 < r ∧ ContDiffOn ℝ m g (ball (splitTangentialNormal (R x)).1 r) ∧
        ∀ y ∈ ball x r,
          y ∈ Ω ↔ g (splitTangentialNormal (R y)).1 < (splitTangentialNormal (R y)).2) :
    HasContDiffGraphBoundary m Ω := by
  intro x hx
  obtain ⟨R, r, g, hr, hg, hside⟩ := hgraph x hx
  let e := R.linearIsometryEquiv.toContinuousLinearEquiv.trans
    tangentialNormalContinuousLinearEquiv
  let a := splitTangentialNormal (R 0)
  have hcoord (y : ℝ^(n + 1)) : splitTangentialNormal (R y) = e y + a := by
    change tangentialNormalContinuousLinearEquiv (R y) =
      tangentialNormalContinuousLinearEquiv (R.linearIsometryEquiv y) +
        tangentialNormalContinuousLinearEquiv (R 0)
    rw [← map_add]
    congr 1
    simpa only [vadd_eq_add, add_zero] using R.map_vadd (0 : ℝ^(n + 1)) y
  let γ : ℝ^n → ℝ := fun z ↦ g (z + a.1) - a.2
  let s := (fun z : ℝ^n ↦ z + a.1) ⁻¹' ball (splitTangentialNormal (R x)).1 r
  have hs : IsOpen s := isOpen_ball.preimage (continuous_id.add continuous_const)
  have hxs : (e x).1 ∈ s := by
    change (e x).1 + a.1 ∈ ball (splitTangentialNormal (R x)).1 r
    simpa only [hcoord, Prod.fst_add] using
      (mem_ball_self hr : (e x).1 + a.1 ∈ ball ((e x).1 + a.1) r)
  have hγ : ContDiffOn ℝ m γ s := by
    have hadd : ContDiff ℝ m (fun z : ℝ^n ↦ z + a.1) :=
      contDiff_id.add contDiff_const
    exact (hg.comp hadd.contDiffOn fun _ hz ↦ hz).sub contDiffOn_const
  have hside' : ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ γ (e y).1 < (e y).2 := by
    filter_upwards [ball_mem_nhds x hr] with y hy
    rw [hside y hy, hcoord]
    change g ((e y).1 + a.1) < (e y).2 + a.2 ↔
      g ((e y).1 + a.1) - a.2 < (e y).2
    exact sub_lt_iff_lt_add.symm
  let f : ℝ^(n + 1) → ℝ := fun y ↦ (e y).2 - γ (e y).1
  have hf : ContinuousAt f x :=
    e.continuous.continuousAt.snd.sub
      ((hγ.contDiffAt (hs.mem_nhds hxs)).continuousAt.comp
        (f := fun y ↦ (e y).1) e.continuous.continuousAt.fst)
  have hpos : ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ 0 < f y :=
    hside'.mono fun _ hy ↦ hy.trans sub_pos.symm
  have hx' : x ∈ closure Ω ∩ closure Ωᶜ := by
    rwa [← frontier_eq_closure_inter_closure]
  have hle : f x ≤ 0 := le_of_tendsto_of_frequently hf <|
    ((mem_closure_iff_frequently.mp hx'.2).and_eventually hpos).mono fun y hy ↦
      le_of_not_gt fun h ↦ hy.1 (hy.2.mpr h)
  have hge : 0 ≤ f x := ge_of_tendsto_of_frequently hf <|
    ((mem_closure_iff_frequently.mp hx'.1).and_eventually hpos).mono fun y hy ↦
      (hy.2.mp hy.1).le
  exact ⟨e, γ, s, hs, hxs, hγ, sub_eq_zero.mp (le_antisymm hle hge), hside'⟩

/-- Local strict epigraphs of C1 functions in rigid coordinates give C1 graph boundary.
The graph height needs regularity only on its tangential ball. -/
theorem hasC1GraphBoundary_of_rigid_local_graph
    (hgraph : ∀ x ∈ frontier Ω,
      ∃ R : (ℝ^(n + 1)) ≃ᵃⁱ[ℝ] (ℝ^(n + 1)), ∃ r : ℝ, ∃ g : ℝ^n → ℝ,
        0 < r ∧ ContDiffOn ℝ 1 g (ball (splitTangentialNormal (R x)).1 r) ∧
        ∀ y ∈ ball x r,
          y ∈ Ω ↔ g (splitTangentialNormal (R y)).1 < (splitTangentialNormal (R y)).2) :
    HasC1GraphBoundary Ω :=
  hasContDiffGraphBoundary_one_iff.mp (hasContDiffGraphBoundary_of_rigid_local_graph hgraph)

end SobolevSpace.Boundary
