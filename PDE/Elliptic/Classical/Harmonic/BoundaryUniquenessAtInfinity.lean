/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.WeakMaximumPrinciple.BoundedDomain

/-!
# Harmonic Dirichlet uniqueness with decay at infinity

On any open Euclidean domain, a harmonic function continuous up to the
boundary, zero on the boundary, and tending to zero at spatial infinity
vanishes throughout the closure. Apply the bounded-domain maximum principle
on intersections with large balls and then let the exterior bound tend to zero.

## Main results

* `IsHarmonicPDE.eq_zero_on_closure_of_boundary_zero_of_tendsto_zero`: a harmonic function with
  zero boundary values and zero limit at infinity vanishes on the closure of an open domain.
-/

@[expose] public section

namespace LaplacianEquation

open Set Filter Topology

/-- On an open set `Ω`, a harmonic function continuous on the closure, zero on the frontier and
tending to zero at infinity satisfies `u ≤ 0` in `Ω`. -/
private theorem harmonic_nonpos_of_boundary_zero_of_tendsto_zero
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} {u : ℝ^n → ℝ}
    (hu : IsHarmonicPDE n u Ω) (hΩ : IsOpen Ω)
    (hc : ContinuousOn u (closure Ω)) (hb : ∀ x ∈ frontier Ω, u x = 0)
    (hi : Tendsto u (cocompact (ℝ^n)) (𝓝 0)) {x : ℝ^n} (hx : x ∈ Ω) :
    u x ≤ 0 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R, hR⟩ := Metric.closedBall_compl_subset_of_mem_cocompact
    (hi.eventually (gt_mem_nhds hε)) (0 : ℝ^n)
  let r : ℝ := max R ‖x‖ + 1
  have hrR : R < r := by dsimp [r]; linarith [le_max_left R ‖x‖]
  have hrx : ‖x‖ < r := by dsimp [r]; linarith [le_max_right R ‖x‖]
  have hboundary : ∀ y ∈ frontier (Ω ∩ Metric.ball 0 r), u y ≤ ε := by
    intro y hy
    rcases frontier_inter_subset Ω (Metric.ball 0 r) hy with hy | hy
    · rw [hb y hy.1]
      exact hε.le
    · have hsphere := Metric.frontier_ball_subset_sphere hy.2
      have hnorm : ‖y‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hsphere
      exact (hR (by simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
        not_le, hnorm] using hrR)).le
  have hbound := (hu.mono inter_subset_left).le_on_closure_of_boundary_le
    (hΩ.inter Metric.isOpen_ball)
    (Metric.isBounded_ball.subset inter_subset_right)
    (hc.mono (closure_mono inter_subset_left)) hboundary x
    (subset_closure ⟨hx, by simpa only [Metric.mem_ball, dist_zero_right] using hrx⟩)
  simpa only [zero_add] using hbound

/-- A harmonic function with zero boundary values and zero limit at infinity
vanishes on the closure of any open Euclidean domain. -/
theorem IsHarmonicPDE.eq_zero_on_closure_of_boundary_zero_of_tendsto_zero
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} {u : ℝ^n → ℝ}
    (hu : IsHarmonicPDE n u Ω) (hΩ : IsOpen Ω)
    (hc : ContinuousOn u (closure Ω)) (hb : ∀ x ∈ frontier Ω, u x = 0)
    (hi : Tendsto u (cocompact (ℝ^n)) (𝓝 0)) :
    ∀ x ∈ closure Ω, u x = 0 := by
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · have hle := harmonic_nonpos_of_boundary_zero_of_tendsto_zero hu hΩ hc hb hi hxΩ
    have hge := harmonic_nonpos_of_boundary_zero_of_tendsto_zero hu.neg hΩ hc.neg
      (fun y hy ↦ by simp only [Pi.neg_apply, hb y hy, neg_zero])
      (by simpa only [Pi.neg_def, neg_zero] using hi.neg) hxΩ
    change -u x ≤ 0 at hge
    exact le_antisymm hle (neg_nonpos.mp hge)
  · exact hb x (by
      rw [frontier, hΩ.interior_eq]
      exact ⟨hx, hxΩ⟩)

end LaplacianEquation
