/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Quadratic

/-!
# Interior quadratic contacts on a ball

A nonnegative function with a value at most one in the half ball has interior
lower contacts for every vertex in a ball of radius `1/8`. Aperture `32` keeps
all these contacts inside the ball of radius `15/16`, with value at most `5/4`.
The strict separation follows from the triangle inequality and comparison with
the reference point. No differential inequality is needed for this geometry.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Sliding a paraboloid from a nearby vertex gives a low contact strictly inside
the unit ball. The boundary separation is derived from nonnegativity. -/
theorem exists_quadratic_contact_unitBall
    {u : E → ℝ} (hu : ContinuousOn u (closedBall 0 1))
    (hnonneg : ∀ x ∈ closedBall (0 : E) 1, 0 ≤ u x)
    {x₀ y : E} (hx₀ : x₀ ∈ closedBall (0 : E) (1 / 2))
    (hsmall : u x₀ ≤ 1) (hy : y ∈ closedBall x₀ (1 / 8)) :
    ∃ x ∈ ball (0 : E) (15 / 16), u x ≤ 5 / 4 ∧
      IsMinOn (quadraticTilt u 32 y) (closedBall 0 1) x := by
  have hx₀norm : ‖x₀‖ ≤ 1 / 2 := by simpa using hx₀
  have hx₀unit : x₀ ∈ closedBall (0 : E) 1 :=
    closedBall_subset_closedBall (by norm_num) hx₀
  have hynear : ‖y - x₀‖ ≤ 1 / 8 := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hx₀near : ‖x₀ - y‖ ≤ 1 / 8 := by rwa [norm_sub_rev]
  have hynorm : ‖y‖ ≤ 5 / 8 := by
    have htriangle := norm_add_le (y - x₀) x₀
    rw [sub_add_cancel] at htriangle
    linarith
  have htest : quadraticTilt u 32 y x₀ ≤ 5 / 4 := by
    have hsquare := sq_le_sq₀ (norm_nonneg (x₀ - y)) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hbound := hsquare.mpr hx₀near
    dsimp [quadraticTilt]
    nlinarith
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn
    ⟨x₀, hx₀unit⟩ (continuousOn_quadraticTilt hu 32 y)
  have hvalue : quadraticTilt u 32 y x ≤ 5 / 4 :=
    (hmin hx₀unit).trans htest
  have hxlow : u x ≤ 5 / 4 := by
    dsimp [quadraticTilt] at hvalue
    nlinarith [sq_nonneg ‖x - y‖]
  refine ⟨x, ?_, hxlow, hmin⟩
  rw [mem_ball, dist_zero_right]
  by_contra hfar
  have hnorm : 15 / 16 ≤ ‖x‖ := le_of_not_gt hfar
  have htriangle := norm_add_le (x - y) y
  rw [sub_add_cancel] at htriangle
  have hdist : 5 / 16 ≤ ‖x - y‖ := by linarith
  have hsquare := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 5 / 16)
    (norm_nonneg (x - y))).mpr hdist
  dsimp [quadraticTilt] at hvalue
  nlinarith [hnonneg x hx]

/-- Every nearby vertex belongs to the image of the compactly localized contact set. -/
theorem closedBall_subset_image_quadraticContactMap
    {u : E → ℝ} (hu : ContinuousOn u (closedBall 0 1))
    (hreg : DifferentiableOn ℝ u (ball 0 1))
    (hnonneg : ∀ x ∈ closedBall (0 : E) 1, 0 ≤ u x)
    {x₀ : E} (hx₀ : x₀ ∈ closedBall (0 : E) (1 / 2)) (hsmall : u x₀ ≤ 1) :
    closedBall x₀ (1 / 8) ⊆ quadraticContactMap u 32 ''
      quadraticContactSet u 32 (closedBall 0 1) (closedBall 0 (15 / 16))
        (closedBall x₀ (1 / 8)) := by
  intro y hy
  obtain ⟨x, hx, _, hmin⟩ := exists_quadratic_contact_unitBall hu hnonneg hx₀ hsmall hy
  have hxunit : x ∈ ball (0 : E) 1 := ball_subset_ball (by norm_num) hx
  have hlocal := hmin.isLocalMin (closedBall_mem_nhds_of_mem hxunit)
  have hvertex := quadraticContactMap_eq_of_isLocalMin (by norm_num : (32 : ℝ) ≠ 0)
    (hreg.differentiableAt (isOpen_ball.mem_nhds hxunit)) hlocal
  refine ⟨x, ⟨ball_subset_closedBall hx, ?_, ?_⟩, hvertex⟩
  · rwa [hvertex]
  · simpa only [hvertex] using hmin

/-- Every contact with a nearby vertex has controlled height, by comparing its
supporting paraboloid with the reference point. -/
theorem quadraticContactSet_unitBall_subset_sublevel
    {u : E → ℝ} {x₀ : E} (hx₀ : x₀ ∈ closedBall (0 : E) (1 / 2))
    (hsmall : u x₀ ≤ 1) :
    quadraticContactSet u 32 (closedBall 0 1) (closedBall 0 (15 / 16))
        (closedBall x₀ (1 / 8)) ⊆
      ball (0 : E) 1 ∩ {x | u x ≤ 5 / 4} := by
  intro x hx
  have hx₀unit : x₀ ∈ closedBall (0 : E) 1 :=
    closedBall_subset_closedBall (by norm_num) hx₀
  have hnear : ‖x₀ - quadraticContactMap u 32 x‖ ≤ 1 / 8 := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hx.2.1
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 8)).mpr hnear
  have htest := hx.2.2 hx₀unit
  refine ⟨closedBall_subset_ball (by norm_num) hx.1, ?_⟩
  dsimp [quadraticTilt] at htest
  change u x ≤ 5 / 4
  nlinarith [sq_nonneg ‖x - quadraticContactMap u 32 x‖]

end PDE.Analysis
