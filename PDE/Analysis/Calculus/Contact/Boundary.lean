/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Quadratic

/-!
# Quadratic contacts separated from a spherical boundary

A function nonnegative on the boundary and at most `-1` at a reference point
has interior quadratic contacts of sufficiently small aperture. The sublevel
set at height `-1/2` provides compact localization without requiring a numerical
distance between contacts and the boundary.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A negative sublevel of a function nonnegative on the sphere is interior. -/
theorem negative_sublevel_closedBall_subset_ball
    {w : E → ℝ} {R h : ℝ} (hh : h < 0)
    (hboundary : ∀ x ∈ sphere (0 : E) R, 0 ≤ w x) :
    closedBall (0 : E) R ∩ {x | w x ≤ h} ⊆ ball (0 : E) R := by
  intro x hx
  have hxnorm : ‖x‖ ≤ R := by simpa using hx.1
  rw [mem_ball, dist_zero_right]
  by_contra hn
  have hxsphere : x ∈ sphere (0 : E) R := by
    simpa only [mem_sphere, dist_zero_right] using hxnorm.antisymm (le_of_not_gt hn)
  exact (hh.not_ge ((hboundary x hxsphere).trans hx.2)).elim

/-- Continuous negative sublevels on a closed ball are compact. -/
theorem isCompact_sublevel_closedBall
    {w : E → ℝ} {R h : ℝ} (hw : ContinuousOn w (closedBall 0 R)) :
    IsCompact (closedBall (0 : E) R ∩ {x | w x ≤ h}) := by
  exact (isCompact_closedBall (0 : E) R).of_isClosed_subset
    (isClosed_closedBall.isClosed_le hw continuousOn_const) inter_subset_left

/-- A small-aperture tilt retains a strictly negative minimum. -/
theorem exists_quadratic_contact_of_boundary_nonneg
    {w : E → ℝ} {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ) (hscale : κ * R ^ 2 ≤ 1)
    (hw : ContinuousOn w (closedBall 0 R))
    {x₀ y : E} (hx₀ : x₀ ∈ closedBall (0 : E) (R / 2)) (hsmall : w x₀ ≤ -1)
    (hy : y ∈ closedBall (0 : E) (R / 2)) :
    ∃ x ∈ closedBall (0 : E) R ∩ {x | w x ≤ -(1 / 2)},
      IsMinOn (quadraticTilt w κ y) (closedBall 0 R) x := by
  have hx₀norm : ‖x₀‖ ≤ R / 2 := by simpa using hx₀
  have hynorm : ‖y‖ ≤ R / 2 := by simpa using hy
  have hdist : ‖x₀ - y‖ ≤ R := (norm_sub_le _ _).trans (by linarith)
  have hsq := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hdist
  have htest : quadraticTilt w κ y x₀ ≤ -(1 / 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hsq hκ.le
    dsimp [quadraticTilt]
    nlinarith
  have hx₀R : x₀ ∈ closedBall (0 : E) R :=
    closedBall_subset_closedBall (by linarith) hx₀
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    ⟨x₀, hx₀R⟩ (continuousOn_quadraticTilt hw κ y)
  have hvalue := (hmin hx₀R).trans htest
  refine ⟨x, ⟨hx, ?_⟩, hmin⟩
  change w x ≤ -(1 / 2)
  dsimp [quadraticTilt] at hvalue
  have hterm := mul_nonneg hκ.le (sq_nonneg ‖x - y‖)
  linarith

/-- The half ball of vertices is covered by contacts in a compact negative
sublevel. Boundary nonnegativity makes all these contacts interior. -/
theorem closedBall_subset_image_quadraticContactMap_of_boundary_nonneg
    {w : E → ℝ} {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ) (hscale : κ * R ^ 2 ≤ 1)
    (hw : ContinuousOn w (closedBall 0 R))
    (hreg : DifferentiableOn ℝ w (ball 0 R))
    (hboundary : ∀ x ∈ sphere (0 : E) R, 0 ≤ w x)
    {x₀ : E} (hx₀ : x₀ ∈ closedBall (0 : E) (R / 2)) (hsmall : w x₀ ≤ -1) :
    closedBall (0 : E) (R / 2) ⊆ quadraticContactMap w κ ''
      quadraticContactSet w κ (closedBall 0 R)
        (closedBall 0 R ∩ {x | w x ≤ -(1 / 2)}) (closedBall 0 (R / 2)) := by
  intro y hy
  obtain ⟨x, hx, hmin⟩ :=
    exists_quadratic_contact_of_boundary_nonneg hR hκ hscale hw hx₀ hsmall hy
  have hxball := negative_sublevel_closedBall_subset_ball
    (by norm_num : -(1 / 2 : ℝ) < 0) hboundary hx
  have hlocal := hmin.isLocalMin (closedBall_mem_nhds_of_mem hxball)
  have hvertex := quadraticContactMap_eq_of_isLocalMin hκ.ne'
    (hreg.differentiableAt (isOpen_ball.mem_nhds hxball)) hlocal
  exact ⟨x, ⟨hx, by rwa [hvertex], by simpa only [hvertex] using hmin⟩, hvertex⟩

end PDE.Analysis
