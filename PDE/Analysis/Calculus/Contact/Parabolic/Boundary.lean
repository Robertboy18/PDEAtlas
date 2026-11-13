/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Parabolic.Compact
public import PDE.Analysis.Topology.Order.FirstZero

/-!
# First parabolic contacts separated from the boundary

On a short cylinder, a function nonnegative on the initial and lateral faces
and at most `-1` at a point of the top half ball admits first contacts for an
entire cylinder of vertices. The time width is less than `R² / 8` and the
aperture satisfies `κ R² ≤ 1`. These elementary choices keep all contacts
away from the initial and lateral faces, including in spatial dimension zero.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A positive vertex time separates the gap from the initial face. -/
theorem parabolicQuadraticTilt_pos_at_initial
    {w : E → ℝ → ℝ} {κ : ℝ} {x : E} {v : E × ℝ}
    (hκ : 0 < κ) (hv : 0 < v.2) (hw : 0 ≤ w x 0) :
    0 < parabolicQuadraticTilt w κ v (x, 0) := by
  have hterm := mul_nonneg (show 0 ≤ κ / 2 by positivity) (sq_nonneg ‖x - v.1‖)
  have htime := mul_pos hκ hv
  dsimp [parabolicQuadraticTilt, quadraticTilt]
  nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The spatial gap on the sphere dominates the height of a short cylinder. -/
theorem parabolicQuadraticTilt_pos_at_lateral
    {w : E → ℝ → ℝ} {R κ b : ℝ} {x : E} {t : ℝ} {v : E × ℝ}
    (hR : 0 < R) (hκ : 0 < κ) (hshort : b < R ^ 2 / 8)
    (hx : x ∈ sphere (0 : E) R) (hy : v.1 ∈ closedBall (0 : E) (R / 2))
    (hs : 0 ≤ v.2) (ht : t ≤ b) (hw : 0 ≤ w x t) :
    0 < parabolicQuadraticTilt w κ v (x, t) := by
  have hxnorm : ‖x‖ = R := by simpa only [mem_sphere, dist_zero_right] using hx
  have hynorm : ‖v.1‖ ≤ R / 2 := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hdist : R / 2 ≤ ‖x - v.1‖ := by
    have h := norm_sub_norm_le x v.1
    rw [hxnorm] at h
    linarith
  have hsq := pow_le_pow_left₀ (show 0 ≤ R / 2 by positivity) hdist 2
  have hscaled := mul_le_mul_of_nonneg_left hsq (show 0 ≤ κ / 2 by positivity)
  have htime := mul_le_mul_of_nonneg_left (show t - v.2 ≤ b by linarith) hκ.le
  have hstrict := mul_lt_mul_of_pos_left hshort hκ
  dsimp [parabolicQuadraticTilt, quadraticTilt]
  nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A value below `-1` in the top half ball makes every chosen vertex's gap
negative somewhere, with an aperture bound independent of the function. -/
theorem parabolicQuadraticTilt_neg_at_top
    {w : E → ℝ → ℝ} {R κ b : ℝ} {x : E} {v : E × ℝ}
    (hR : 0 < R) (hκ : 0 < κ) (hscale : κ * R ^ 2 ≤ 1)
    (hx : x ∈ closedBall (0 : E) (R / 2))
    (hy : v.1 ∈ closedBall (0 : E) (R / 2))
    (hs : v.2 ≤ b) (hw : w x b ≤ -1) :
    parabolicQuadraticTilt w κ v (x, b) < 0 := by
  have hxnorm : ‖x‖ ≤ R / 2 := by simpa using hx
  have hynorm : ‖v.1‖ ≤ R / 2 := by simpa using hy
  have hdist : ‖x - v.1‖ ≤ R := (norm_sub_le _ _).trans (by linarith)
  have hsq := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hdist
  have hscaled := mul_le_mul_of_nonneg_left hsq hκ.le
  have htime := mul_nonneg hκ.le (sub_nonneg.mpr hs)
  dsimp [parabolicQuadraticTilt, quadraticTilt]
  nlinarith

/-- Every vertex in the chosen cylinder is recovered by an actual first
contact, supported at all earlier times and spatially interior. -/
theorem cylinder_subset_image_parabolicQuadraticContactMap_of_boundary_nonneg
    {w : E → ℝ → ℝ} {R κ b : ℝ}
    (hR : 0 < R) (hκ : 0 < κ) (hb : 0 < b)
    (hshort : b < R ^ 2 / 8) (hscale : κ * R ^ 2 ≤ 1)
    (hw : ContinuousOn (Function.uncurry w) (closedBall 0 R ×ˢ Icc 0 b))
    (hreg : ∀ p ∈ ball (0 : E) R ×ˢ Ioc 0 b,
      DifferentiableAt ℝ (fun x ↦ w x p.2) p.1)
    (hinitial : ∀ x ∈ closedBall (0 : E) R, 0 ≤ w x 0)
    (hlateral : ∀ x ∈ sphere (0 : E) R, ∀ t ∈ Icc 0 b, 0 ≤ w x t)
    {x₀ : E} (hx₀ : x₀ ∈ closedBall (0 : E) (R / 2)) (hsmall : w x₀ b ≤ -1) :
    closedBall (0 : E) (R / 2) ×ˢ Icc (b / 4) (b / 2) ⊆
      parabolicQuadraticContactMap w κ ''
        parabolicQuadraticContactSet w κ 0 (closedBall 0 R)
          (closedBall 0 R ×ˢ Icc 0 b)
          (closedBall 0 (R / 2) ×ˢ Icc (b / 4) (b / 2)) := by
  intro v hv
  have hs : 0 < v.2 := lt_of_lt_of_le (by positivity : 0 < b / 4) hv.2.1
  have htest : ∃ q ∈ closedBall (0 : E) R ×ˢ Icc 0 b,
      parabolicQuadraticTilt w κ v q ≤ 0 :=
    ⟨(x₀, b), ⟨closedBall_subset_closedBall (by linarith) hx₀, hb.le, le_rfl⟩,
      (parabolicQuadraticTilt_neg_at_top hR hκ hscale hx₀ hv.1
        (by linarith [hv.2.2]) hsmall).le⟩
  obtain ⟨p, hp, hzero, hsupport⟩ := exists_first_zero_with_nonneg_past
    (isCompact_closedBall (0 : E) R) (continuousOn_parabolicQuadraticTilt hw κ v)
    (fun x hx ↦ parabolicQuadraticTilt_pos_at_initial hκ hs (hinitial x hx)) htest
  have hxball : p.1 ∈ ball (0 : E) R := by
    rw [mem_ball, dist_zero_right]
    have hxnorm : ‖p.1‖ ≤ R := by simpa using hp.1
    by_contra hn
    have hxsphere : p.1 ∈ sphere (0 : E) R := by
      simpa only [mem_sphere, dist_zero_right] using hxnorm.antisymm (le_of_not_gt hn)
    have hpos := parabolicQuadraticTilt_pos_at_lateral hR hκ hshort hxsphere
      hv.1 hs.le hp.2.2 (hlateral p.1 hxsphere p.2 ⟨hp.2.1.le, hp.2.2⟩)
    exact (ne_of_gt hpos) hzero
  have hvertex := parabolicQuadraticContactMap_eq_of_support hκ.ne' hp.2.1.le
    (closedBall_mem_nhds_of_mem hxball) (hreg p ⟨hxball, hp.2⟩) hzero hsupport
  refine ⟨p, ⟨⟨hp.1, hp.2.1.le, hp.2.2⟩, ?_, ?_⟩, hvertex⟩
  · rwa [hvertex]
  · simpa only [hvertex] using hsupport

/-- All contacts with these vertices avoid the initial and lateral boundary.
The closed cylinder can therefore be used for compactness, while derivative
estimates are needed only on its spatial interior at positive times. -/
theorem parabolicQuadraticContactSet_subset_interior_of_boundary_nonneg
    {w : E → ℝ → ℝ} {R κ b : ℝ}
    (hR : 0 < R) (hκ : 0 < κ) (hb : 0 < b) (hshort : b < R ^ 2 / 8)
    (hinitial : ∀ x ∈ closedBall (0 : E) R, 0 ≤ w x 0)
    (hlateral : ∀ x ∈ sphere (0 : E) R, ∀ t ∈ Icc 0 b, 0 ≤ w x t) :
    parabolicQuadraticContactSet w κ 0 (closedBall 0 R)
      (closedBall 0 R ×ˢ Icc 0 b)
      (closedBall 0 (R / 2) ×ˢ Icc (b / 4) (b / 2)) ⊆ ball 0 R ×ˢ Ioc 0 b := by
  intro p hp
  let v := parabolicQuadraticContactMap w κ p
  have hv : v ∈ closedBall (0 : E) (R / 2) ×ˢ Icc (b / 4) (b / 2) := hp.2.1
  have hs : 0 < v.2 := lt_of_lt_of_le (by positivity : 0 < b / 4) hv.2.1
  have hzero : parabolicQuadraticTilt w κ v p = 0 :=
    parabolicQuadraticTilt_contactMap w hκ.ne' p
  have ht : 0 < p.2 := by
    apply lt_of_le_of_ne hp.1.2.1
    intro he
    have hpos := parabolicQuadraticTilt_pos_at_initial hκ hs (hinitial p.1 hp.1.1)
    have hepair : p = (p.1, 0) := Prod.ext rfl he.symm
    rw [hepair] at hzero
    exact (ne_of_gt hpos) hzero
  refine ⟨?_, ht, hp.1.2.2⟩
  rw [mem_ball, dist_zero_right]
  have hxnorm : ‖p.1‖ ≤ R := by simpa using hp.1.1
  by_contra hn
  have hxsphere : p.1 ∈ sphere (0 : E) R := by
    simpa only [mem_sphere, dist_zero_right] using hxnorm.antisymm (le_of_not_gt hn)
  have hpos := parabolicQuadraticTilt_pos_at_lateral hR hκ hshort hxsphere
    hv.1 hs.le hp.1.2.2 (hlateral p.1 hxsphere p.2 hp.1.2)
  exact (ne_of_gt hpos) hzero

end PDE.Analysis
