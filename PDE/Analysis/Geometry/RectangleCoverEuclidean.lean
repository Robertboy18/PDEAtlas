/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.RectangleCover
public import PDE.Common.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Rectangle subdivisions covering a Euclidean half-ball

Four rational-to-real endpoint inequalities put a closed half-ball in a root
rectangle. `Tree.covers` then covers it by the finite leaf
rectangles. These cells are closed and hence measurable.
-/

@[expose] public section

open Set

namespace PDE.Analysis.RectangleCover

/-- Closed coordinate sides give a measurable Euclidean cell. -/
theorem Box.isClosed_contains (b : Box) :
    IsClosed {x : ℝ^2 | b.Contains (x 0) (x 1)} := by
  exact (isClosed_le continuous_const (PiLp.continuous_apply 2 _ 0)).inter
    ((isClosed_le (PiLp.continuous_apply 2 _ 0) continuous_const).inter
      ((isClosed_le continuous_const (PiLp.continuous_apply 2 _ 1)).inter
        (isClosed_le (PiLp.continuous_apply 2 _ 1) continuous_const)))

/-- A root box containing `[0,R] × [-R,R]` covers the radius-`R` half-ball by
its finitely indexed leaves. Boundary faces are included. -/
theorem Tree.halfBall_subset_iUnion_records (t : Tree) (b : Box) (R : ℝ)
    (hxlo : (b.xlo : ℝ) ≤ 0) (hxhi : R ≤ (b.xhi : ℝ))
    (hylo : (b.ylo : ℝ) ≤ -R) (hyhi : R ≤ (b.yhi : ℝ)) :
    {x : ℝ^2 | 0 ≤ x 0} ∩ Metric.closedBall 0 R ⊆
      ⋃ j : Fin (t.records b).length,
        {x : ℝ^2 | ((t.records b)[j]).1.Contains (x 0) (x 1)} := by
  intro x hx
  have hn : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2
  have hcoord (i : Fin 2) : |x i| ≤ R :=
    (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans hn
  have hb : b.Contains (x 0) (x 1) :=
    ⟨hxlo.trans hx.1, (le_abs_self _).trans ((hcoord 0).trans hxhi),
      hylo.trans (abs_le.mp (hcoord 1)).1,
      (le_abs_self _).trans ((hcoord 1).trans hyhi)⟩
  obtain ⟨entry, he, hp⟩ := t.covers b (x 0) (x 1) hb
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  change ((t.records b).get j).1.Contains (x 0) (x 1)
  rw [hj]
  exact hp

end PDE.Analysis.RectangleCover
