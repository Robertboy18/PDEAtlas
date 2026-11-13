/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.FixedPoint.Brouwer.CompactConvex

/-!
# Continuous fixed points in different ball and convex-set geometries

We apply Brouwer's theorem to an absolute-value map of the disk, a reflected segment
in `ℝ³`, and a square with the sup norm. The absolute-value maps are continuous but
not smooth.
-/

@[expose] public noncomputable section

open Set Metric Function

namespace PDE.Examples.FixedPoint

/-- The map `((1 + |x₂|)/2, 0)` on the Euclidean plane. -/
def absoluteDiskMap (x : ℝ^2) : ℝ^2 :=
  ((1 + |x 1|) / 2) • EuclideanSpace.single 0 1

/-- The disk map is continuous. -/
theorem continuous_absoluteDiskMap : Continuous absoluteDiskMap :=
  ((continuous_const.add (EuclideanSpace.proj 1).continuous.abs).div_const 2).smul
    continuous_const

/-- The disk map takes the entire closed disk into itself. -/
theorem absoluteDiskMap_mem_ball {x : ℝ^2} (hx : x ∈ closedBall 0 1) :
    absoluteDiskMap x ∈ closedBall 0 1 := by
  have hcoord : |x 1| ≤ 1 :=
    (PiLp.norm_apply_le x 1).trans (mem_closedBall_zero_iff.mp hx)
  rw [mem_closedBall_zero_iff, absoluteDiskMap, norm_smul]
  simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  linarith

/-- Brouwer's theorem for the absolute-value disk map. -/
theorem absoluteDiskMap_fixedPoint :
    ∃ x ∈ closedBall (0 : ℝ^2) 1, absoluteDiskMap x = x := by
  let f : C(closedBall (0 : ℝ^2) 1, closedBall (0 : ℝ^2) 1) :=
    ⟨fun x ↦ ⟨absoluteDiskMap x, absoluteDiskMap_mem_ball x.property⟩,
      (continuous_absoluteDiskMap.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨x, hx⟩ := PDE.FixedPoint.exists_isFixedPt_unitClosedBall 2 f
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- A line segment in three-dimensional Euclidean space. -/
def axisSegment : Set (ℝ^3) := segment ℝ 0 (EuclideanSpace.single 0 1)

/-- Reflection exchanges the two endpoints of the segment. -/
def axisReflection (x : ℝ^3) : ℝ^3 := EuclideanSpace.single 0 1 - x

/-- Reflection is not constant on the segment. -/
theorem axisReflection_endpoints_ne :
    axisReflection 0 ≠ axisReflection (EuclideanSpace.single 0 1) := by
  simp [axisReflection]

/-- The segment is invariant under reflection. -/
theorem axisReflection_mapsTo : MapsTo axisReflection axisSegment axisSegment := by
  intro x ⟨a, b, ha, hb, hab, hx⟩
  refine ⟨b, a, hb, ha, by linarith, ?_⟩
  simp only [smul_zero, zero_add] at hx ⊢
  rw [← hx]
  change a • EuclideanSpace.single 0 (1 : ℝ) =
    EuclideanSpace.single 0 1 - b • EuclideanSpace.single 0 1
  have ha' : a = 1 - b := by linarith
  rw [ha', sub_smul, one_smul]

/-- Brouwer applies to a lower-dimensional convex set in its ambient space. -/
theorem axisReflection_fixedPoint : ∃ x ∈ axisSegment, axisReflection x = x := by
  have hcompact : IsCompact axisSegment := by
    unfold axisSegment
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const
      |>.add (continuous_id.smul continuous_const))
  let f : C(axisSegment, axisSegment) :=
    ⟨fun x ↦ ⟨axisReflection x, axisReflection_mapsTo x.property⟩,
      ((continuous_const.sub continuous_id).comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨x, hx⟩ := PDE.FixedPoint.exists_isFixedPt_of_isCompact_convex_finiteDimensional
    ⟨0, left_mem_segment ℝ _ _⟩ hcompact (convex_segment _ _) f
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- A self-map for the Pi/sup norm, with both coordinates equal. -/
def absoluteSquareMap (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun _ ↦ (1 + |x 0|) / 2

/-- Brouwer's theorem for the sup-norm ball in `Fin 2 → ℝ`. -/
theorem absoluteSquareMap_fixedPoint :
    ∃ x ∈ closedBall (0 : Fin 2 → ℝ) 1, absoluteSquareMap x = x := by
  have hcont : Continuous absoluteSquareMap :=
    continuous_pi fun _ ↦ (continuous_const.add (continuous_apply 0).abs).div_const 2
  have hmap : MapsTo absoluteSquareMap (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    have hcoord : |x 0| ≤ 1 := (norm_le_pi_norm x 0).trans (mem_closedBall_zero_iff.mp hx)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    change |(1 + |x 0|) / 2| ≤ 1
    rw [abs_of_nonneg (by positivity)]
    linarith
  let f : C(closedBall (0 : Fin 2 → ℝ) 1, closedBall (0 : Fin 2 → ℝ) 1) :=
    ⟨fun x ↦ ⟨absoluteSquareMap x, hmap x.property⟩,
      (hcont.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨x, hx⟩ := PDE.FixedPoint.exists_isFixedPt_closedBall 0 zero_le_one f
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

end PDE.Examples.FixedPoint
