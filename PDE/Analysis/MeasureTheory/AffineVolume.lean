/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Volume under scalar affine changes of variables, and of coordinate hyperplanes

The two image formulas combine translation invariance with Mathlib's Haar scaling
theorem. They apply to arbitrary sets, without a measurability premise.

`volume_coordinate_eq` says that every coordinate hyperplane `{y | y i = b}` of `ℝ^n` is
Lebesgue-null. The statements for the plane, for the level `0`, for
`PDE.Common.coordinateHyperplane` and for the boundary of the half-space are proved from it
(`GreenFunction.volume_coordinate_eq_zero`,
`SobolevSpace.HalfSpace.volume_coordinateHyperplane_eq_zero`,
`SobolevSpace.HalfSpace.volume_boundary`).
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set MeasureTheory MeasureTheory.Measure
open scoped Pointwise

variable {n : ℕ}

/-- Volume of the image of a Euclidean set under `x ↦ z + r • x` with `0 ≤ r`: it is `r ^ n`
times the volume of the set. -/
theorem volume_image_const_add_smul
    (z : ℝ^n) {r : ℝ} (hr : 0 ≤ r) (S : Set (ℝ^n)) :
    volume ((fun x ↦ z + r • x) '' S) = ENNReal.ofReal (r ^ n) * volume S := by
  have himage : (fun x ↦ z + r • x) '' S = (fun x ↦ z + x) '' (r • S) := by
    rw [← image_smul, image_image]
  rw [himage, image_add_left, measure_preimage_add, addHaar_smul_of_nonneg volume hr]
  rw [finrank_euclideanSpace_fin]

/-- The real-valued volume formula for an affine image. -/
theorem volume_real_image_const_add_smul
    (z : ℝ^n) {r : ℝ} (hr : 0 ≤ r) (S : Set (ℝ^n)) :
    volume.real ((fun x ↦ z + r • x) '' S) = r ^ n * volume.real S := by
  simp only [measureReal_def, volume_image_const_add_smul z hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr n)]

/-- Every coordinate hyperplane `{y | y i = b}` of `ℝ^n` is Lebesgue-null: it is a translate of
the kernel of the `i`-th coordinate, which is a proper subspace. -/
theorem volume_coordinate_eq (i : Fin n) (b : ℝ) : volume {y : ℝ^n | y i = b} = 0 := by
  have hset : {y : ℝ^n | y i = b} = (fun y ↦ y + -EuclideanSpace.single i b) ⁻¹'
      (LinearMap.ker (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).toLinearMap : Set (ℝ^n)) := by
    ext y
    simp [add_neg_eq_zero]
  rw [hset, measure_preimage_add_right]
  -- the kernel is proper: the `i`-th basis vector is not in it
  refine addHaar_submodule _ _ fun h ↦ ?_
  have hmem : EuclideanSpace.single i (1 : ℝ) ∈
      LinearMap.ker (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).toLinearMap := by
    rw [h]; exact Submodule.mem_top
  simp at hmem

end PDE.Analysis
