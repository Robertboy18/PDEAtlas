/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Volume under scalar affine changes of variables

These formulas combine translation invariance with Mathlib's Haar scaling
theorem. They apply to arbitrary sets, without a measurability premise.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set MeasureTheory MeasureTheory.Measure
open scoped Pointwise

variable {n : ℕ}

/-- Volume of a translated, positively dilated Euclidean set. -/
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

end PDE.Analysis
