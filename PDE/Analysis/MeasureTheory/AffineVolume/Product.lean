/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.AffineVolume

/-!
# Independent affine dilations of product factors

The determinant of a block diagonal map gives the exact Haar measure change
when the two factors have different dilation rates. In spacetime, spatial
scale `r` and temporal scale `r²` give the factor `r^(n + 2)`.
The formulas apply to arbitrary sets, including zero-dimensional factors.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set MeasureTheory MeasureTheory.Measure

/-- Haar measure under independent scalar dilations of two factors and a
translation. No measurability or invertibility premise is needed. -/
theorem addHaar_image_const_add_prod_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace (E × F)] [BorelSpace (E × F)]
    (μ : Measure (E × F)) [μ.IsAddHaarMeasure]
    (z : E × F) (r s : ℝ) (S : Set (E × F)) :
    μ ((fun p : E × F ↦ z + (r • p.1, s • p.2)) '' S) =
      ENNReal.ofReal |r ^ Module.finrank ℝ E * s ^ Module.finrank ℝ F| * μ S := by
  let A := (r • (LinearMap.id : E →ₗ[ℝ] E)).prodMap
    (s • (LinearMap.id : F →ₗ[ℝ] F))
  have himage : (fun p : E × F ↦ z + (r • p.1, s • p.2)) '' S =
      (fun p ↦ z + p) '' (A '' S) := by
    rw [image_image]
    rfl
  rw [himage, image_add_left, measure_preimage_add, addHaar_image_linearMap]
  simp [A, LinearMap.det_prodMap, LinearMap.det_smul]

/-- Parabolic dilation has dimension `n + 2` for spacetime volume, also when
the spatial dimension is zero. -/
theorem volume_image_space_time_dilation {n : ℕ}
    (z : ℝ^n) (s : ℝ) {r : ℝ} (hr : 0 ≤ r) (S : Set (ℝ^n × ℝ)) :
    volume ((fun p : ℝ^n × ℝ ↦ (z + r • p.1, s + r ^ 2 * p.2)) '' S) =
      ENNReal.ofReal (r ^ (n + 2)) * volume S := by
  let : (volume : Measure (ℝ^n × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have h := addHaar_image_const_add_prod_smul volume (z, s) r (r ^ 2) S
  simpa only [Prod.mk_add_mk, smul_eq_mul, finrank_euclideanSpace_fin,
    Module.finrank_self, pow_one, ← pow_add, abs_of_nonneg (pow_nonneg hr _)] using h

/-- The real-valued form of spacetime volume scaling. -/
theorem volume_real_image_space_time_dilation {n : ℕ}
    (z : ℝ^n) (s : ℝ) {r : ℝ} (hr : 0 ≤ r) (S : Set (ℝ^n × ℝ)) :
    volume.real ((fun p : ℝ^n × ℝ ↦ (z + r • p.1, s + r ^ 2 * p.2)) '' S) =
      r ^ (n + 2) * volume.real S := by
  simp only [measureReal_def, volume_image_space_time_dilation z s hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)]

end PDE.Analysis
