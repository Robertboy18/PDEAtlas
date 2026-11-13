/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Scaling

/-!
# Affine changes of scale on concentric balls

The same affine map transports every concentric ball, with the same Jacobian.
This lets a weak-equation rescaling and its smaller-ball estimate use one map.
The homeomorphism and Lebesgue scaling are those of `MeanScaling`.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace.MeanScaling

variable {n : ℕ}

/-- An affine dilation transports every concentric ball, including empty balls. -/
theorem preimage_ball_mul (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ) :
    ballHomeomorph z ha ⁻¹' ball z (a * r) = ball 0 r := by
  ext y
  simp only [mem_preimage, ballHomeomorph_apply, mem_ball, dist_eq_norm, sub_zero]
  rw [show z + a • y - z = a • y by abel, norm_smul, Real.norm_of_nonneg ha.le]
  exact mul_lt_mul_iff_right₀ ha

/-- The image formula corresponding to `preimage_ball_mul`. -/
theorem image_ball_mul (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ) :
    ballHomeomorph z ha '' ball 0 r = ball z (a * r) := by
  rw [← preimage_ball_mul z ha r]
  exact (ballHomeomorph z ha).surjective.image_preimage _

/-- Restrict the affine homeomorphism to a pair of corresponding balls. -/
def scaledBallChart (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ) :
    OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
  (ballHomeomorph z ha).toOpenPartialHomeomorphOfImageEq
    (ball 0 r) isOpen_ball (ball z (a * r)) (image_ball_mul z ha r)

/-- The affine chart is smooth on the whole space. -/
theorem contDiff_scaledBallChart (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (k : ℕ∞) : ContDiff ℝ k (scaledBallChart z ha r) := by
  change ContDiff ℝ k (fun y : ℝ^n ↦ z + a • y)
  fun_prop

/-- The inverse affine chart is smooth on the whole space. -/
theorem contDiff_scaledBallChart_symm (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (k : ℕ∞) : ContDiff ℝ k (scaledBallChart z ha r).symm := by
  change ContDiff ℝ k (fun y ↦ (ballHomeomorph z ha).symm y)
  simp only [ballHomeomorph_symm_apply]
  fun_prop

/-- The pushforward formula uses the same Jacobian at every radius. -/
theorem map_ball_volume_mul (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (volume.restrict (ball (0 : ℝ^n) r)).map (ballHomeomorph z ha) =
      ENNReal.ofReal (a ^ n)⁻¹ • volume.restrict (ball z (a * r)) := by
  rw [← preimage_ball_mul z ha r, ← Measure.restrict_map
    (ballHomeomorph z ha).measurable measurableSet_ball, map_volume,
    Measure.restrict_smul]

/-- Almost-everywhere assertions transport in both directions under the affine map. -/
theorem ae_comp_ballHomeomorph_iff (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (P : ℝ^n → Prop) :
    (∀ᵐ y ∂volume.restrict (ball (0 : ℝ^n) r), P (ballHomeomorph z ha y)) ↔
      ∀ᵐ y ∂volume.restrict (ball z (a * r)), P y := by
  have he : MeasurableEmbedding (ballHomeomorph z ha) :=
    (ballHomeomorph z ha).toMeasurableEquiv.measurableEmbedding
  rw [← he.ae_map_iff,
    map_ball_volume_mul, Measure.ae_ennreal_smul_measure_iff
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos ha n))).ne']

/-- The integral change of variables needs no integrability premise; both sides
use the usual total Bochner integral. -/
theorem integral_comp_ballHomeomorph_mul (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (f : ℝ^n → ℝ) :
    (∫ y in ball (0 : ℝ^n) r, f (ballHomeomorph z ha y)) =
      (a ^ n)⁻¹ * ∫ y in ball z (a * r), f y := by
  have he : MeasurableEmbedding (ballHomeomorph z ha) :=
    (ballHomeomorph z ha).toMeasurableEquiv.measurableEmbedding
  rw [← he.integral_map,
    map_ball_volume_mul, integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg ha.le n))]

end SobolevSpace.GraphSpace.MeanScaling
