/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Centering
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Translation and dilation of ball integrals

The map `y ↦ x + r y` sends the unit ball onto `B(x,r)`. Its pushforward of restricted
Lebesgue measure is `r⁻ⁿ` times restricted Lebesgue measure on the target ball.
This gives the exact scaling of integral averages and `Lᵖ` norms, including exponent infinity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace.MeanScaling

variable {n : ℕ}

/-- The affine homeomorphism sending the unit ball onto a positive-radius ball. -/
def ballHomeomorph (x : ℝ^n) {r : ℝ} (hr : 0 < r) : (ℝ^n) ≃ₜ (ℝ^n) :=
  (Homeomorph.smul (Units.mk0 r hr.ne')).trans (Homeomorph.addLeft x)

/-- The ball homeomorphism has the usual translation and dilation formula. -/
@[simp]
theorem ballHomeomorph_apply (x : ℝ^n) {r : ℝ} (hr : 0 < r) (y : ℝ^n) :
    ballHomeomorph x hr y = x + r • y := rfl

/-- The inverse affine map subtracts the center and divides by the radius. -/
@[simp]
theorem ballHomeomorph_symm_apply (x : ℝ^n) {r : ℝ} (hr : 0 < r) (y : ℝ^n) :
    (ballHomeomorph x hr).symm y = r⁻¹ • (y - x) := by
  apply (ballHomeomorph x hr).injective
  rw [Homeomorph.apply_symm_apply, ballHomeomorph_apply, smul_smul,
    mul_inv_cancel₀ hr.ne', one_smul]
  abel

/-- Pulling back the target ball gives the unit ball exactly. -/
theorem preimage_ball (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    ballHomeomorph x hr ⁻¹' ball x r = ball 0 1 := by
  ext y
  simp only [mem_preimage, ballHomeomorph_apply, mem_ball, dist_eq_norm, sub_zero]
  rw [show x + r • y - x = r • y by abel, norm_smul, Real.norm_of_nonneg hr.le]
  simpa only [mul_one] using (mul_lt_mul_iff_right₀ hr : r * ‖y‖ < r * 1 ↔ ‖y‖ < 1)

/-- The affine image of the unit ball is the target ball. -/
theorem image_ball (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    ballHomeomorph x hr '' ball 0 1 = ball x r := by
  rw [← preimage_ball x hr]
  exact (ballHomeomorph x hr).surjective.image_preimage _

/-- The affine map rescales Lebesgue measure by the reciprocal of `rⁿ`. -/
theorem map_volume (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    volume.map (ballHomeomorph x hr) =
      ENNReal.ofReal (r ^ n)⁻¹ • (volume : Measure (ℝ^n)) := by
  change volume.map ((fun y : ℝ^n ↦ x + y) ∘ (fun y : ℝ^n ↦ r • y)) = _
  rw [← Measure.map_map (measurable_const_add x) (measurable_const_smul r),
    Measure.map_addHaar_smul volume hr.ne', Measure.map_smul, map_add_left_eq_self]
  · simp only [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hr n))]
  · exact (measurable_const_add x).aemeasurable

/-- Restricted Lebesgue measure has the same Jacobian factor under the ball map. -/
theorem map_ball_volume (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    (volume.restrict (ball (0 : ℝ^n) 1)).map (ballHomeomorph x hr) =
      ENNReal.ofReal (r ^ n)⁻¹ • volume.restrict (ball x r) := by
  rw [← preimage_ball x hr, ← Measure.restrict_map (ballHomeomorph x hr).measurable
    measurableSet_ball, map_volume x hr, Measure.restrict_smul]

/-- The common volume factor in the `Lᵖ` scaling formula. -/
def normFactor (n : ℕ) (r : ℝ) (p : ℝ≥0∞) : ℝ :=
  (ENNReal.ofReal (r ^ n)⁻¹ ^ (1 / p).toReal).toReal

/-- The norm scaling factor is strictly positive for every exponent. -/
theorem normFactor_pos {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) :
    0 < normFactor n r p := by
  have hc : ENNReal.ofReal (r ^ n)⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr n))).ne'
  exact ENNReal.toReal_pos
    (by simp [ENNReal.rpow_eq_zero_iff, hc])
    (ENNReal.rpow_ne_top_of_ne_zero hc ENNReal.ofReal_ne_top)

/-- Composition with the ball map preserves membership in every `Lᵖ`. -/
theorem memLp_comp_ballHomeomorph {F : Type*} [NormedAddCommGroup F]
    (x : ℝ^n) {r : ℝ} (hr : 0 < r) {p : ℝ≥0∞} {f : ℝ^n → F}
    (hf : MemLp f p (volume.restrict (ball x r))) :
    MemLp (fun y ↦ f (ballHomeomorph x hr y))
      p (volume.restrict (ball (0 : ℝ^n) 1)) := by
  have he : MeasurableEmbedding (ballHomeomorph x hr) :=
    (ballHomeomorph x hr).toMeasurableEquiv.measurableEmbedding
  apply he.memLp_map_measure_iff.mp
  rw [map_ball_volume]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- Exact `Lᵖ` scaling under translation and dilation, including `p = ∞`. -/
theorem eLpNorm_comp_ballHomeomorph {F : Type*} [NormedAddCommGroup F]
    (x : ℝ^n) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) (f : ℝ^n → F) :
    (eLpNorm (fun y ↦ f (ballHomeomorph x hr y))
      p (volume.restrict (ball (0 : ℝ^n) 1))).toReal =
        normFactor n r p * (eLpNorm f p (volume.restrict (ball x r))).toReal := by
  have he : MeasurableEmbedding (ballHomeomorph x hr) :=
    (ballHomeomorph x hr).toMeasurableEquiv.measurableEmbedding
  change (eLpNorm (f ∘ ballHomeomorph x hr) p _).toReal = _
  rw [← he.eLpNorm_map_measure,
    map_ball_volume, eLpNorm_smul_measure_of_ne_zero
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr n))).ne',
    smul_eq_mul, ENNReal.toReal_mul]
  rfl

/-- Null sets on the target ball pull back to null sets on the unit ball. -/
theorem quasiMeasurePreserving_ballHomeomorph (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    QuasiMeasurePreserving (ballHomeomorph x hr)
      (volume.restrict (ball (0 : ℝ^n) 1)) (volume.restrict (ball x r)) := by
  refine ⟨(ballHomeomorph x hr).measurable, ?_⟩
  rw [map_ball_volume]
  exact Measure.smul_absolutelyContinuous

private theorem average_smul_measure {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure α) (f : α → F) {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ∞) :
    (⨍ y, f y ∂c • μ) = ⨍ y, f y ∂μ := by
  simp only [average_eq, measureReal_def, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, integral_smul_measure, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hc, hc'⟩), mul_one]

/-- The spatial average is unchanged after pulling back to the unit ball. -/
theorem average_comp_ballHomeomorph {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x : ℝ^n) {r : ℝ} (hr : 0 < r) (f : ℝ^n → F) :
    (⨍ y, f (ballHomeomorph x hr y) ∂volume.restrict (ball (0 : ℝ^n) 1)) =
      ⨍ y, f y ∂volume.restrict (ball x r) := by
  have he : MeasurableEmbedding (ballHomeomorph x hr) :=
    (ballHomeomorph x hr).toMeasurableEquiv.measurableEmbedding
  have havg :
      (⨍ y, f (ballHomeomorph x hr y) ∂volume.restrict (ball (0 : ℝ^n) 1)) =
        ⨍ y, f y ∂(volume.restrict (ball (0 : ℝ^n) 1)).map (ballHomeomorph x hr) := by
    simp only [average_eq, he.integral_map, measureReal_def,
      Measure.map_apply (ballHomeomorph x hr).measurable MeasurableSet.univ,
      preimage_univ]
  rw [havg, map_ball_volume]
  exact average_smul_measure _ _
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr n))).ne' ENNReal.ofReal_ne_top

end SobolevSpace.GraphSpace.MeanScaling
