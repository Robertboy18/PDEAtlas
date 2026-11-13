/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Geometry

/-!
# Integral averages under affine ball rescaling

The Jacobian in the integral and the volume normalization cancel at every
concentric radius. This extends the unit-ball average formula to the
single affine map used to transport a weak equation and its interior estimates.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set

namespace SobolevSpace.GraphSpace.MeanScaling

variable {n : ℕ}

/-- Averages on corresponding concentric balls agree under an affine dilation.
The assertion also covers empty balls and nonintegrable functions. -/
theorem average_comp_ballHomeomorph_mul {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ) (f : ℝ^n → F) :
    (⨍ y in ball (0 : ℝ^n) r, f (ballHomeomorph z ha y)) =
      ⨍ y in ball z (a * r), f y := by
  have he : MeasurableEmbedding (ballHomeomorph z ha) :=
    (ballHomeomorph z ha).toMeasurableEquiv.measurableEmbedding
  have havg :
      (⨍ y in ball (0 : ℝ^n) r, f (ballHomeomorph z ha y)) =
        ⨍ y, f y ∂(volume.restrict (ball (0 : ℝ^n) r)).map (ballHomeomorph z ha) := by
    simp only [average_eq, he.integral_map, measureReal_def,
      Measure.map_apply (ballHomeomorph z ha).measurable MeasurableSet.univ,
      preimage_univ]
  rw [havg, map_ball_volume_mul]
  simp only [average_eq, measureReal_def, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, integral_smul_measure, mul_inv_rev, smul_smul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg ha.le n))]
  rw [mul_assoc, inv_mul_cancel₀ (inv_ne_zero (pow_ne_zero n ha.ne')), mul_one]

end SobolevSpace.GraphSpace.MeanScaling
