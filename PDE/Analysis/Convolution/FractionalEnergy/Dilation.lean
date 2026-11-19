/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Convolution.FractionalEnergy.HeightIntegral

/-!
# Dilation and fractional displacement energy

Changing a compact-kernel variable into a physical displacement contributes the
inverse volume scale. The height-tail identity then supplies the fractional power.
-/

@[expose] public section

open MeasureTheory Set Module
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Positive scalar dilation of a nonnegative integral against an additive Haar measure. -/
theorem lintegral_comp_pos_smul (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    (∫⁻ z, f (t • z) ∂μ) =
      ENNReal.ofReal ((t ^ finrank ℝ E)⁻¹) * ∫⁻ h, f h ∂μ := by
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 t ht.ne')).toMeasurableEquiv
  calc
    _ = ∫⁻ h, f h ∂Measure.map (fun z : E ↦ t • z) μ :=
      (lintegral_map_equiv f e).symm
    _ = _ := by
      rw [Measure.map_addHaar_smul μ ht.ne', lintegral_smul_measure,
        abs_of_pos (inv_pos.mpr (pow_pos ht _)), smul_eq_mul]

/-- A compact integration ball dilates with the kernel variable. -/
theorem lintegral_ball_comp_pos_smul (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (R : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ z in Metric.ball (0 : E) R, f (t • z) ∂μ) =
      ENNReal.ofReal ((t ^ finrank ℝ E)⁻¹) *
        ∫⁻ h in Metric.ball (0 : E) (R * t), f h ∂μ := by
  classical
  calc
    _ = ∫⁻ z, (Metric.ball (0 : E) (R * t)).indicator f (t • z) ∂μ := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro z
      have hm : t • z ∈ Metric.ball (0 : E) (R * t) ↔ z ∈ Metric.ball (0 : E) R := by
        simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht, mul_comm R t, mul_lt_mul_iff_right₀ ht]
      simp only [indicator_apply, hm]
    _ = _ := by
      rw [lintegral_comp_pos_smul μ _ ht, lintegral_indicator measurableSet_ball]

/-- Integrating dilated compact kernels in height gives the fractional displacement kernel. -/
theorem lintegral_dilation_ball_rpow_eq (μ : Measure E) [μ.IsAddHaarMeasure]
    {p R : ℝ} (hp : 1 < p) (hR : 0 < R)
    {f : E → ℝ≥0∞} (hf : Measurable f) (hf0 : f 0 = 0) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-p)) *
      ∫⁻ z in Metric.ball (0 : E) R, f (t • z) ∂μ) =
      ENNReal.ofReal (R ^ ((finrank ℝ E : ℝ) + p - 1) /
        ((finrank ℝ E : ℝ) + p - 1)) *
        ∫⁻ h, ENNReal.ofReal (‖h‖ ^ (-((finrank ℝ E : ℝ) + p - 1))) * f h ∂μ := by
  have hq : 0 < (finrank ℝ E : ℝ) + p - 1 := by
    have := Nat.cast_nonneg (α := ℝ) (finrank ℝ E)
    linarith
  rw [← lintegral_height_ball_eq μ hq hR hf hf0]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht : 0 < t := ht
  rw [lintegral_ball_comp_pos_smul μ _ R ht,
    ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  have heq : t ^ (-p) * (t ^ finrank ℝ E)⁻¹ =
      t ^ (-((finrank ℝ E : ℝ) + p - 1 + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    congr 1
    ring
  rw [heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end MeasureTheory
