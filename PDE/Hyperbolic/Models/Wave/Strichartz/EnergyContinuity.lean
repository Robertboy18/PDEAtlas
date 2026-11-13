/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergyGram
import CAS.ExactTactic

/-!
# Time continuity of the Fourier energy datum

The unit Lipschitz bounds for sine and cosine cancel the inverse frequency in a
time difference. Explicit almost-everywhere transport gives Lipschitz estimates
for the L² classes and continuity in the Hilbert product.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap

namespace WaveEquation.Strichartz

private theorem norm_modulated_inverse_frequency_sub_le {m : ℝ → ℝ}
    (hm : LipschitzWith 1 m) (F : 𝓢(ℝ^3, ℂ)) (t s : ℝ) {ξ : ℝ^3} (hξ : ξ ≠ 0) :
    ‖m ((2 * Real.pi * ‖ξ‖) * t) • ((2 * Real.pi)⁻¹ • (‖ξ‖ ^ (-1 : ℝ) • F ξ)) -
      m ((2 * Real.pi * ‖ξ‖) * s) • ((2 * Real.pi)⁻¹ • (‖ξ‖ ^ (-1 : ℝ) • F ξ))‖ ≤
        dist t s * ‖F ξ‖ := by
  have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hc : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [← sub_smul, norm_smul, norm_smul, norm_smul, Real.rpow_neg hr.le, Real.rpow_one]
  simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), abs_of_pos (inv_pos.mpr hr)]
  have hm' : |m ((2 * Real.pi * ‖ξ‖) * t) - m ((2 * Real.pi * ‖ξ‖) * s)| ≤
      |(2 * Real.pi * ‖ξ‖) * t - (2 * Real.pi * ‖ξ‖) * s| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      hm.dist_le_mul ((2 * Real.pi * ‖ξ‖) * t) ((2 * Real.pi * ‖ξ‖) * s)
  calc
    _ ≤ |(2 * Real.pi * ‖ξ‖) * t - (2 * Real.pi * ‖ξ‖) * s| * ((2 * Real.pi)⁻¹ * (‖ξ‖⁻¹ * ‖F ξ‖)) :=
      mul_le_mul_of_nonneg_right hm' (by positivity)
    _ = dist t s * ‖F ξ‖ := by
      rw [← mul_sub, abs_mul, abs_of_pos (mul_pos hc hr), Real.dist_eq]
      have hcancel : (2 * Real.pi * ‖ξ‖) * (2 * Real.pi)⁻¹ * ‖ξ‖⁻¹ = 1 := by
        cas using [hr, Real.pi_pos]
      calc
        _ = ((2 * Real.pi * ‖ξ‖) * (2 * Real.pi)⁻¹ * ‖ξ‖⁻¹) *
            (|t - s| * ‖F ξ‖) := by ring
        _ = _ := by rw [hcancel, one_mul]

/-- The cosine L² component is Lipschitz in time with the source L² norm. -/
theorem lipschitzWith_cosineEnergyDatum (F : 𝓢(ℝ^3, ℂ)) :
    LipschitzWith ‖F.toLp 2 volume‖₊ (cosineEnergyDatum F) := by
  refine LipschitzWith.of_dist_le_mul fun t s ↦ ?_
  rw [dist_eq_norm, coe_nnnorm, mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (cosineEnergyDatum F t) (cosineEnergyDatum F s),
    cosineEnergyDatum_ae_eq F t, cosineEnergyDatum_ae_eq F s,
    F.coeFn_toLp 2 volume, volume.ae_ne (0 : ℝ^3)] with ξ hsub ht hs hF hξ
  rw [hsub, Pi.sub_apply, ht, hs, hF]
  exact norm_modulated_inverse_frequency_sub_le Real.lipschitzWith_cos F t s hξ

/-- The sine L² component is Lipschitz in time with the source L² norm. -/
theorem lipschitzWith_sineEnergyDatum (F : 𝓢(ℝ^3, ℂ)) :
    LipschitzWith ‖F.toLp 2 volume‖₊ (sineEnergyDatum F) := by
  refine LipschitzWith.of_dist_le_mul fun t s ↦ ?_
  rw [dist_eq_norm, coe_nnnorm, mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (sineEnergyDatum F t) (sineEnergyDatum F s),
    sineEnergyDatum_ae_eq F t, sineEnergyDatum_ae_eq F s,
    F.coeFn_toLp 2 volume, volume.ae_ne (0 : ℝ^3)] with ξ hsub ht hs hF hξ
  rw [hsub, Pi.sub_apply, ht, hs, hF]
  exact norm_modulated_inverse_frequency_sub_le Real.lipschitzWith_sin F t s hξ

/-- The Hilbert energy datum is continuous in time. -/
theorem continuous_frequencyEnergyDatum (F : 𝓢(ℝ^3, ℂ)) :
    Continuous (frequencyEnergyDatum F) :=
  (WithLp.prod_continuous_toLp 2 _ _).comp ((lipschitzWith_cosineEnergyDatum F).continuous.prodMk
      (lipschitzWith_sineEnergyDatum F).continuous)

end WaveEquation.Strichartz
