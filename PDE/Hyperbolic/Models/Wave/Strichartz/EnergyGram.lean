/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.NewtonFrequency

/-!
# The wave energy Gram multiplier

Cosine and sine multiplication of the inverse-frequency Schwartz datum gives
L² classes. Their Hilbert product pairing is the Newton-weighted cosine
multiplier at the time difference. Explicit almost-everywhere transport connects
the quotient representatives to the raw frequency functions.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal

namespace WaveEquation.Strichartz

/-- A bounded cosine multiplier preserves the inverse-frequency L² datum. -/
theorem memLp_cosine_inverse_frequency (F : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    MemLp (fun ξ ↦ Real.cos ((2 * Real.pi * ‖ξ‖) * t) •
      ((2 * Real.pi)⁻¹ • (‖ξ‖ ^ (-1 : ℝ) • F ξ))) 2 volume := by
  have hw : MemLp (fun ξ : ℝ^3 ↦ Real.cos ((2 * Real.pi * ‖ξ‖) * t)) ∞ volume :=
    memLp_top_of_bound (show Continuous (fun ξ : ℝ^3 ↦
      Real.cos ((2 * Real.pi * ‖ξ‖) * t)) by fun_prop).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ξ ↦ by
        simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ((2 * Real.pi * ‖ξ‖) * t))
  exact hw.smul (memLp_inverse_frequency F)

/-- A bounded sine multiplier preserves the inverse-frequency L² datum. -/
theorem memLp_sine_inverse_frequency (F : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    MemLp (fun ξ ↦ Real.sin ((2 * Real.pi * ‖ξ‖) * t) •
      ((2 * Real.pi)⁻¹ • (‖ξ‖ ^ (-1 : ℝ) • F ξ))) 2 volume := by
  have hw : MemLp (fun ξ : ℝ^3 ↦ Real.sin ((2 * Real.pi * ‖ξ‖) * t)) ∞ volume :=
    memLp_top_of_bound (show Continuous (fun ξ : ℝ^3 ↦
      Real.sin ((2 * Real.pi * ‖ξ‖) * t)) by fun_prop).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ξ ↦ by
        simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one ((2 * Real.pi * ‖ξ‖) * t))
  exact hw.smul (memLp_inverse_frequency F)

/-- The cosine component of the inverse-frequency energy datum, as an L² class. -/
noncomputable def cosineEnergyDatum (F : 𝓢(ℝ^3, ℂ)) (t : ℝ) : Lp ℂ 2 (volume : Measure (ℝ^3)) :=
  (memLp_cosine_inverse_frequency F t).toLp _

/-- The sine component of the inverse-frequency energy datum, as an L² class. -/
noncomputable def sineEnergyDatum (F : 𝓢(ℝ^3, ℂ)) (t : ℝ) : Lp ℂ 2 (volume : Measure (ℝ^3)) :=
  (memLp_sine_inverse_frequency F t).toLp _

/-- The cosine L² class has the specified frequency representative almost everywhere. -/
theorem cosineEnergyDatum_ae_eq (F : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    cosineEnergyDatum F t =ᵐ[volume] fun ξ ↦ Real.cos ((2 * Real.pi * ‖ξ‖) * t) •
      ((2 * Real.pi)⁻¹ • (‖ξ‖ ^ (-1 : ℝ) • F ξ)) :=
  (memLp_cosine_inverse_frequency F t).coeFn_toLp

/-- The sine L² class has the specified frequency representative almost everywhere. -/
theorem sineEnergyDatum_ae_eq (F : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    sineEnergyDatum F t =ᵐ[volume] fun ξ ↦ Real.sin ((2 * Real.pi * ‖ξ‖) * t) •
      ((2 * Real.pi)⁻¹ • (‖ξ‖ ^ (-1 : ℝ) • F ξ)) :=
  (memLp_sine_inverse_frequency F t).coeFn_toLp

/-- The two inverse-frequency components in their Hilbert product. -/
noncomputable def frequencyEnergyDatum (F : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    WithLp 2 (Lp ℂ 2 (volume : Measure (ℝ^3)) × Lp ℂ 2 (volume : Measure (ℝ^3))) :=
  WithLp.toLp 2 (cosineEnergyDatum F t, sineEnergyDatum F t)

/-- The Hilbert Gram pairing is the Newton-weighted cosine multiplier. -/
theorem inner_frequencyEnergyDatum (F G : 𝓢(ℝ^3, ℂ)) (t s : ℝ) :
    inner ℂ (frequencyEnergyDatum F t) (frequencyEnergyDatum G s) =
      ∫ ξ, inner ℂ (F ξ) (Real.cos ((2 * Real.pi * ‖ξ‖) * (t - s)) • newtonFrequency G ξ) := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ (cosineEnergyDatum F t) (cosineEnergyDatum G s) +
    inner ℂ (sineEnergyDatum F t) (sineEnergyDatum G s) = _
  rw [L2.inner_def, L2.inner_def, ← integral_add
    (L2.integrable_inner (𝕜 := ℂ) (cosineEnergyDatum F t) (cosineEnergyDatum G s))
    (L2.integrable_inner (𝕜 := ℂ) (sineEnergyDatum F t) (sineEnergyDatum G s))]
  apply integral_congr_ae
  filter_upwards [cosineEnergyDatum_ae_eq F t, cosineEnergyDatum_ae_eq G s,
    sineEnergyDatum_ae_eq F t, sineEnergyDatum_ae_eq G s] with ξ hFt hGs hFt' hGs'
  rw [hFt, hGs, hFt', hGs']
  simp only [newtonFrequency, inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul]
  rw [← add_smul]
  congr 1
  rw [Real.rpow_neg (norm_nonneg ξ), Real.rpow_one, Real.rpow_neg (norm_nonneg ξ), Real.rpow_two]
  have htrig := Real.cos_sub ((2 * Real.pi * ‖ξ‖) * t) ((2 * Real.pi * ‖ξ‖) * s)
  rw [← mul_sub] at htrig
  rw [htrig]
  ring

end WaveEquation.Strichartz
