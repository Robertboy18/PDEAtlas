/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergyGram

/-!
# Linearity of the Fourier energy datum

The cosine and sine L² classes respect addition and real scalar multiplication.
Their almost-everywhere frequency formulas prove these identities on quotient
classes, and give a real linear map on Schwartz frequency sources.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap

namespace WaveEquation.Strichartz

/-- Addition of Schwartz sources induces addition of the Hilbert energy data. -/
theorem frequencyEnergyDatum_add (F G : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    frequencyEnergyDatum (F + G) t = frequencyEnergyDatum F t + frequencyEnergyDatum G t := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · change cosineEnergyDatum (F + G) t = cosineEnergyDatum F t + cosineEnergyDatum G t
    apply Lp.ext
    filter_upwards [cosineEnergyDatum_ae_eq (F + G) t, cosineEnergyDatum_ae_eq F t,
      cosineEnergyDatum_ae_eq G t, Lp.coeFn_add (cosineEnergyDatum F t)
        (cosineEnergyDatum G t)] with ξ hsum hF hG hout
    rw [hsum, hout, Pi.add_apply, hF, hG]
    simp only [add_apply, smul_add]
  · change sineEnergyDatum (F + G) t = sineEnergyDatum F t + sineEnergyDatum G t
    apply Lp.ext
    filter_upwards [sineEnergyDatum_ae_eq (F + G) t, sineEnergyDatum_ae_eq F t,
      sineEnergyDatum_ae_eq G t, Lp.coeFn_add (sineEnergyDatum F t)
        (sineEnergyDatum G t)] with ξ hsum hF hG hout
    rw [hsum, hout, Pi.add_apply, hF, hG]
    simp only [add_apply, smul_add]

/-- Real scalar multiplication commutes with the Hilbert energy datum. -/
theorem frequencyEnergyDatum_smul (c : ℝ) (F : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    frequencyEnergyDatum (c • F) t = c • frequencyEnergyDatum F t := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · change cosineEnergyDatum (c • F) t = c • cosineEnergyDatum F t
    apply Lp.ext
    filter_upwards [cosineEnergyDatum_ae_eq (c • F) t, cosineEnergyDatum_ae_eq F t,
      Lp.coeFn_smul c (cosineEnergyDatum F t)] with ξ hsmul hF hout
    rw [hsmul, hout, Pi.smul_apply, hF]
    simp only [smul_apply, smul_comm _ c]
  · change sineEnergyDatum (c • F) t = c • sineEnergyDatum F t
    apply Lp.ext
    filter_upwards [sineEnergyDatum_ae_eq (c • F) t, sineEnergyDatum_ae_eq F t,
      Lp.coeFn_smul c (sineEnergyDatum F t)] with ξ hsmul hF hout
    rw [hsmul, hout, Pi.smul_apply, hF]
    simp only [smul_apply, smul_comm _ c]

/-- The energy datum is a real linear map on Schwartz frequency sources. -/
noncomputable def frequencyEnergyDatumLinearMap (t : ℝ) :
    𝓢(ℝ^3, ℂ) →ₗ[ℝ]
      WithLp 2 (Lp ℂ 2 (volume : Measure (ℝ^3)) × Lp ℂ 2 (volume : Measure (ℝ^3))) where
  toFun F := frequencyEnergyDatum F t
  map_add' F G := frequencyEnergyDatum_add F G t
  map_smul' c F := frequencyEnergyDatum_smul c F t

end WaveEquation.Strichartz
