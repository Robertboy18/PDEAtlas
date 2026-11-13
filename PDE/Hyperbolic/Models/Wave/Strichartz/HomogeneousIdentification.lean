/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.Homogeneous
public import PDE.Hyperbolic.Models.Wave.Strichartz.InitialEnergy

/-!
# Physical tensor pairings of the homogeneous wave operator

For Schwartz initial data, the bounded homogeneous operator and the physical
Fourier wave have equal pairings against every finite compact spacetime tensor.
The datum has exactly gradient plus velocity energy. The almost-everywhere
identification is in `Strichartz.PhysicalIdentification`.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- The constructed homogeneous operator and the physical Fourier wave have
identical pairings against every finite compact spacetime tensor. -/
theorem spacetimePairing_homogeneousWaveOperator_initialEnergyDatum_compactTensor (g h : 𝓢(ℝ^3, ℂ))
    (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} × {f :
      𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    spacetimePairing (homogeneousWaveOperator (initialEnergyDatum g h))
      (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a) =
        ∫ t, ∫ x, SchwartzMap.compactTensorSchwartzLinearMap a t x *
          (Fourier.waveSolution (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ)) (t, x)).re := by
  rw [spacetimePairing_homogeneousWaveOperator, energyAdjointOperator_compactTensor]
  have hi := integrable_frequencyEnergyDatum_compactTensor a
  change RCLike.re (inner ℂ (∫ t, frequencyEnergyDatum
    (𝓕 ((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM Complex.ofRealCLM)) t)
    (initialEnergyDatum g h)) = _
  rw [inner_re_symm, ← integral_inner hi, ← integral_re (hi.const_inner _)]
  apply integral_congr_ae
  filter_upwards with t
  rw [inner_re_symm]
  exact re_inner_frequencyEnergyDatum_initialEnergyDatum
    (SchwartzMap.compactTensorSchwartzLinearMap a t)
    (hasCompactSupport_compactTensorSchwartzSection a t) g h t

end WaveEquation.Strichartz
