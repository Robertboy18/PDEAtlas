/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.Cutoff
public import PDE.Hyperbolic.Models.Wave.Strichartz.PhysicalIdentification

/-!
# Physical retarded impulses and spacetime pairings

The future restriction of the homogeneous quotient wave is identified almost
everywhere with the shifted Schwartz sine wave. Continuous dual pairings
commute with the retarded Bochner integral for arbitrary L1L2 forcing.

These identities preserve the quotient representatives and the direction
of the time cutoff. The identification for general forcing is in `Strichartz.Duhamel`.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- For Schwartz forcing data, the retarded quotient impulse is the
future-truncated sine wave almost everywhere in spacetime. -/
theorem jointRepresentative_retardedWaveAt_schwartz (h : 𝓢(ℝ^3, ℂ)) (s : ℝ) :
    Lp.jointRepresentative (retardedWaveAt s (h.toLp 2 volume)) =ᵐ[volume.prod volume]
      (Prod.fst ⁻¹' Set.Ici s).indicator
      (fun z ↦ (Fourier.waveSolution (0 : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ)) (z.1 - s, z.2)).re) := by
  have hcut := Lp.jointRepresentative_indicatorCLM (𝕜 := ℝ) (s := Set.Ici s) measurableSet_Ici
    (homogeneousWaveOperator (Lp.rotationColumn measurable_waveFrequency s ((𝓕 h).toLp 2 volume)))
  have hphys := jointRepresentative_homogeneousWaveOperator_rotationColumn (𝓕 h) s
  have heq := congrArg (fun H : Lp ℂ 2 (volume : Measure (ℝ^3)) ↦
    Lp.jointRepresentative (Lp.indicatorCLM ℝ (s := Set.Ici s) measurableSet_Ici
      (homogeneousWaveOperator (Lp.rotationColumn measurable_waveFrequency s H))))
    (SchwartzMap.toLp_fourier_eq h)
  apply heq.eventuallyEq.trans
  filter_upwards [hcut, hphys] with z hz hp
  rw [hz]
  by_cases ht : z ∈ Prod.fst ⁻¹' Set.Ici s
  · simp only [Set.indicator_of_mem ht, hp]
  · simp only [Set.indicator_of_notMem ht]

/-- The retarded integral commutes with every continuous spacetime dual pairing. -/
theorem spacetimePairing_retardedWaveOperator_eq_integral
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume : Measure ℝ))
    (v : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ)) :
    spacetimePairing (retardedWaveOperator f) v =
      ∫ s, spacetimePairing (retardedWaveAt s (f s)) v :=
  ((spacetimePairing.flip v).integral_comp_comm
    (integrable_retardedWaveAt (L1.integrable_coeFn f))).symm

end WaveEquation.Strichartz
