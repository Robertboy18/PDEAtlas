/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Analysis.MeasureTheory.Lp.Restriction
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Duhamel

/-!
# Causality under restriction of the wave forcing interval

Restricting a forcing class above an observation time preserves its physical
Duhamel value. The proof transports Lp representatives through the canonical
measure-restriction map and uses the vanishing sine integrand after
the observation time. This allows one forcing trajectory to identify a wave
at every time of a closed forward interval.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace WaveEquation.Fourier

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Restricting the forcing interval above an observation time does not change
its physical causal Duhamel value. Representatives are transported explicitly. -/
theorem duhamelL2_restrict_right (a b c t : ℝ) (hcb : c ≤ b) (htc : t ≤ c)
    (f : Lp (Lp F 2 (volume : Measure V)) 1 (volume.restrict (Icc a b))) :
    duhamelL2 a c t (Lp.restrictionCLMOfLE (Measure.restrict_mono (Icc_subset_Icc le_rfl hcb)
      le_rfl) f) = duhamelL2 a b t f := by
  rw [duhamelL2_apply, duhamelL2_apply]
  calc
    _ = ∫ s in Icc a c, sineEvolution (max (t - s) 0) (f s) := by
      apply integral_congr_ae
      filter_upwards [Lp.restrictionCLMOfLE_apply_ae
        (Measure.restrict_mono (Icc_subset_Icc le_rfl hcb) le_rfl) f] with s hs
      rw [hs]
    _ = _ := (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
      (Icc_subset_Icc le_rfl hcb) fun s hs ↦ by
        have hcs : c < s := lt_of_not_ge fun hsc ↦ hs.2 ⟨hs.1.1, hsc⟩
        rw [max_eq_right (sub_nonpos.mpr (htc.trans hcs.le))]
        exact sineEvolution_zero_apply (f s)).symm

end WaveEquation.Fourier
