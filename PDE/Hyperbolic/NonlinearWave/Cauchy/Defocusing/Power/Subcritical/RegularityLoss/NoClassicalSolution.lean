/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ClassicalIdentification
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss.GlobalField

/-!
# Smooth data admitting no global classical quadratic wave

Every classical competitor with the same position and right velocity agrees with the constructed
integral field. Its failure of interior second differentiability rules out every such
competitor.
-/

@[expose] public noncomputable section

section

open Set PDE PDE.Analysis PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped ContDiff

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss

/-- One compact smooth datum pair admits no global classical solution of the
signed-quadratic equation. The excluded class requires C² only at positive
times and C¹ up to the initial face, with the right velocity trace. -/
theorem exists_smooth_compact_data_no_global_classical_quadratic_wave :
    ∃ g h : ℝ^3 → ℝ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      HasCompactSupport g ∧ HasCompactSupport h ∧
      ¬∃ v : ℝ^4 → ℝ, ContDiffOn ℝ 2 v {z | 0 < z 0} ∧
        ContDiffOn ℝ 1 v {z | 0 ≤ z 0} ∧
        (∀ x : ℝ^3, v (timeSpaceCons 0 x) = g x) ∧
        (∀ x : ℝ^3, derivWithin (fun t ↦ v (timeSpaceCons t x)) (Ici 0) 0 = h x) ∧
        (∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
          waveOperator v (timeSpaceCons t x) +
            Real.signedPower 2 (v (timeSpaceCons t x)) = 0) := by
  obtain ⟨g, h, hg, hh, hgs, hhs, b, _, hb, _, U, hU, _, _, _, _, _, hnot⟩ :=
    exists_smooth_data_global_quadratic_wave_not_contDiffOn_two_interior
  refine ⟨g, h, hg, hh, hgs, hhs, ?_⟩
  rintro ⟨v, hv, hv₀, hpos, hvel, hw⟩
  have he := eq_global_integral_of_interior_classical_power
    (p := 2) (L := 3) (S := 2) (by norm_num) hb (by norm_num) (by norm_num) hU
    (hv.mono (fun _ hz ↦ hz.1)) (hv₀.mono (fun _ hz ↦ hz.1))
    (hg.of_le (by simp)) (hh.of_le (by simp)) hgs hhs hpos hvel (fun t ht x ↦ hw t ht.1 x)
  apply hnot
  refine (hv.mono (fun _ hz ↦ hz.1)).congr fun z hz ↦ ?_
  have hz' : timeSpaceCons (z 0) (spatialPartCLM 3 z) = z := timeSpaceCons_spatialPartCLM z
  have he' := (he (z 0) ⟨hz.1.le, hz.2⟩ (spatialPartCLM 3 z)).symm
  rw [hz'] at he'
  simpa only [Function.comp_apply, timeSpaceContinuousLinearEquiv_apply,
    PDE.time, spatialPartCLM_eq_spatialPart] using he'

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss

end
