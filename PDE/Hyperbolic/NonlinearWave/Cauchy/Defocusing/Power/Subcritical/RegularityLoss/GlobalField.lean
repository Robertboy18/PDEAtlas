/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss.ZeroPatch

/-!
# Smooth data whose global wave lacks interior second derivatives

Local integral uniqueness identifies the incoming wave with the global trajectory. Its
positive nodal moment excludes interior second derivatives on an open positive-time band.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped ContDiff Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss

/-- One smooth compact data pair constructs a global signed-quadratic integral wave
which is not C² on the open positive-time band. Traces, tested PDE, support, energy,
and nonregularity all concern the same field. -/
theorem exists_smooth_data_global_quadratic_wave_not_contDiffOn_two_interior :
    ∃ g h : ℝ^3 → ℝ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      HasCompactSupport g ∧ HasCompactSupport h ∧ ∃ b R : ℝ, 0 < b ∧ 0 < R ∧
      ∃ U : (ℝ × ℝ^3) → ℝ,
        IsGlobalIntegralTrajectory 2 b (cauchyFreeField g h) U ∧
        (∀ x : ℝ^3, U (0, x) = g x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ U (t, x)) (h x) 0) ∧
        (∀ z : ℝ × ℝ^3, 0 ≤ z.1 → R + z.1 < ‖z.2‖ → U z = 0) ∧
        (∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t : ℝ, 0 < t →
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, U (s, x) * φ x))
            ((∫ x : ℝ^3, U (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower 2 (U (t, x)) * φ x) t) ∧
        (∀ S : ℝ, 0 < S → HasConservedEnergyOn 2 S U) ∧
        ¬ContDiffOn ℝ 2 (U ∘ timeSpaceContinuousLinearEquiv 3)
          {x | 0 < x 0 ∧ x 0 < 2} := by
  obtain ⟨g, h, hg, hh, hgs, hhs, u, hu, _, _, heq, _, ⟨M, hM, huM⟩, ⟨δ, hδ, hpatch⟩, hmoment⟩ :=
    exists_smooth_bounded_quadratic_wave_pos_nodalMoment_with_zero_patch
  have hg₃ : ContDiff ℝ 3 g := hg.of_le (by simp)
  have hh₂ : ContDiff ℝ 2 h := hh.of_le (by simp)
  obtain ⟨b, R, hb, hR, U, hU, hpos, hvel, hsupp, htest, henergy⟩ :=
    exists_global_integral_solution_of_compact_data
      (by norm_num : (1 : ℝ) < 2) (by norm_num) hg₃ hh₂ hgs hhs
  have hident := eq_global_of_bounded_local_quadratic_integral hb hM.le hu
    (contDiff_one_cauchyFreeField (hg₃.of_le (by norm_num)) (hh₂.of_le (by norm_num)))
    hU huM (fun p hp ↦ heq p ⟨hp.1, hp.2.le⟩)
  refine ⟨g, h, hg, hh, hgs, hhs, b, R, hb, hR, U, hU, hpos, hvel, hsupp, htest, henergy, ?_⟩
  intro hU₂
  have hu₂ : ContDiffOn ℝ 2 (u ∘ timeSpaceContinuousLinearEquiv 3) {x | 0 < x 0 ∧ x 0 < 2} :=
    hU₂.congr fun x hx ↦ hident (timeSpaceContinuousLinearEquiv 3 x) ⟨hx.1.le, hx.2⟩
  have hz := nodalMoment_eq_zero_of_interior_integral_identity
    (by norm_num : (1 : ℝ) < 2) le_rfl hg₃ hh₂ hu hu₂ hδ hpatch heq
  exact (ne_of_gt hmoment) hz

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss

end
