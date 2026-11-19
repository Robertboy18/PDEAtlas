/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss.GlobalField
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss.NoClassicalSolution

/-!
# Regularity loss for the wave equation with reaction `|u| u`

These are the signed-power results at exponent two, where `signedPower 2 u = |u| u`. There
are smooth compactly supported data on `ℝ³` for which `□v + |v| v = 0` has no solution
that is `C²` for `t > 0`, `C¹` for `t ≥ 0` and attains the data
(`exists_smooth_compact_data_no_global_classical_abs_wave`). There are also smooth
compactly supported data with a global `C¹` weak solution that is not `C²` on the slab
`0 < t < 2` (`exists_smooth_compact_data_global_abs_wave_not_contDiffOn_two_interior`).
-/

@[expose] public noncomputable section

section

open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss
open Set PDE PDE.Common WaveEquation
open scoped ContDiff

namespace PDE.Examples.Cauchy.FinitePower

/-- There are smooth compactly supported data for which `□v + |v| v = 0` has no solution
that is `C²` for `t > 0`, `C¹` for `t ≥ 0` and attains the data. -/
theorem exists_smooth_compact_data_no_global_classical_abs_wave :
    ∃ g h : ℝ^3 → ℝ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      HasCompactSupport g ∧ HasCompactSupport h ∧
      ¬∃ v : ℝ^4 → ℝ, ContDiffOn ℝ 2 v {z | 0 < z 0} ∧
        ContDiffOn ℝ 1 v {z | 0 ≤ z 0} ∧
        (∀ x : ℝ^3, v (timeSpaceCons 0 x) = g x) ∧
        (∀ x : ℝ^3, derivWithin (fun t ↦ v (timeSpaceCons t x)) (Ici 0) 0 = h x) ∧
        (∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
          waveOperator v (timeSpaceCons t x) +
            |v (timeSpaceCons t x)| * v (timeSpaceCons t x) = 0) := by
  simpa only [Real.signedPower, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
    exists_smooth_compact_data_no_global_classical_quadratic_wave

end PDE.Examples.Cauchy.FinitePower

end

section

open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss
open Set MeasureTheory PDE PDE.Common
open scoped ContDiff Laplacian

namespace PDE.Examples.Cauchy.FinitePower

/-- There are smooth compactly supported data with a global `C¹` solution of
`□u + |u| u = 0`, tested against `C²` compactly supported functions, that is not `C²` on
the slab `0 < t < 2`. -/
theorem exists_smooth_compact_data_global_abs_wave_not_contDiffOn_two_interior :
    ∃ g h : ℝ^3 → ℝ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      HasCompactSupport g ∧ HasCompactSupport h ∧ ∃ b : ℝ, 0 < b ∧
      ∃ u : (ℝ × ℝ^3) → ℝ,
        ContDiffOn ℝ 1 u {p | -b < p.1} ∧
        (∀ x : ℝ^3, u (0, x) = g x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
        (∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t : ℝ, 0 < t →
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
            ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, |u (t, x)| * u (t, x) * φ x) t) ∧
        ¬ContDiffOn ℝ 2 (u ∘ timeSpaceContinuousLinearEquiv 3)
          {x | 0 < x 0 ∧ x 0 < 2} := by
  obtain ⟨g, h, hg, hh, hgs, hhs, b, _, hb, _, u, hu, hpos, hvel, _, htest, _, hnot⟩ :=
    exists_smooth_data_global_quadratic_wave_not_contDiffOn_two_interior
  refine ⟨g, h, hg, hh, hgs, hhs, b, hb, u, hu.regular, hpos, hvel, ?_, hnot⟩
  simpa only [Real.signedPower, show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one] using htest

end PDE.Examples.Cauchy.FinitePower

end
