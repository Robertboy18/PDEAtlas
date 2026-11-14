/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.LocalExistence
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.IntegralAgreement

/-!
# Local classical waves with a reaction of finite regularity

For the reaction `signedPower (5/2) u = |u|^{3/2} u` on `ℝ³`, compactly supported data
`g ∈ C³`, `h ∈ C²` give a `C²` solution of `□u + |u|^{3/2} u = 0` on a time interval
`[0, T)` (`exists_classical_signedPower_of_compact_data`).

The general theorem `exists_classical_of_compact_data` asks only that the reaction is `C²`. The
last two examples are reactions that the signed powers do not reach: the focusing cubic `-u³`,
for which `z f(z) ≤ 0`, and `cos u`, which does not vanish at zero.
-/

open Set PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

noncomputable section

/-- Compactly supported `C³ × C²` data give a local `C²` solution. -/
example {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ^4 → ℝ, ContDiff ℝ 2 u ∧
      (∀ t ∈ Ico 0 T, ∀ x : ℝ^3,
        waveOperator u (timeSpaceCons t x) +
          Real.signedPower (5 / 2) (u (timeSpaceCons t x)) = 0) ∧
      (∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x) ∧
      ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (timeSpaceCons t x)) (h x) 0 := by
  obtain ⟨T, u, hu, hsol⟩ :=
    exists_classical_signedPower_of_compact_data (by norm_num : (2 : ℝ) < 5 / 2)
      hg hh hgs hhs
  refine ⟨T, hsol.time_pos, u, hu, ?_, hsol.position, ?_⟩
  · intro t ht x
    have he := hsol.equation (timeSpaceCons t x) (by simpa only [timeSpaceCons_zero] using ht)
    exact eq_neg_iff_add_eq_zero.mp he
  · intro x
    simpa only [hsol.velocity] using
      PDE.hasDerivAt_timeSpaceCons u 0 x (hu.differentiable (by norm_num) _)

/-- The focusing cubic `□u = u³`: a reaction with `z f(z) ≤ 0`. -/
example {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, ContDiff ℝ 2 u ∧
      SmallData.Classical.IsSolutionBefore (fun z ↦ -z ^ 3) g h T u :=
  exists_classical_of_compact_data (by fun_prop) hg hh hgs hhs

/-- The reaction `cos u`, which does not vanish at zero. -/
example {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, ContDiff ℝ 2 u ∧
      SmallData.Classical.IsSolutionBefore Real.cos g h T u :=
  exists_classical_of_compact_data Real.contDiff_cos hg hh hgs hhs
