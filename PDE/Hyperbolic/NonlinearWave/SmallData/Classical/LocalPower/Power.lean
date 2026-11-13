/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Construction
public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.PowerSource
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Local classical waves for noninteger absolute powers

For every real `p > 2`, zero displacement and compactly supported C² velocity
construct a local classical solution of `u_tt - Δu = |u|^p` in three dimensions.
The representative is jointly C² across the initial hyperplane; its ordinary
initial velocity is the prescribed function. In particular the result applies
to smooth compact velocity and to `2 < p < 1 + √2`.

This argument uses the C² regularity of the power at zero. The case `1 < p < 2` needs a different
lower-regularity argument.
-/

@[expose] public noncomputable section

open Set PDE.Analysis PDE.Common
open PDE (partialDeriv laplacian)

namespace WaveEquation.SmallData.Classical.LocalPower

/-- Local existence for a real power greater than two, with
compactly supported C² velocity and zero displacement. -/
theorem exists_solutionBefore_abs_rpow_three {p : ℝ} (hp : 2 < p)
    {h : ℝ^3 → ℝ} (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, ContDiff ℝ 2 u ∧
      IsSolutionBefore (fun z ↦ -|z| ^ p) (fun _ ↦ 0) h T u := by
  exact exists_solutionBefore_of_contDiff_two (WaveEquation.SmallData.contDiff_two_abs_rpow hp)
    (ofCompactSupport h hh.continuous hhc) hh

/-- The constructed noninteger-power wave satisfies the PDE written using
ordinary time derivatives and the spatial Laplacian, together with ordinary
Cauchy traces and joint C² regularity at time zero. -/
theorem exists_classical_abs_rpow_three {p : ℝ} (hp : 2 < p)
    {h : ℝ^3 → ℝ} (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ^4 → ℝ,
      ContDiff ℝ 2 u ∧
      (∀ t ∈ Ico 0 T, ∀ x : ℝ^3,
        deriv (deriv (fun s ↦ u (timeSpaceCons s x))) t -
          laplacian (fun y ↦ u (timeSpaceCons t y)) x =
            |u (timeSpaceCons t x)| ^ p) ∧
      (∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0) ∧
      (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (timeSpaceCons t x)) (h x) 0) := by
  obtain ⟨T, u, hu, hs⟩ := exists_solutionBefore_abs_rpow_three hp hh hhc
  refine ⟨T, hs.time_pos, u, hu, ?_, hs.position, ?_⟩
  · intro t ht x
    rw [← waveOperator_timeSpaceCons hu]
    simpa only [neg_neg] using hs.equation (timeSpaceCons t x) (by simpa using ht)
  · intro x
    simpa only [hs.velocity] using
      PDE.hasDerivAt_timeSpaceCons u 0 x (hu.differentiable (by norm_num) _)

end WaveEquation.SmallData.Classical.LocalPower
