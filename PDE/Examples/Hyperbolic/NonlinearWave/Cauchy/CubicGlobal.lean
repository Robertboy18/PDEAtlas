/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.GlobalSmooth
import CAS.ExactTactic

/-!
# Global smooth cubic waves from nonzero compact data

The defocusing cubic wave equation `□u + u³ = 0` on `ℝ³` is energy subcritical
(`1 < 3 < 5`). For bump data `g = h` with `g 0 = 1`, the global theorem
`exists_unique_global_smooth_wave_of_smooth_signedPower` gives a solution that is
smooth for `t ≥ 0`, solves the equation for all `t > 0`, and is the only solution with
these data that is `C²` for `t > 0` and `C¹` for `t ≥ 0`.
-/

@[expose] public noncomputable section

open Set PDE PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

namespace PDE.Examples.Cauchy.CubicGlobal

/-- There are nonzero smooth compactly supported data for which `□u + u³ = 0` has a
global smooth solution, unique among solutions that are `C²` for `t > 0` and `C¹` for
`t ≥ 0`. -/
theorem exists_nonzero_compact_data_unique_global_cubic_wave :
    ∃ g h : ℝ^3 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧
      HasCompactSupport g ∧ HasCompactSupport h ∧ g 0 = 1 ∧ h 0 = 1 ∧
      ∃ u : ℝ^4 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u {z | 0 ≤ z 0} ∧
        (∀ x, u (timeSpaceCons 0 x) = g x) ∧
        (∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) ∧
        (∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
          waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 3 = 0) ∧
        ∀ v : ℝ^4 → ℝ,
          ContDiffOn ℝ 2 v {z | 0 < z 0} → ContDiffOn ℝ 1 v {z | 0 ≤ z 0} →
          (∀ x, v (timeSpaceCons 0 x) = g x) →
          (∀ x, HasDerivWithinAt (fun t ↦ v (timeSpaceCons t x)) (h x) (Ici 0) 0) →
          (∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
            waveOperator v (timeSpaceCons t x) + v (timeSpaceCons t x) ^ 3 = 0) →
          EqOn v u {z | 0 ≤ z 0} := by
  let b : ContDiffBump (0 : ℝ^3) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hpow : Real.signedPower 3 = fun x : ℝ ↦ x ^ 3 := by
    funext x
    unfold Real.signedPower
    norm_num only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two, sq_abs]
    cas
  have hs : ContDiff ℝ (⊤ : ℕ∞) (Real.signedPower 3) := by
    rw [hpow]
    exact contDiff_id.pow 3
  refine ⟨b, b, b.contDiff, b.contDiff, b.hasCompactSupport, b.hasCompactSupport, hb, hb, ?_⟩
  simpa only [hpow] using exists_unique_global_smooth_wave_of_smooth_signedPower
    (by norm_num : (1 : ℝ) < 3) (by norm_num : (3 : ℝ) < 5) hs b b
    b.contDiff b.contDiff b.hasCompactSupport b.hasCompactSupport

end PDE.Examples.Cauchy.CubicGlobal
