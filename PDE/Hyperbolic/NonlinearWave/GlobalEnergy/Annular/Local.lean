/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.TruncatedEnergy.KineticBound
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.SliceCompactness

/-!
# Compact Cauchy slices supply the initial face of a distant cone

Only separate compact displacement slices are assumed. The compact energy at
the initial time is obtained from the established compact velocity theorem.
The remaining bound is a potential value in the enclosing cylinder.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE PDE.Common PDE.Analysis

namespace WaveEquation

/-- Distant unit balls have kinetic energy bounded by a potential value
on the finite cone's enclosing cylinder, without common support in time. -/
theorem exists_radius_ballIntegral_kinetic_le_potential_value {n : ℕ} [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {s : ℝ}
    (hs0 : 0 ≤ s) :
    ∃ R > 0, ∀ τ, s ≤ τ → ∀ c : ℝ^n, R + (τ + 1 - s) < ‖c‖ →
      ∃ r ∈ Icc s τ, ∃ y ∈ Metric.closedBall c (τ + 1 - s),
        ballIntegral n (fun x ↦ classicalWaveEnergyDensity u (timeSpaceCons τ x)) c 1 ≤
          volume.real (Metric.ball c (τ + 1 - s)) *
            |V (u (timeSpaceCons r y))| := by
  have hc := WaveEquation.hasCompactSupport_energy_at_nonneg_time hV hVzero hu hwave hs hs0
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_ball (0 : ℝ^n)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun τ hsτ c hfar ↦ ?_⟩
  have hpde (r : ℝ) (hr : r ∈ Icc s τ) (x : ℝ^n) (_hx : x ∈ Metric.ball c (τ + 1 - r)) :
      semilinearWaveOperator V u (timeSpaceCons r x) = 0 :=
    semilinearWaveOperator_eq_zero_of_nonneg hV.continuous_deriv_one hu2 hwave (hs0.trans hr.1) x
  have hzero (x : ℝ^n) (hx : x ∈ Metric.ball c (τ + 1 - s)) :
      semilinearWaveEnergyDensity V u (timeSpaceCons s x) = 0 := by
    by_contra hn
    have hxR := hR (subset_tsupport _ (show x ∈ Function.support
      (semilinearWaveSpatialEnergyDensity V u s) from hn))
    rw [Metric.mem_ball, dist_zero_right] at hxR
    have hd : ‖x - c‖ < τ + 1 - s := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hc_le := norm_le_norm_add_norm_sub x c
    have hRR := le_max_left R 1
    linarith
  have hb := exists_potential_value_ballIntegral_kinetic_le
    hV hu2 c hsτ (show τ < τ + 1 by linarith) hpde hzero
  simpa only [add_sub_cancel_left] using hb

end WaveEquation
