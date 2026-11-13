/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Cutoff.Balance
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.SliceCompactness

/-!
# Compact-slice wave energy and cutoff stress

Every sufficiently large smooth bump captures the two energy caps and the initial
momentum. The resulting double-time identity assumes no common spatial support between caps.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Topology ContDiff

namespace WaveEquation

/-- Separate compact displacement slices imply the exact stress formula for every sufficiently
large bump. The global `C³` hypothesis represents a smooth extension across the initial face;
the wave equation is required only at positive times. No differentiability of `deriv V` is used. -/
theorem exists_radius_energy_sub_eq_timeWeightedStress {n : ℕ} [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ r, 0 < r → ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0)
    (hs : ∀ r, 0 ≤ r → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons r x))) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) :
    ∃ R₀ > 0, ∀ χ : ContDiffBump (0 : ℝ^n), R₀ ≤ χ.rIn → semilinearWaveSpatialEnergy V u t -
      semilinearWaveSpatialEnergy V u s = ∫ r in s..t, (t - r) * cutoffStress χ V u r := by
  have hes := WaveEquation.hasCompactSupport_energy_at_nonneg_time hV hVzero hu hwave hs hs0
  have het := WaveEquation.hasCompactSupport_energy_at_nonneg_time
    hV hVzero hu hwave hs (hs0.trans hst)
  have hq (i : Fin n) : HasCompactSupport (semilinearWaveSpatialEnergyFlux u i s) :=
    hasCompactSupport_semilinearWaveSpatialEnergyFlux
      (fun _ ↦ (hu.differentiable (by norm_num)).differentiableAt) (hs s hs0) i
  let K := tsupport (semilinearWaveSpatialEnergyDensity V u s) ∪
    tsupport (semilinearWaveSpatialEnergyDensity V u t) ∪
      ⋃ i : Fin n, tsupport (semilinearWaveSpatialEnergyFlux u i s)
  have hK : IsCompact K :=
    (hes.isCompact.union het.isCompact).union (isCompact_iUnion fun i ↦ (hq i).isCompact)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℝ^n)
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun χ hχ ↦ ?_⟩
  have hsub : K ⊆ Metric.ball (0 : ℝ^n) χ.rIn :=
    hR.trans (Metric.ball_subset_ball ((le_max_left R 1).trans hχ))
  apply energy_sub_eq_timeWeightedStress_of_endpoint_supports
    isOpen_univ hst (subset_univ _) χ.contDiff χ.hasCompactSupport hV
    (fun _ _ _ ↦ (hu.of_le (by norm_num)).contDiffAt) (fun r hr ↦ hwave r (hs0.trans_lt hr.1))
  · intro x hx
    exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hsub (Or.inl (Or.inl hx))))
  · intro x hx
    exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hsub (Or.inl (Or.inr hx))))
  · intro i x hx
    apply χ.eventuallyEq_one_of_mem_ball
    apply hsub
    exact Or.inr (mem_iUnion.mpr ⟨i, hx⟩)

end WaveEquation
