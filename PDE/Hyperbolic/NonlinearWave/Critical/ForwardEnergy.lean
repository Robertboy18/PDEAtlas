/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.GlobalEnergy
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiniteForwardSupport
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.CompactSlab
import PDE.Analysis.Calculus.LocalExtension.ForwardBand
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import PDE.Analysis.Calculus.PowerPotential.Classical

/-!
# Quintic energy uniformly up to the initial boundary

The forward C2 quintic equation with compact Cauchy data has one energy
bound for all positive times before a finite terminal time. Finite propagation
derives common support. Continuity across the initial edge bounds early energy,
while one interior cone cap bounds the remaining times.

This supplies a constant independent of the starting time for linear estimates
in the critical continuation argument.
-/

@[expose] public section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- Forward C2 regularity closes the early-time gap in the energy bound.
The single constant precedes every positive start, with no terminal regularity. -/
theorem exists_uniform_energy_bound_of_forward_wave {u : ℝ^4 → ℝ} {T R : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 ≤ p 0 ∧ p 0 < T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0)
    (hsupport : ∀ t ∈ Ico 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0) :
    ∃ E : ℝ, ∀ t ∈ Ioo 0 T,
      Integrable (semilinearWaveSpatialEnergyDensity (Real.signedPowerPotential 5) u t) ∧
      semilinearWaveSpatialEnergy (Real.signedPowerPotential 5) u t ≤ E := by
  have hb : 0 < T / 2 := half_pos hT
  have hbT : T / 2 < T := half_lt_self hT
  have hui : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T} := hu.mono fun _ hp ↦ ⟨hp.1.le, hp.2⟩
  have hsuppi : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0 :=
    fun t ht ↦ hsupport t ⟨ht.1.le, ht.2⟩
  obtain ⟨E, hE⟩ := exists_global_energy_bound_of_wave hb hbT hui hwave hsuppi
  obtain ⟨v, hv, hvu⟩ := exists_contDiffOn_extension_halfOpenBand 0 hT hu
  obtain ⟨U, hU, heq⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
    (k := 2) (f := v) (s₀ := -1) (s := 0) (τ := T / 2) (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ)
    (hv.mono fun _ hp ↦ hp.2) (by norm_num) hbT
  have heval (t : ℝ) (ht : t ∈ Icc 0 (T / 2)) (x : ℝ^3) :
      U (timeSpaceCons t x) = u (timeSpaceCons t x) :=
    (heq _ (by simpa using ht)).eq_of_nhds.symm.trans
      (hvu (by simpa using ht.1))
  have heDensity (t : ℝ) (ht : t ∈ Ioc 0 (T / 2)) :
      semilinearWaveSpatialEnergyDensity (Real.signedPowerPotential 5) u t =
        semilinearWaveSpatialEnergyDensity (Real.signedPowerPotential 5) U t := by
    funext x
    have he : u =ᶠ[𝓝 (timeSpaceCons t x)] U :=
      (eventuallyEq_of_eqOn_forward hvu (by simpa using ht.1)).symm.trans
        (heq _ (by simpa using And.intro ht.1.le ht.2))
    simp only [semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity,
      classicalWaveEnergyDensity_congr_nhds he, he.eq_of_nhds]
  have hc : ContinuousOn (semilinearWaveSpatialEnergy (Real.signedPowerPotential 5) U)
      (Icc 0 (T / 2)) := by
    apply continuousOn_semilinearWaveSpatialEnergy_of_compact_support
      (Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5))
      (Real.signedPowerPotential_zero (by norm_num : (1 : ℝ) ≤ 5)) hU
      (isCompact_closedBall (0 : ℝ^3) (R + T)) hb
    intro t ht x hx
    rw [heval t ht x]
    apply hsupport t ⟨ht.1, ht.2.trans_lt hbT⟩ x
    have hx' : R + T < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    linarith [ht.2]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max E M, fun t ht ↦ ?_⟩
  obtain ⟨Et, hEt⟩ := exists_global_energy_bound_of_wave (half_pos ht.1)
    ((half_lt_self ht.1).trans ht.2) hui hwave hsuppi
  refine ⟨(hEt t ⟨(half_lt_self ht.1).le, ht.2⟩).1, ?_⟩
  by_cases hbt : T / 2 ≤ t
  · exact ((hE t ⟨hbt, ht.2⟩).2).trans (le_max_left E M)
  · have hte : t ∈ Ioc 0 (T / 2) := ⟨ht.1, (lt_of_not_ge hbt).le⟩
    have he : semilinearWaveSpatialEnergy (Real.signedPowerPotential 5) u t =
        semilinearWaveSpatialEnergy (Real.signedPowerPotential 5) U t := by
      unfold semilinearWaveSpatialEnergy
      rw [heDensity t hte]
    rw [he]
    exact (le_abs_self _).trans ((hM t ⟨ht.1.le, hte.2⟩).trans (le_max_right E M))

/-- Compact Cauchy traces and the forward PDE give support and one
energy bound for all positive times, including starts approaching zero. -/
theorem exists_support_and_uniform_energy_of_quintic_cauchy {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (g h : ℝ^3 → ℝ) (hu : ContDiffOn ℝ 2 u {p | 0 ≤ p 0 ∧ p 0 < T}) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) :
    ∃ R E : ℝ,
      (∀ t ∈ Ico 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0) ∧
      ∀ t ∈ Ioo 0 T,
        Integrable (semilinearWaveSpatialEnergyDensity (Real.signedPowerPotential 5) u t) ∧
        semilinearWaveSpatialEnergy (Real.signedPowerPotential 5) u t ≤ E := by
  have hf : ContDiff ℝ 1 (fun z : ℝ ↦ z ^ 5) := contDiff_id.pow 5
  obtain ⟨R, hR⟩ := (hgc.union hhc).isBounded.exists_norm_le
  have hsupp : ∀ t ∈ Ico 0 T, ∀ x : ℝ^3,
      R + t < ‖x‖ → u (timeSpaceCons t x) = 0 := by
    apply PDE.Hyperbolic.NonlinearWave.Cauchy.eq_zero_of_cauchyData_finite_strip
      hf.locallyLipschitz (by simp)
      (hu.mono fun p hp ↦ ⟨hp.1.le, hp.2⟩) (hu.of_le (by norm_num))
      hwave hpos (fun x ↦ (hvel x).derivWithin (uniqueDiffWithinAt_Ici 0))
    · exact fun x hx ↦ image_eq_zero_of_notMem_tsupport
        (fun hx' ↦ (not_le_of_gt hx) (hR x (Or.inl hx')))
    · exact fun x hx ↦ image_eq_zero_of_notMem_tsupport
        (fun hx' ↦ (not_le_of_gt hx) (hR x (Or.inr hx')))
  obtain ⟨E, hE⟩ := exists_uniform_energy_bound_of_forward_wave hT hu hwave hsupp
  exact ⟨R, E, hsupp, hE⟩

end WaveEquation.Critical
