/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardBasic
public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.CompactData.Domination
public import PDE.Hyperbolic.NonlinearWave.SmallData.Mass
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.InitialData

/-!
# Energy at the initial boundary of a forward wave

The continuous differential within the closed forward half-space identifies the
initial energy with the displacement gradient and right velocity. Finite
propagation places all nearby energy densities in one compact ball, so the
spatial energy tends to this data energy from positive time. The density through
initial time is `forwardSemilinearWaveEnergyDensity` of `GlobalEnergy.ForwardBasic`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Topology BigOperators

namespace WaveEquation.NegativeEnergy

variable {n : ℕ}

/-- The total energy tends to the Cauchy-data energy from the right.
Compact support is propagated by the field. -/
theorem tendsto_semilinearWaveSpatialEnergy_initial {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {g h : ℝ^n → ℝ}
    {R : ℝ} (hV : Continuous V) (hVzero : V 0 = 0) (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hs : SmallData.HasForwardSupport u R) (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x)
    (hh : ∀ x, R < ‖x‖ → h x = 0) :
    Tendsto (semilinearWaveSpatialEnergy V u) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ^n, (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x))) := by
  let K := Metric.closedBall (0 : ℝ^n) (R + 1)
  let F : ℝ → ℝ := fun t ↦ ∫ x in K, forwardSemilinearWaveEnergyDensity V u t x
  have hF : Continuous F := continuous_parametric_integral_of_continuous
    (continuous_forwardSemilinearWaveEnergyDensity hV hu) (isCompact_closedBall _ _)
  have hinitial (x : ℝ^n) (hx : R < ‖x‖) : forwardSemilinearWaveEnergyDensity V u 0 x = 0 := by
    have hD := forwardDifferential_initial_eq_zero hu (isOpen_lt continuous_const continuous_norm)
      (fun y hy ↦ hs 0 le_rfl y (by simpa using hy)) (fun y hy ↦ (hvel y).trans (hh y hy)) hx
    simp [forwardSemilinearWaveEnergyDensity, EuclideanSpace.real_norm_sq_eq, hD,
      hs 0 le_rfl x (by simpa using hx), hVzero]
  have hFzero : F 0 = ∫ x : ℝ^n, (1 / 2 : ℝ) *
      ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x) := by
    have he := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (f := forwardSemilinearWaveEnergyDensity V u 0) (s := K) (fun x hx ↦ ?_)
    · change (∫ x in K, forwardSemilinearWaveEnergyDensity V u 0 x) = _
      rw [he]
      exact integral_congr_ae (Eventually.of_forall
        (forwardSemilinearWaveEnergyDensity_initial_of_contDiffOn_band zero_lt_one
          (hu.mono fun _ hp ↦ hp.1) hpos hvel))
    · apply hinitial
      have hx' : R + 1 < ‖x‖ := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      linarith
  have heq : semilinearWaveSpatialEnergy V u =ᶠ[𝓝[>] 0] F := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    change (∫ x : ℝ^n, semilinearWaveSpatialEnergyDensity V u t x) = _
    have he := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (f := semilinearWaveSpatialEnergyDensity V u t) (s := K) (fun x hx ↦ ?_)
    · rw [← he]
      apply setIntegral_congr_fun measurableSet_closedBall
      exact fun x _ ↦ (forwardSemilinearWaveEnergyDensity_eq ht x).symm
    · have hx' : R + 1 < ‖x‖ := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      exact (semilinearWaveEnergyDensity_eventuallyEq_zero hVzero
        (eventuallyEq_zero_of_cone_support (fun r hr ↦ hs r hr.le) ht
          (show R + t < ‖x‖ by linarith [show t < 1 from ht1]))).eq_of_nhds
  rw [← hFzero]
  exact (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

end WaveEquation.NegativeEnergy
