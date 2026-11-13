/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PowerPotential
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
import PDE.Analysis.Calculus.PowerPotential.Classical
import PDE.Analysis.Calculus.SpaceTime.Support
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.NonlinearWave.Critical.Cone.QuinticEnergy
import CAS.ExactTactic

/-!
# Whole-space quintic energy on interior time bands

The defocusing quintic equation and speed-one support give integrable energy
slices and uniform whole-space energy and L6 bounds after any interior starting time.
One large cone contains the entire support until the terminal time. Its monotone
energy bounds the whole-space energy.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- One interior energy cap uniformly bounds the whole-space quintic energy.
The speed-one support supplies integrability of every energy slice. -/
theorem exists_global_energy_bound_of_wave {u : ℝ^4 → ℝ} {T R b : ℝ} (hb : 0 < b) (hbT : b < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^
      5 = 0)
    (hsupport : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0) :
    ∃ E : ℝ, ∀ t ∈ Ico b T, Integrable (semilinearWaveSpatialEnergyDensity
      (Real.signedPowerPotential 5) u t) ∧ semilinearWaveSpatialEnergy (Real.signedPowerPotential 5)
      u t ≤ E := by
  let A : ℝ := |R| + 2 * T + 1
  let E : ℝ := ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
    (Real.signedPowerPotential 5) u (timeSpaceCons b x)) 0 (A - b)
  refine ⟨E, fun t ht ↦ ?_⟩
  have ht0 : 0 < t := hb.trans_le ht.1
  have hTA : T < A := by dsimp [A]; linarith [abs_nonneg R, hb.trans hbT]
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hut (x : ℝ^3) : ContDiffAt ℝ 2 u (timeSpaceCons t x) :=
    hu.contDiffAt (hopen.mem_nhds (by simpa using And.intro ht0 ht.2))
  have hc : Continuous (semilinearWaveSpatialEnergyDensity (Real.signedPowerPotential 5) u t) :=
    continuous_iff_continuousAt.mpr fun x ↦ (contDiffAt_semilinearWaveEnergyDensity
        (Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)).contDiffAt
        (hut x)).continuousAt.comp
        (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous.continuousAt
  have hz (x : ℝ^3) (hx : R + T < ‖x‖) :
      semilinearWaveSpatialEnergyDensity (Real.signedPowerPotential 5) u t x = 0 := by
    have hd (i : Fin 4) := partialDeriv_eq_zero_of_forward_support hsupport ⟨ht0, ht.2⟩ i hx
    have hg : classicalWaveSpatialGradient u (timeSpaceCons t x) = 0 := by
      ext i
      exact hd i.succ
    have hv := hsupport t ⟨ht0, ht.2⟩ x (by linarith [ht.2])
    simp only [semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity,
      classicalWaveEnergyDensity, hd 0, hg, hv, norm_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero, mul_zero]
    simpa only [zero_add] using
      (Real.signedPowerPotential_zero (by norm_num : (1 : ℝ) ≤ 5))
  have hi : Integrable (semilinearWaveSpatialEnergyDensity
      (Real.signedPowerPotential 5) u t) := by
    apply hc.integrable_of_hasCompactSupport
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) (R + T)) fun x hx ↦ ?_
    exact hz x (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx)
  refine ⟨hi, ?_⟩
  have henergy : ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential 5) u (timeSpaceCons t x)) 0 (A - t) ≤ E := by
    apply WaveEquation.ballIntegral_energy_le_of_le_of_contDiffOn_finite_band
      (Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5))
      (fun z ↦ Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5) z)
      hu 0 hb ht.1 ht.2 (ht.2.trans hTA)
    intro q hq x _
    have hpde := hwave q ⟨hb.trans_le hq.1, hq.2.trans_lt ht.2⟩ x
    unfold semilinearWaveOperator
    rw [(Real.hasDerivAt_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5) _).deriv]
    have hid : Real.signedPower 5 (u (timeSpaceCons q x)) = u (timeSpaceCons q x) ^ 5 := by
      unfold Real.signedPower
      rw [show (5 : ℝ) - 1 = (4 : ℕ) by norm_num, Real.rpow_natCast,
        (show Even 4 by decide).pow_abs]
      cas
    rwa [hid]
  have heq : ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential 5) u (timeSpaceCons t x)) 0 (A - t) =
      semilinearWaveSpatialEnergy (Real.signedPowerPotential 5) u t := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    have hnorm : A - t ≤ ‖x‖ := by
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
    exact hz x (by dsimp [A] at hnorm; linarith [le_abs_self R, ht.2])
  rwa [heq] at henergy


/-- The defocusing equation and speed-one support give a uniform whole-space
L6 bound from one interior energy cap, without terminal regularity. -/
theorem exists_global_lpNorm_six_bound_of_wave {u : ℝ^4 → ℝ} {T R b : ℝ} (hb : 0 < b) (hbT : b < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^
      5 = 0)
    (hsupport : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0) :
    ∃ M : ℝ, ∀ t ∈ Ico b T, lpNorm (fun x ↦ u (timeSpaceCons t x)) 6 volume ≤ M := by
  let A : ℝ := |R| + 2 * T + 1
  obtain ⟨E, hE⟩ := exists_global_energy_bound_of_wave hb hbT hu hwave hsupport
  let M : ℝ := max (6 * E) 1
  have hM : 1 ≤ M := le_max_right _ _
  refine ⟨M, fun t ht ↦ ?_⟩
  have ht0 : 0 < t := hb.trans_le ht.1
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hut (x : ℝ^3) : ContDiffAt ℝ 2 u (timeSpaceCons t x) :=
    hu.contDiffAt (hopen.mem_nhds (by simpa using And.intro ht0 ht.2))
  have hc : Continuous (fun x ↦ u (timeSpaceCons t x)) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hut x).continuousAt.comp
      (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous.continuousAt
  have hsup : Function.support (fun x ↦ u (timeSpaceCons t x)) ⊆ Metric.ball 0 (A - t) := by
    intro x hx
    by_contra hnot
    have hnorm : A - t ≤ ‖x‖ := by
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hnot
    exact hx (hsupport t ⟨ht0, ht.2⟩ x (by dsimp [A] at hnorm; linarith [le_abs_self R, ht.2]))
  have heq : lpNorm (fun x ↦ u (timeSpaceCons t x)) 6 (volume.restrict (Metric.ball 0 (A - t))) =
      lpNorm (fun x ↦ u (timeSpaceCons t x)) 6 volume := congrArg ENNReal.toReal
      (eLpNorm_restrict_eq_of_support_subset hc.aestronglyMeasurable hsup)
  have hpow := lpNorm_six_pow_le_quintic_ball_energy hut 0 (A - t)
  rw [heq] at hpow
  have henergy : ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential 5) u (timeSpaceCons t x)) 0 (A - t) ≤ E :=
    (setIntegral_le_integral (hE t ht).1 (Filter.Eventually.of_forall fun x ↦
      semilinearWaveEnergyDensity_nonneg _
        (Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5)) u
        (timeSpaceCons t x))).trans (hE t ht).2
  apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (zero_le_one.trans hM)
  exact (hpow.trans (mul_le_mul_of_nonneg_left henergy (by norm_num))).trans
    ((le_max_left (6 * E) 1).trans (le_self_pow₀ hM (by norm_num : (6 : ℕ) ≠ 0)))

end WaveEquation.Critical
