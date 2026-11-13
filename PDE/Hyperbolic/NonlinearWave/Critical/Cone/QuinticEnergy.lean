/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PowerPotential
public import PDE.Hyperbolic.NonlinearWave.Critical.Cone.EnergyDecay
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.EnergyEnlargement
import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.Limit
import CAS.ExactTactic

/-!
# Full quintic energy decay and enlarged cones

The quintic equation and two linear prefix estimates give full local energy decay. Radius continuity
then gives a uniformly small enlarged cone, and nonnegative kinetic energy controls the local L⁶
norm.

These are the first estimates of step 5 of the proof of Evans, §12.4, Theorem 3: the limits (18)
and (19) give the small local energy (23), radius continuity gives the enlarged cone of (24), and
the energy controls the local L⁶ norm, as in the energy calculation that follows (24). The linear
estimates remain hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, steps 4-5 of its proof, equations (18),
  (19), (23) and (24).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- Quintic local energy vanishes, conditional on the two linear prefix estimates. -/
theorem tendsto_quintic_localEnergy_of_wave_strichartz {u : ℝ^4 → ℝ} {T C K L : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0)
    (hC : 0 < C) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlinear : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ico s T, lpNorm (fun r ↦
      lpNorm (fun x ↦ u (timeSpaceCons r x)) 12 (volume.restrict (Metric.ball c (T - r)))) 4
      (volume.restrict (Icc s t)) ≤ C + K * ∫ r in Icc s t, lpNorm
      (fun x ↦ u (timeSpaceCons r x) ^ 5) 2 (volume.restrict (Metric.ball c (T - r))))
    (hderivative : ∀ i : Fin 4, ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 (volume.restrict (Metric.ball c (T - r))) ≤
      A + L * ∫ q in Icc s r, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 *
      (∂[i] u) (timeSpaceCons q x)) 2 (volume.restrict (Metric.ball c (T - q)))) :
    Tendsto (fun t ↦ ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential 5) u (timeSpaceCons t x)) c (T - t)) (𝓝[<] T) (𝓝 0) := by
  have hkin := tendsto_integral_kinetic_gradient_of_wave_strichartz hT hu c hwave
    hC hK hL hlinear hderivative
  have hpot := tendsto_integral_quinticSlice_zero_of_wave hT hu c hwave
  have hlim := (hkin.const_mul (1 / 2 : ℝ)).add (hpot.div_const 6)
  simp only [mul_zero, zero_div, add_zero] at hlim
  have hVeq : Real.signedPowerPotential 5 = fun z ↦ z ^ 6 / 6 := by
    funext z
    norm_num [Real.signedPowerPotential, Real.rpow_ofNat,
      (show Even 6 by decide).pow_abs]
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hut (x : ℝ^3) : ContDiffAt ℝ 2 u (timeSpaceCons t x) :=
    hu.contDiffAt (hopen.mem_nhds (by simpa using ht))
  have hs := (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous
  have he : Continuous (fun x ↦ classicalWaveEnergyDensity u (timeSpaceCons t x)) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (contDiffAt_classicalWaveEnergyDensity (m := 1) (hut x)).continuousAt.comp hs.continuousAt
  have hv : Continuous (fun x ↦ u (timeSpaceCons t x) ^ 6 / 6) :=
    ((continuous_iff_continuousAt.mpr fun x ↦
      (hut x).continuousAt.comp hs.continuousAt).pow 6).div_const 6
  have hint {f : ℝ^3 → ℝ} (hf : Continuous f) : IntegrableOn f (Metric.ball c (T - t)) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall c (T - t))).mono_set
      Metric.ball_subset_closedBall
  symm
  simp only [ballIntegral, semilinearWaveEnergyDensity, hVeq]
  rw [integral_add (hint he) (hint hv)]
  simp only [classicalWaveEnergyDensity, integral_const_mul, integral_div]

/-- The quintic wave admits a late enlarged cone of arbitrarily small
energy, conditional only on the stated critical and differentiated linear estimates. -/
theorem exists_enlarged_quintic_cone_energy_lt_of_wave_strichartz {u : ℝ^4 → ℝ} {T C K L : ℝ}
    (hT : 0 < T) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^
      5 = 0)
    (hC : 0 < C) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlinear : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ico s T, lpNorm (fun r ↦
      lpNorm (fun x ↦ u (timeSpaceCons r x)) 12 (volume.restrict (Metric.ball c (T - r)))) 4
      (volume.restrict (Icc s t)) ≤ C + K * ∫ r in Icc s t, lpNorm
      (fun x ↦ u (timeSpaceCons r x) ^ 5) 2 (volume.restrict (Metric.ball c (T - r))))
    (hderivative : ∀ i : Fin 4, ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 (volume.restrict (Metric.ball c (T - r))) ≤
      A + L * ∫ q in Icc s r, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 *
      (∂[i] u) (timeSpaceCons q x)) 2 (volume.restrict (Metric.ball c (T - q))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ Ioo 0 T, ∃ δ > 0, ∀ t ∈ Ico s T, ballIntegral 3 (fun x ↦
      semilinearWaveEnergyDensity (Real.signedPowerPotential 5) u (timeSpaceCons t x)) c
      (T + δ - t) < ε := by
  have henergy := tendsto_quintic_localEnergy_of_wave_strichartz hT hu c
    (fun t ht x _ ↦ hwave t ht x) hC hK hL hlinear hderivative
  apply exists_enlarged_cone_energy_lt
    (Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5))
    (fun z ↦ Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5) z) hT hu c ?_ henergy hε
  intro t ht x
  have he : semilinearWaveOperator (Real.signedPowerPotential 5) u (timeSpaceCons t x) =
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 := by
    unfold semilinearWaveOperator
    rw [(Real.hasDerivAt_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5) _).deriv]
    unfold Real.signedPower
    rw [show (5 : ℝ) - 1 = (4 : ℕ) by norm_num, Real.rpow_natCast,
      (show Even 4 by decide).pow_abs]
    cas
  rw [he]
  exact hwave t ht x

/-- The defocusing quintic energy controls the sixth power of the local L6 norm. -/
theorem lpNorm_six_pow_le_quintic_ball_energy {u : ℝ^4 → ℝ} {t : ℝ}
    (hu : ∀ x : ℝ^3, ContDiffAt ℝ 2 u (timeSpaceCons t x)) (c : ℝ^3) (R : ℝ) :
    lpNorm (fun x ↦ u (timeSpaceCons t x)) 6 (volume.restrict (Metric.ball c R)) ^ 6 ≤
      6 * ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity (Real.signedPowerPotential 5) u
      (timeSpaceCons t x)) c R := by
  have hs := (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous
  have hU : Continuous (fun x ↦ u (timeSpaceCons t x)) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hu x).continuousAt.comp hs.continuousAt
  have he : Continuous (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential 5) u (timeSpaceCons t x)) :=
    continuous_iff_continuousAt.mpr fun x ↦ (contDiffAt_semilinearWaveEnergyDensity (m := 1)
        (Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)).contDiffAt
        (hu x)).continuousAt.comp hs.continuousAt
  have hint {f : ℝ^3 → ℝ} (hf : Continuous f) : IntegrableOn f (Metric.ball c R) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall c R)).mono_set
      Metric.ball_subset_closedBall
  have hid := integral_norm_pow_eq_lpNorm_pow
    (μ := volume.restrict (Metric.ball c R)) hU.aestronglyMeasurable
    (by norm_num : (0 : ℕ) < 6)
  norm_num only [Nat.cast_ofNat] at hid
  rw [← hid]
  rw [ballIntegral, ← integral_const_mul]
  apply integral_mono (hint (hU.norm.pow 6)) ((hint he).const_mul 6)
  intro x
  have hpos := classicalWaveEnergyDensity_nonneg u (timeSpaceCons t x)
  have hV : Real.signedPowerPotential 5 (u (timeSpaceCons t x)) =
      ‖u (timeSpaceCons t x)‖ ^ 6 / 6 := by
    norm_num [Real.signedPowerPotential, Real.rpow_ofNat, Real.norm_eq_abs]
  unfold semilinearWaveEnergyDensity
  dsimp only [Pi.pow_apply]
  rw [hV]
  linarith

end WaveEquation.Critical
