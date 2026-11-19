/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.TruncatedEnergy
public import PDE.Hyperbolic.NonlinearWave.Morawetz.QuinticCap
import CAS.ExactTactic

/-!
# Local energy control for the quintic wave before a cone vertex

The equation on the forward open time band makes shrinking-ball energy
decrease. Energy at any fixed positive starting time bounds all later slices
and supplies the hypothesis of the terminal Morawetz cap estimate.

Step 3 of the proof of Evans, §12.4, Theorem 3, uses that the local energy `e(t)` is
nonincreasing, which follows from the formula (4) for its derivative in the proof of §12.1.2,
Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, proof of Theorem 2, equation (4); §12.4, Theorem 3,
  step 3 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Common PDE.Analysis Set
open scoped Topology

namespace WaveEquation

private theorem semilinearWaveOperator_quintic {u : ℝ^(3 + 1) → ℝ} (p : ℝ^(3 + 1)) :
    semilinearWaveOperator (Real.signedPowerPotential 5) u p = waveOperator u p + u p ^ 5 := by
  unfold semilinearWaveOperator
  rw [(Real.hasDerivAt_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5) _).deriv]
  unfold Real.signedPower
  rw [show (5 : ℝ) - 1 = (4 : ℕ) by norm_num, Real.rpow_natCast,
    (show Even 4 by decide).pow_abs]
  cas

/-- Quintic wave energy decreases on shrinking balls throughout `0 < t < T`. -/
theorem quintic_ballIntegral_energy_antitoneOn {u : ℝ^(3 + 1) → ℝ} {T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    AntitoneOn (fun t ↦ ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential 5) u (timeSpaceCons t x)) c (T - t)) (Ioo 0 T) := by
  apply ballIntegral_energy_antitoneOn
    (Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5))
    (fun z ↦ Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5) z) hu c
  intro t ht x hx
  rw [semilinearWaveOperator_quintic]
  exact hwave t ht x hx

/-- Energy at a fixed interior starting time bounds every sufficiently late shrinking ball.
This is the local-energy hypothesis needed by the terminal cap theorem. -/
theorem eventually_quintic_ballIntegral_energy_le {u : ℝ^(3 + 1) → ℝ} {s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    ∀ᶠ t in 𝓝[<] T, ballIntegral 3
      (fun x ↦ semilinearWaveEnergyDensity (Real.signedPowerPotential 5) u
        (timeSpaceCons t x)) c (T - t) ≤
      ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity (Real.signedPowerPotential 5) u
        (timeSpaceCons s x)) c (T - s) := by
  have hlate : ∀ᶠ t in 𝓝[<] T, s < t := (eventually_gt_nhds hsT).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlate, self_mem_nhdsWithin] with t hst ht
  exact quintic_ballIntegral_energy_antitoneOn hu c hwave ⟨hs, hsT⟩ ⟨hs.trans hst, ht⟩ hst.le

/-- The forward quintic equation removes the terminal scaling-current cap.
Local energy conservation supplies all norm and energy bounds required by the cap estimate. -/
theorem tendsto_quintic_ballIntegral_scalingCurrentDensity_zero_of_wave {u : ℝ^(3 + 1) → ℝ}
    {s T : ℝ} (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    Tendsto (fun t ↦ ballIntegral 3 (fun x ↦ scalingCurrentDensity (Real.signedPowerPotential 5) 1
      (timeSpaceCons T c) u (timeSpaceCons t x)) c (T - t)) (𝓝[<] T) (𝓝 0) := by
  apply tendsto_quintic_ballIntegral_scalingCurrentDensity_zero c T
    (ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity (Real.signedPowerPotential 5) u
      (timeSpaceCons s x)) c (T - s))
  · have hopen : IsOpen {p : ℝ^(3 + 1) | 0 < p 0 ∧ p 0 < T} :=
      (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
        (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
    have hpos : ∀ᶠ t in 𝓝[<] T, 0 < t :=
      (eventually_gt_nhds (hs.trans hsT)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, self_mem_nhdsWithin] with t ht htT x using hu.contDiffAt (hopen.mem_nhds
      (by simpa only [mem_ofPred_eq, timeSpaceCons_zero, mem_Iio] using And.intro ht htT))
  · exact eventually_quintic_ballIntegral_energy_le hu c hs hsT hwave

end WaveEquation
