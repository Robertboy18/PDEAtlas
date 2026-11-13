/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Scalar.OddPower
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Differentiation
import PDE.Hyperbolic.NonlinearWave.DefocusingPower.Equation
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Conservation

/-!
# Energy conservation for defocusing power waves

We specialize the semilinear conservation theorem to the polynomial
potential

`V(z) = massSq / 2 * z² + coupling / (2 * (k + 1)) * z^(2 * (k + 1))`.

The local results cover unordered intervals and arbitrary order-connected time
sets. Conservation holds for coefficients of either sign; sign assumptions enter only the coercive
estimates in `DefocusingPower.CoerciveBounds`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Scalar
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Odd-power wave energy agrees at two times when the equation and the
analytic hypotheses for differentiating the energy hold on the unordered
interval between them. -/
theorem oddPowerSpatialEnergy_eq_of_wave_on_uIcc (massSq coupling : ℝ) (k : ℕ) {u : ℝ^(n + 1) → ℝ}
    {t₀ t₁ : ℝ} {s : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ}
    (hu : ∀ t ∈ uIcc t₀ t₁, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ uIcc t₀ t₁, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (henergyIntegrable : ∀ t ∈ uIcc t₀ t₁, Integrable (semilinearWaveSpatialEnergyDensity (n := n)
      (oddPowerPotential massSq coupling k) u t))
    (hs : ∀ t ∈ uIcc t₀ t₁, s t ∈ 𝓝 t)
    (hdominated : ∀ t ∈ uIcc t₀ t₁, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) (oddPowerPotential massSq coupling k) u r
      x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t ∈ uIcc t₀ t₁, Integrable (bound t))
    (hfluxCompact : ∀ t ∈ uIcc t₀ t₁, ∀ i, HasCompactSupport
      (semilinearWaveSpatialEnergyFlux (n := n) u i t)) :
    semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ =
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₁ := by
  apply semilinearWaveSpatialEnergy_eq_of_wave_on_uIcc
    ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
  · intro t ht x
    simpa only [semilinearWaveOperator_oddPowerPotential] using hwave t ht x
  · exact henergyIntegrable
  · exact hs
  · exact hdominated
  · exact hboundIntegrable
  · exact hfluxCompact

/-- Odd-power wave energy agrees at any two times in an order-connected set
on which the equation and analytic differentiation hypotheses hold.

This includes closed and half-open lifespan intervals in either time
direction. -/
theorem oddPowerSpatialEnergy_eq_of_wave_on_ordConnected (massSq coupling : ℝ) (k : ℕ)
    {u : ℝ^(n + 1) → ℝ} {times : Set ℝ} {t₀ t₁ : ℝ} {s : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ}
    (htimes : times.OrdConnected) (ht₀ : t₀ ∈ times) (ht₁ : t₁ ∈ times)
    (hu : ∀ t ∈ times, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ times, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (henergyIntegrable : ∀ t ∈ times, Integrable (semilinearWaveSpatialEnergyDensity (n := n)
      (oddPowerPotential massSq coupling k) u t))
    (hs : ∀ t ∈ times, s t ∈ 𝓝 t)
    (hdominated : ∀ t ∈ times, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) (oddPowerPotential massSq coupling k) u r
      x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t ∈ times, Integrable (bound t))
    (hfluxCompact : ∀ t ∈ times, ∀ i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u
      i t)) :
    semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ =
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₁ := by
  apply semilinearWaveSpatialEnergy_eq_of_wave_on_ordConnected htimes ht₀ ht₁
    ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
  · intro t ht x
    simpa only [semilinearWaveOperator_oddPowerPotential] using hwave t ht x
  · exact henergyIntegrable
  · exact hs
  · exact hdominated
  · exact hboundIntegrable
  · exact hfluxCompact

/-- Global energy conservation for the concrete odd-power wave equation. -/
theorem oddPowerSpatialEnergy_conserved (massSq coupling : ℝ) (k : ℕ) {u : ℝ^(n + 1) → ℝ}
    {s : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ} (hu : ContDiff ℝ 2 u)
    (hwave : ∀ p, waveOperator (n := n) u p + massSq * u p + coupling * (u p) ^ (2 * k + 1) = 0)
    (henergyIntegrable : ∀ t, Integrable (semilinearWaveSpatialEnergyDensity (n := n)
      (oddPowerPotential massSq coupling k) u t))
    (hs : ∀ t, s t ∈ 𝓝 t)
    (hdominated : ∀ t, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) (oddPowerPotential massSq coupling k) u r
      x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t, Integrable (bound t))
    (hfluxCompact : ∀ t i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t))
    (t₀ t₁ : ℝ) :
    semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ =
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₁ := by
  apply semilinearWaveSpatialEnergy_conserved (n := n)
    ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
  · intro p
    simpa only [semilinearWaveOperator_oddPowerPotential] using hwave p
  · exact henergyIntegrable
  · exact hs
  · exact hdominated
  · exact hboundIntegrable
  · exact hfluxCompact

end WaveEquation
