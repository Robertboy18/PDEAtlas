/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Scalar.OddPower
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Differentiation
import PDE.Hyperbolic.NonlinearWave.DefocusingPower.CoerciveBounds
import PDE.Hyperbolic.NonlinearWave.DefocusingPower.Conservation

/-!
# Rigidity for defocusing odd-power waves

We combine conservation of the odd-power spatial energy with its
coercive zero-energy rigidity. The first theorem applies on an arbitrary
order-connected lifespan, while the second gives the global spacetime
conclusion.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Scalar
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- A defocusing odd-power wave with zero energy at one time vanishes on every
spatial slice in the same order-connected lifespan.

The analytic assumptions are precisely those used to differentiate the
spatial energy and discard the flux at spatial infinity. -/
theorem defocusingPowerField_eq_zero_on_ordConnected_of_spatialEnergy_eq_zero (massSq coupling : ℝ)
    (k : ℕ) (hmassSq : 0 ≤ massSq) (hcoupling : 0 ≤ coupling)
    (hpositive : 0 < massSq ∨ 0 < coupling) {u : ℝ^(n + 1) → ℝ} {times : Set ℝ} {t₀ : ℝ}
    {s : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ} (htimes : times.OrdConnected) (ht₀ : t₀ ∈ times)
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
      i t))
    (hreferenceEnergy : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ = 0) :
    ∀ t ∈ times, ∀ x : ℝ^n, u (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  intro t ht x
  have henergyEq : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t =
        semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ :=
    oddPowerSpatialEnergy_eq_of_wave_on_ordConnected
      massSq coupling k htimes ht ht₀ hu hwave henergyIntegrable hs
        hdominated hboundIntegrable hfluxCompact
  let density : ℝ^n → ℝ := semilinearWaveSpatialEnergyDensity (n := n)
    (oddPowerPotential massSq coupling k) u t
  have hdensityContinuous : Continuous density := (contDiff_semilinearWaveSpatialEnergyDensity
      ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp))
      (hu t ht).self_of_nhds).continuous
  have hdensityNonneg : ∀ y, 0 ≤ density y := fun y ↦
    semilinearWaveEnergyDensity_nonneg _ (oddPowerPotential_nonneg k hmassSq hcoupling)
      u (PDE.Common.timeSpaceCons (n := n) t y)
  have hdensityIntegral : ∫ y, density y = 0 := henergyEq.trans hreferenceEnergy
  have hdensityAE : density =ᵐ[(volume : Measure (ℝ^n))] 0 :=
    (integral_eq_zero_iff_of_nonneg hdensityNonneg (henergyIntegrable t ht)).mp hdensityIntegral
  have hdensityZero : density = 0 :=
    (hdensityContinuous.ae_eq_iff_eq (volume : Measure (ℝ^n)) continuous_const).mp hdensityAE
  have hx : density x = 0 := congrFun hdensityZero x
  have hpotentialNonneg := oddPowerPotential_nonneg k hmassSq hcoupling
    (u (PDE.Common.timeSpaceCons (n := n) t x))
  have hclassicalNonneg := classicalWaveEnergyDensity_nonneg u
    (PDE.Common.timeSpaceCons (n := n) t x)
  apply (oddPowerPotential_eq_zero_iff k hmassSq hcoupling hpositive _).mp
  change classicalWaveEnergyDensity u (PDE.Common.timeSpaceCons (n := n) t x) +
    oddPowerPotential massSq coupling k (u (PDE.Common.timeSpaceCons (n := n) t x)) = 0 at hx
  linarith

/-- A global defocusing odd-power wave with zero energy at one time vanishes
identically when at least one defocusing coefficient is positive. -/
theorem eq_zero_of_defocusingPowerWave_of_spatialEnergy_eq_zero (massSq coupling : ℝ) (k : ℕ)
    (hmassSq : 0 ≤ massSq) (hcoupling : 0 ≤ coupling) (hpositive : 0 < massSq ∨ 0 < coupling)
    {u : ℝ^(n + 1) → ℝ} {s : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ} (hu : ContDiff ℝ 2 u)
    (hwave : ∀ p, waveOperator (n := n) u p + massSq * u p + coupling * (u p) ^ (2 * k + 1) = 0)
    (henergyIntegrable : ∀ t, Integrable (semilinearWaveSpatialEnergyDensity (n := n)
      (oddPowerPotential massSq coupling k) u t))
    (hs : ∀ t, s t ∈ 𝓝 t)
    (hdominated : ∀ t, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) (oddPowerPotential massSq coupling k) u r
      x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t, Integrable (bound t))
    (hfluxCompact : ∀ t i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t))
    (t₀ : ℝ)
    (hreferenceEnergy : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ = 0) :
    u = 0 := by
  apply eq_zero_of_defocusingPowerEnergy_eq_zero
    k hmassSq hcoupling hpositive hu.continuous t₀ henergyIntegrable
  · exact fun t ↦ oddPowerSpatialEnergy_conserved
      massSq coupling k hu hwave henergyIntegrable hs hdominated hboundIntegrable hfluxCompact t t₀
  · exact hreferenceEnergy

end WaveEquation
