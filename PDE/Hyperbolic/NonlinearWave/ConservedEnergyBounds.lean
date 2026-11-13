/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Bounds

/-!
# Bounds transported by semilinear wave-energy equality

An equality between the energy at time `t` and a reference time `t₀` transports every
fixed-time component estimate to the reference energy. The equality is a hypothesis,
which may come from `semilinearWaveSpatialEnergy_conserved` or from a more specialized
conservation theorem.

With the conservation of energy of Evans, §12.1.1, Theorem 1, and a nonnegative potential, the
bounds control each component of the energy by the energy at the reference time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace WaveEquation

variable {n : ℕ}

/-- An energy equality transports the normalized kinetic-energy bound to the
reference time. -/
theorem integral_semilinearWaveKineticEnergy_le_referenceEnergy (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀) :
    (∫ x : ℝ^n, semilinearWaveSpatialKineticEnergyDensity (n := n) u t x) ≤
      semilinearWaveSpatialEnergy (n := n) V u t₀ :=
  (integral_semilinearWaveKineticEnergy_le_spatialEnergy
    (n := n) V hVnonneg hu t henergyIntegrable).trans_eq henergy

/-- An energy equality transports the normalized spatial-gradient bound to
the reference time. -/
theorem integral_semilinearWaveGradientEnergy_le_referenceEnergy (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀) :
    (∫ x : ℝ^n, semilinearWaveSpatialGradientEnergyDensity (n := n) u t x) ≤
      semilinearWaveSpatialEnergy (n := n) V u t₀ :=
  (integral_semilinearWaveGradientEnergy_le_spatialEnergy
    (n := n) V hVnonneg hu t henergyIntegrable).trans_eq henergy

/-- An energy equality transports the potential-energy bound to the
reference time. -/
theorem integral_semilinearWavePotentialEnergy_le_referenceEnergy (V : ℝ → ℝ) (hV : Continuous V)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀) :
    (∫ x : ℝ^n, semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t x) ≤
      semilinearWaveSpatialEnergy (n := n) V u t₀ :=
  (integral_semilinearWavePotentialEnergy_le_spatialEnergy
    (n := n) V hV hVnonneg hu t henergyIntegrable).trans_eq henergy

/-- An energy equality transports the sum of normalized kinetic and
spatial-gradient energies to the reference time. -/
theorem integral_semilinearWaveDerivativeEnergy_le_referenceEnergy (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀) :
    (∫ x : ℝ^n, semilinearWaveSpatialKineticEnergyDensity (n := n) u t x +
      semilinearWaveSpatialGradientEnergyDensity (n := n) u t x) ≤
      semilinearWaveSpatialEnergy (n := n) V u t₀ :=
  (integral_semilinearWaveDerivativeEnergy_le_spatialEnergy
    (n := n) V hVnonneg hu t henergyIntegrable).trans_eq henergy

/-- An energy equality transports the unnormalized squared time-derivative
bound to twice the reference energy. -/
theorem integral_semilinearWaveTimeDerivativeSq_le_two_mul_referenceEnergy (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀) :
    (∫ x : ℝ^n, ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) ≤
      2 * semilinearWaveSpatialEnergy (n := n) V u t₀ := by
  calc
    (∫ x : ℝ^n, ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) ≤
        2 * semilinearWaveSpatialEnergy (n := n) V u t :=
      integral_semilinearWaveTimeDerivativeSq_le_two_mul_spatialEnergy
        (n := n) V hVnonneg hu t henergyIntegrable
    _ = 2 * semilinearWaveSpatialEnergy (n := n) V u t₀ := by rw [henergy]

/-- An energy equality transports the unnormalized squared spatial-gradient
bound to twice the reference energy. -/
theorem integral_semilinearWaveGradientSq_le_two_mul_referenceEnergy (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀) :
    (∫ x : ℝ^n, ‖classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x)‖ ^
      2) ≤ 2 * semilinearWaveSpatialEnergy (n := n) V u t₀ := by
  calc
    (∫ x : ℝ^n, ‖classicalWaveSpatialGradient (n := n) u
          (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2) ≤
        2 * semilinearWaveSpatialEnergy (n := n) V u t :=
      integral_semilinearWaveGradientSq_le_two_mul_spatialEnergy
        (n := n) V hVnonneg hu t henergyIntegrable
    _ = 2 * semilinearWaveSpatialEnergy (n := n) V u t₀ := by rw [henergy]

end WaveEquation
