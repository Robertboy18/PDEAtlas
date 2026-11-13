/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Scalar.OddPower
public import PDE.Hyperbolic.NonlinearWave.DominatedData
import PDE.Hyperbolic.NonlinearWave.DefocusingPower.Conservation
import PDE.Hyperbolic.NonlinearWave.DefocusingPower.Equation
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.Lifespan

/-!
# Finite lifespan for negative-energy odd-power waves

We specialize the negative-energy concavity method to

`uₜₜ - Δu + massSq * u + coupling * u^(2 * k + 1) = 0`.

For `massSq ≥ 0` and `k > 0`, the canonical potential obeys the growth
inequality with exponent `2 * (k + 1)`. Consequently, the Riccati coefficient
in the lifespan estimate simplifies to `k / 2`.

The virial and energy data structures supply the analytic assumptions for
differentiating the spatial integrals and proving energy conservation.
The common-neighborhood regularity assumption is local along the time slab;
half-open lifespans require no extension through their excluded endpoint.

The argument is Levine's concavity method, as in the proof of Evans, §12.5.1, Theorem 1. With
`I(t) = ½ ∫ u²` and `P = I'`, negative energy and the growth condition with `Λ = 2 (k + 1)` give
`I I'' ≥ (1 + k / 2) (I')²`, so `I^{-k/2}` is concave; if `P(t₀) > 0` this concave function is
decreasing at `t₀` and reaches zero no later than the Riccati horizon displayed in the statements,
so a solution with the stated regularity cannot exist on a slab reaching that time. We prove the
forward and backward, closed and half-open, forms of that horizon; the `shifted` variants start from
nonnegative momentum by first advancing a positive time `δ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, Theorem 1 and its proof, equations (2)-(7).
  <https://doi.org/10.1090/gsm/019>
* H. A. Levine, *Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `Pu_tt = -Au + F(u)`*, Trans. Amer. Math. Soc. 192 (1974), 1-21, Theorem I and its
  proof, equations (II-2)-(II-4), pp. 4-6.
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
* L. E. Payne and D. H. Sattinger, *Saddle points and instability of nonlinear hyperbolic
  equations*, Israel J. Math. 22 (1975), 273-303.
  <https://doi.org/10.1007/BF02761595>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Scalar
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- The growth exponent `2 (k + 1)` of a nonlinear odd power exceeds `2`. -/
private theorem two_lt_oddPower_growth_factor {k : ℕ} (hk : 0 < k) :
    2 < 2 * (k + 1 : ℝ) := by
  have : 0 < (k : ℝ) := by exact_mod_cast hk
  linarith

/-- The Riccati coefficient `(Λ - 2) / 4` for `Λ = 2 (k + 1)`. -/
private theorem oddPower_riccati_coefficient (k : ℕ) :
    (2 * (k + 1 : ℝ) - 2) / 4 = (k : ℝ) / 2 := by
  ring

/-- On an order-connected slab containing `t₀`, the odd-power equation is the semilinear
equation for `oddPowerPotential`, and it conserves the corresponding energy. -/
private theorem oddPower_inputs {massSq coupling : ℝ} {k : ℕ} {u : ℝ^(n + 1) → ℝ} {times : Set ℝ}
    {t₀ : ℝ} (htimes : times.OrdConnected) (ht₀ : t₀ ∈ times)
    (hu : ∀ t ∈ times, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ times, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u times) :
    (∀ t ∈ times, ∀ x : ℝ^n, semilinearWaveOperator (oddPowerPotential massSq coupling k) u
      (PDE.Common.timeSpaceCons t x) = 0) ∧ ∀ t ∈ times, semilinearWaveSpatialEnergy
      (oddPowerPotential massSq coupling k) u t = semilinearWaveSpatialEnergy
      (oddPowerPotential massSq coupling k) u t₀ :=
  ⟨fun t ht x ↦ by simpa only [semilinearWaveOperator_oddPowerPotential] using hwave t ht x,
    fun t ht ↦ oddPowerSpatialEnergy_eq_of_wave_on_ordConnected massSq coupling k htimes ht ht₀ hu
      hwave hE.energy_integrable hE.mem_nhds hE.dominated hE.bound_integrable
      hE.flux_compact_support⟩

/-- A negative-energy odd-power wave with positive initial quadratic momentum
on the closed slab `[t₀, T]` must end strictly before the explicit Riccati
horizon

`t₀ + (((k / 2) * P(t₀) / I(t₀))⁻¹)`.

Here `I` is the spatial quadratic mass and `P = I'` is the spatial quadratic
momentum. -/
theorem right_endpoint_lt_riccati_horizon_of_oddPower_negative_energy {massSq coupling : ℝ} {k : ℕ}
    {u : ℝ^(n + 1) → ℝ} {t₀ T : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (htime : t₀ ≤ T)
    (hu : ∀ t ∈ Icc t₀ T, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ Icc t₀ T, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Icc t₀ T))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Icc t₀ T))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0)
    (hmomentumPos : 0 < waveSpatialQuadraticMomentum (n := n) u t₀) :
    T < t₀ + (((k : ℝ) / 2) * (waveSpatialQuadraticMomentum (n := n) u t₀ /
      waveSpatialQuadraticMass (n := n) u t₀))⁻¹ := by
  obtain ⟨hwave', henergy⟩ := oddPower_inputs ordConnected_Icc ⟨le_rfl, by linarith⟩ hu hwave hE
  simpa only [oddPower_riccati_coefficient] using
    right_endpoint_lt_riccati_horizon_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
      (oddPowerPotential_zero massSq coupling k)
      ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
      (two_lt_oddPower_growth_factor hk) htime (mul_deriv_oddPowerPotential_le coupling k hmassSq)
      hwave' hD henergy henergyNeg hmomentumPos

/-- A negative-energy odd-power wave with positive initial quadratic momentum
cannot have a half-open lifespan extending beyond the explicit Riccati
horizon

`t₀ + (((k / 2) * P(t₀) / I(t₀))⁻¹)`.

Here `I` is the spatial quadratic mass and `P = I'` is the spatial quadratic
momentum. -/
theorem right_endpoint_le_riccati_horizon_of_oddPower_negative_energy {massSq coupling : ℝ} {k : ℕ}
    {u : ℝ^(n + 1) → ℝ} {t₀ T : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (htime : t₀ < T)
    (hu : ∀ t ∈ Ico t₀ T, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ Ico t₀ T, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Ico t₀ T))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Ico t₀ T))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0)
    (hmomentumPos : 0 < waveSpatialQuadraticMomentum (n := n) u t₀) :
    T ≤ t₀ + (((k : ℝ) / 2) * (waveSpatialQuadraticMomentum (n := n) u t₀ /
      waveSpatialQuadraticMass (n := n) u t₀))⁻¹ := by
  obtain ⟨hwave', henergy⟩ := oddPower_inputs ordConnected_Ico ⟨le_rfl, by linarith⟩ hu hwave hE
  simpa only [oddPower_riccati_coefficient] using
    right_endpoint_le_riccati_horizon_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
      (oddPowerPotential_zero massSq coupling k)
      ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
      (two_lt_oddPower_growth_factor hk) htime (mul_deriv_oddPowerPotential_le coupling k hmassSq)
      hwave' hD henergy henergyNeg hmomentumPos

/-- A negative-energy odd-power wave with nonnegative initial quadratic
momentum on `[t₀, T]` satisfies the shifted strict lifespan estimate

`T < t₀ + δ + (((k / 2) * P(t₀ + δ) / I(t₀ + δ))⁻¹)`

whenever `δ > 0` and `t₀ + δ ≤ T`. Positive forcing makes the momentum
strictly positive at the shifted time, so this includes time-symmetric initial
data. -/
theorem right_endpoint_lt_shifted_riccati_horizon_of_oddPower_negative_energy {massSq coupling : ℝ}
    {k : ℕ} {u : ℝ^(n + 1) → ℝ} {t₀ T δ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (hδ : 0 < δ)
    (hshift : t₀ + δ ≤ T)
    (hu : ∀ t ∈ Icc t₀ T, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ Icc t₀ T, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Icc t₀ T))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Icc t₀ T))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0)
    (hmomentumNonneg : 0 ≤ waveSpatialQuadraticMomentum (n := n) u t₀) :
    T < t₀ + δ + (((k : ℝ) / 2) * (waveSpatialQuadraticMomentum (n := n) u (t₀ + δ) /
      waveSpatialQuadraticMass (n := n) u (t₀ + δ)))⁻¹ := by
  obtain ⟨hwave', henergy⟩ := oddPower_inputs ordConnected_Icc ⟨le_rfl, by linarith⟩ hu hwave hE
  simpa only [oddPower_riccati_coefficient] using
    right_endpoint_lt_shifted_riccati_horizon_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
      (oddPowerPotential_zero massSq coupling k)
      ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
      (two_lt_oddPower_growth_factor hk) hδ hshift
      (mul_deriv_oddPowerPotential_le coupling k hmassSq) hwave' hD henergy henergyNeg
      hmomentumNonneg

/-- A negative-energy odd-power wave with nonnegative initial quadratic
momentum satisfies the shifted half-open lifespan estimate

`T ≤ t₀ + δ + (((k / 2) * P(t₀ + δ) / I(t₀ + δ))⁻¹)`

whenever `δ > 0` and `t₀ + δ < T`. This includes time-symmetric initial data
with zero initial momentum. -/
theorem right_endpoint_le_shifted_riccati_horizon_of_oddPower_negative_energy {massSq coupling : ℝ}
    {k : ℕ} {u : ℝ^(n + 1) → ℝ} {t₀ T δ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (hδ : 0 < δ)
    (hshift : t₀ + δ < T)
    (hu : ∀ t ∈ Ico t₀ T, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ Ico t₀ T, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Ico t₀ T))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Ico t₀ T))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0)
    (hmomentumNonneg : 0 ≤ waveSpatialQuadraticMomentum (n := n) u t₀) :
    T ≤ t₀ + δ + (((k : ℝ) / 2) * (waveSpatialQuadraticMomentum (n := n) u (t₀ + δ) /
      waveSpatialQuadraticMass (n := n) u (t₀ + δ)))⁻¹ := by
  obtain ⟨hwave', henergy⟩ := oddPower_inputs ordConnected_Ico ⟨le_rfl, by linarith⟩ hu hwave hE
  simpa only [oddPower_riccati_coefficient] using
    right_endpoint_le_shifted_riccati_horizon_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
      (oddPowerPotential_zero massSq coupling k)
      ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
      (two_lt_oddPower_growth_factor hk) hδ hshift
      (mul_deriv_oddPowerPotential_le coupling k hmassSq) hwave' hD henergy henergyNeg
      hmomentumNonneg

/-- A negative-energy odd-power wave with negative quadratic momentum at
`t₀` cannot extend backward to a closed endpoint at or before

`t₀ - (((k / 2) * (-P(t₀) / I(t₀)))⁻¹)`.

Here `I` is the spatial quadratic mass and `P = I'` is the spatial quadratic
momentum. -/
theorem riccati_horizon_lt_left_endpoint_of_oddPower_negative_energy {massSq coupling : ℝ} {k : ℕ}
    {u : ℝ^(n + 1) → ℝ} {T t₀ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (htime : T ≤ t₀)
    (hu : ∀ t ∈ Icc T t₀, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ Icc T t₀, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Icc T t₀))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Icc T t₀))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0)
    (hmomentumNeg : waveSpatialQuadraticMomentum (n := n) u t₀ < 0) :
    t₀ - (((k : ℝ) / 2) * (-waveSpatialQuadraticMomentum (n := n) u t₀ /
      waveSpatialQuadraticMass (n := n) u t₀))⁻¹ < T := by
  obtain ⟨hwave', henergy⟩ := oddPower_inputs ordConnected_Icc ⟨by linarith, le_rfl⟩ hu hwave hE
  simpa only [oddPower_riccati_coefficient] using
    riccati_horizon_lt_left_endpoint_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
      (oddPowerPotential_zero massSq coupling k)
      ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
      (two_lt_oddPower_growth_factor hk) htime (mul_deriv_oddPowerPotential_le coupling k hmassSq)
      hwave' hD henergy henergyNeg hmomentumNeg

/-- A negative-energy odd-power wave on a half-open past time slab `(T, t₀]`
with negative quadratic momentum at `t₀` satisfies

`t₀ - (((k / 2) * (-P(t₀) / I(t₀)))⁻¹) ≤ T`.
-/
theorem riccati_horizon_le_left_endpoint_of_oddPower_negative_energy {massSq coupling : ℝ} {k : ℕ}
    {u : ℝ^(n + 1) → ℝ} {T t₀ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (htime : T < t₀)
    (hu : ∀ t ∈ Ioc T t₀, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ Ioc T t₀, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Ioc T t₀))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Ioc T t₀))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0)
    (hmomentumNeg : waveSpatialQuadraticMomentum (n := n) u t₀ < 0) :
    t₀ - (((k : ℝ) / 2) * (-waveSpatialQuadraticMomentum (n := n) u t₀ /
      waveSpatialQuadraticMass (n := n) u t₀))⁻¹ ≤ T := by
  obtain ⟨hwave', henergy⟩ := oddPower_inputs ordConnected_Ioc ⟨by linarith, le_rfl⟩ hu hwave hE
  simpa only [oddPower_riccati_coefficient] using
    riccati_horizon_le_left_endpoint_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
      (oddPowerPotential_zero massSq coupling k)
      ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
      (two_lt_oddPower_growth_factor hk) htime (mul_deriv_oddPowerPotential_le coupling k hmassSq)
      hwave' hD henergy henergyNeg hmomentumNeg

/-- A negative-energy odd-power wave with nonpositive quadratic momentum at
`t₀` satisfies the shifted strict backward lifespan estimate

`t₀ - δ - (((k / 2) * (-P(t₀ - δ) / I(t₀ - δ)))⁻¹) < T`

whenever `δ > 0` and `T ≤ t₀ - δ`. Negative conserved energy forces the
quadratic momentum to be strictly negative at the shifted time. -/
theorem shifted_riccati_horizon_lt_left_endpoint_of_oddPower_negative_energy {massSq coupling : ℝ}
    {k : ℕ} {u : ℝ^(n + 1) → ℝ} {T t₀ δ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (hδ : 0 < δ)
    (hshift : T ≤ t₀ - δ)
    (hu : ∀ t ∈ Icc T t₀, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ Icc T t₀, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Icc T t₀))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Icc T t₀))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0)
    (hmomentumNonpos : waveSpatialQuadraticMomentum (n := n) u t₀ ≤ 0) :
    t₀ - δ - (((k : ℝ) / 2) * (-waveSpatialQuadraticMomentum (n := n) u (t₀ - δ) /
      waveSpatialQuadraticMass (n := n) u (t₀ - δ)))⁻¹ < T := by
  obtain ⟨hwave', henergy⟩ := oddPower_inputs ordConnected_Icc ⟨by linarith, le_rfl⟩ hu hwave hE
  simpa only [oddPower_riccati_coefficient] using
    shifted_riccati_horizon_lt_left_endpoint_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
      (oddPowerPotential_zero massSq coupling k)
      ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
      (two_lt_oddPower_growth_factor hk) hδ hshift
      (mul_deriv_oddPowerPotential_le coupling k hmassSq) hwave' hD henergy henergyNeg
      hmomentumNonpos

/-- A negative-energy odd-power wave on a half-open past time slab `(T, t₀]`
with nonpositive quadratic momentum at `t₀` satisfies

`t₀ - δ - (((k / 2) * (-P(t₀ - δ) / I(t₀ - δ)))⁻¹) ≤ T`

for every `δ > 0` with `T < t₀ - δ`. This includes time-symmetric initial
data with zero quadratic momentum. -/
theorem shifted_riccati_horizon_le_left_endpoint_of_oddPower_negative_energy {massSq coupling : ℝ}
    {k : ℕ} {u : ℝ^(n + 1) → ℝ} {T t₀ δ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (hδ : 0 < δ)
    (hshift : T < t₀ - δ)
    (hu : ∀ t ∈ Ioc T t₀, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ Ioc T t₀, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Ioc T t₀))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Ioc T t₀))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0)
    (hmomentumNonpos : waveSpatialQuadraticMomentum (n := n) u t₀ ≤ 0) :
    t₀ - δ - (((k : ℝ) / 2) * (-waveSpatialQuadraticMomentum (n := n) u (t₀ - δ) /
      waveSpatialQuadraticMass (n := n) u (t₀ - δ)))⁻¹ ≤ T := by
  obtain ⟨hwave', henergy⟩ := oddPower_inputs ordConnected_Ioc ⟨by linarith, le_rfl⟩ hu hwave hE
  simpa only [oddPower_riccati_coefficient] using
    shifted_riccati_horizon_le_left_endpoint_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
      (oddPowerPotential_zero massSq coupling k)
      ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
      (two_lt_oddPower_growth_factor hk) hδ hshift
      (mul_deriv_oddPowerPotential_le coupling k hmassSq) hwave' hD henergy henergyNeg
      hmomentumNonpos

end WaveEquation
