/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Scalar.OddPower
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.NonlinearWave.CoercivePotential
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Bounds
import CAS.ExactTactic

/-!
# Coercive bounds for defocusing power waves

For nonnegative coefficients, the canonical odd-power potential controls the quadratic
mass term and the higher even power appearing in the energy. We derive their fixed-time
integrability and integral bounds, transport those estimates across an energy equality,
and prove zero-energy rigidity.

The results are stated for fields and spatial energies.

The equation is `u_tt - Δu + massSq·u + coupling·u^(2k+1) = 0`, with energy
density `½ u_t² + ½ |∇u|² + ½ massSq·u² + coupling/(2k+2)·u^(2k+2)`; this is
the energy of Evans, §12.1.1, for a power nonlinearity with the defocusing sign; with
`massSq = 0`, `coupling = 1` and `p = 2k + 1` it is the energy of (18) in §12.3.3.
When `massSq, coupling ≥ 0`, every term is nonnegative.
A strictly positive `massSq` gives the stated `L²` bound, and a strictly positive
`coupling` gives the `L^{2k+2}` bound. In each case, the other coefficient may be zero.

## Main results

* `integral_defocusingPowerEnergy_eq_two_mul_spatialEnergy`: the unnormalized
  energy integrand is twice the energy density, pointwise and integrated.
* `integral_defocusingPowerFieldSq_le_spatialEnergy_div`,
  `integral_defocusingPowerFieldPow_le_spatialEnergy_div`: the `L²` and
  `L^{2k+2}` bounds by the energy, each needing only its own coefficient to be
  positive.
* `eq_zero_of_defocusingPowerEnergy_eq_zero`: with one positive coefficient,
  zero energy at every time forces `u = 0` on all of spacetime.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1; §12.3.3, equation (18) and its energy.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Scalar
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- The kinetic, gradient, mass, and higher-power terms are twice the
normalized defocusing energy density at each point of a spatial slice. -/
theorem defocusingPowerEnergyDensity_eq_two_mul_spatialEnergyDensity (massSq coupling : ℝ) (k : ℕ)
    (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
      ‖classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2 +
      massSq * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 + coupling / (k + 1 : ℝ) *
      (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * (k + 1)) = 2 *
      semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t x := by
  simp only [semilinearWaveSpatialEnergyDensity,
    semilinearWaveEnergyDensity, classicalWaveEnergyDensity,
    oddPowerPotential]
  cas

/-- Twice the spatial energy is exactly the integral of the kinetic,
gradient, mass, and higher-power terms.

No integrability hypothesis is needed: the two integrands agree pointwise,
and scalar multiplication commutes with the totalized Bochner integral. -/
theorem integral_defocusingPowerEnergy_eq_two_mul_spatialEnergy (massSq coupling : ℝ) (k : ℕ)
    (u : ℝ^(n + 1) → ℝ) (t : ℝ) :
    (∫ x : ℝ^n, ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
      ‖classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2 +
      massSq * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 + coupling / (k + 1 : ℝ) *
      (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * (k + 1))) = 2 *
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t := by
  rw [semilinearWaveSpatialEnergy, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun x ↦
    defocusingPowerEnergyDensity_eq_two_mul_spatialEnergyDensity massSq coupling k u t x)

/-- A positive mass coefficient makes the squared field integrable whenever
the total defocusing energy density is integrable. -/
theorem integrable_defocusingPowerFieldSq {massSq coupling : ℝ} (k : ℕ) (hmassSq : 0 < massSq)
    (hcoupling : 0 ≤ coupling) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t : ℝ)
    (henergyIntegrable :
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t)) :
    Integrable fun x : ℝ^n ↦ (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 :=
  integrable_semilinearWaveFieldSq_of_coercive (oddPowerPotential massSq coupling k) (massSq / 2)
    (by positivity) (oddPowerPotential_quadratic_le k hcoupling) hu t henergyIntegrable

/-- A positive coupling makes the controlled even power of the field
integrable whenever the total defocusing energy density is integrable. -/
theorem integrable_defocusingPowerFieldPow {massSq coupling : ℝ} (k : ℕ) (hmassSq : 0 ≤ massSq)
    (hcoupling : 0 < coupling) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t : ℝ)
    (henergyIntegrable :
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t)) :
    Integrable fun x : ℝ^n ↦ (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * (k + 1)) := by
  have hc : 0 < coupling / (2 * (k + 1) : ℝ) := by positivity
  have h : Integrable (semilinearWaveSpatialPotentialEnergyDensity
      (fun z : ℝ ↦ coupling / (2 * (k + 1) : ℝ) * z ^ (2 * (k + 1))) u t) :=
    integrable_semilinearWaveSpatialPotentialEnergyDensity_of_le
      (continuous_const.mul (continuous_id.pow _))
      (fun z ↦ mul_nonneg hc.le ((even_two_mul (k + 1)).pow_nonneg z))
      (oddPowerPotential_power_le k hmassSq) hu t henergyIntegrable
  simpa only [semilinearWaveSpatialPotentialEnergyDensity, ← mul_assoc, inv_mul_cancel₀ hc.ne',
    one_mul] using h.const_mul (coupling / (2 * (k + 1) : ℝ))⁻¹

/-- A positive mass coefficient controls the spatial integral of the
squared field on a fixed time slice. -/
theorem integral_defocusingPowerFieldSq_le_spatialEnergy_div {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 < massSq) (hcoupling : 0 ≤ coupling) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u)
    (t : ℝ)
    (henergyIntegrable :
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t)) :
    (∫ x : ℝ^n, (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) ≤
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t /
      (massSq / 2) :=
  integral_semilinearWaveFieldSq_le_spatialEnergy_div (oddPowerPotential massSq coupling k)
    (massSq / 2) (by positivity) (oddPowerPotential_quadratic_le k hcoupling) hu t henergyIntegrable

/-- A positive coupling controls the spatial integral of the nonlinear
even power on a fixed time slice. -/
theorem integral_defocusingPowerFieldPow_le_spatialEnergy_div {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 ≤ massSq) (hcoupling : 0 < coupling) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u)
    (t : ℝ)
    (henergyIntegrable :
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t)) :
    (∫ x : ℝ^n, (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * (k + 1))) ≤
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t /
      (coupling / (2 * (k + 1) : ℝ)) := by
  have hc : 0 < coupling / (2 * (k + 1) : ℝ) := by positivity
  have h := integral_semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergy_of_le
    (oddPowerPotential massSq coupling k) (fun z : ℝ ↦ coupling / (2 * (k + 1) : ℝ) *
      z ^ (2 * (k + 1))) (continuous_const.mul (continuous_id.pow _))
    (fun z ↦ mul_nonneg hc.le ((even_two_mul (k + 1)).pow_nonneg z))
    (oddPowerPotential_power_le k hmassSq) hu t henergyIntegrable
  simp only [semilinearWaveSpatialPotentialEnergyDensity] at h
  rw [integral_const_mul] at h
  exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using h)

/-- If at least one defocusing coefficient is positive, zero spatial energy
forces a continuous field to vanish on the entire time slice. -/
theorem defocusingPowerField_eq_zero_of_spatialEnergy_eq_zero {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 ≤ massSq) (hcoupling : 0 ≤ coupling) (hpositive : 0 < massSq ∨ 0 < coupling)
    {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t : ℝ)
    (henergyIntegrable :
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t = 0) :
    ∀ x : ℝ^n, u (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  rcases hpositive with hmassSqPos | hcouplingPos
  · exact semilinearWaveField_eq_zero_of_spatialEnergy_eq_zero (oddPowerPotential massSq coupling k)
      (massSq / 2) (by positivity) (oddPowerPotential_quadratic_le k hcoupling) hu t
      henergyIntegrable henergy
  have hnonneg (x : ℝ^n) : 0 ≤ u (PDE.Common.timeSpaceCons t x) ^ (2 * (k + 1)) :=
    (even_two_mul (k + 1)).pow_nonneg _
  have hle := integral_defocusingPowerFieldPow_le_spatialEnergy_div k hmassSq hcouplingPos hu t
    henergyIntegrable
  rw [henergy, zero_div] at hle
  have hint := le_antisymm hle (integral_nonneg hnonneg)
  have hzero := ((hu.comp (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
    ).ae_eq_iff_eq volume continuous_const).mp (by
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae (.of_forall hnonneg)
        (integrable_defocusingPowerFieldPow k hmassSq hcouplingPos hu t henergyIntegrable)).mp
          hint] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      exact (pow_eq_zero_iff (by omega : 2 * (k + 1) ≠ 0)).mp hx)
  exact fun x ↦ congrFun hzero x

/-- An energy equality transports zero-energy rigidity from the reference
time to the chosen spatial slice. -/
theorem defocusingPowerField_eq_zero_of_referenceEnergy_eq_zero {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 ≤ massSq) (hcoupling : 0 ≤ coupling) (hpositive : 0 < massSq ∨ 0 < coupling)
    {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t₀ t : ℝ)
    (henergyIntegrable :
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t))
    (henergyEq : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t =
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀)
    (hreferenceEnergy :
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ = 0) :
    ∀ x : ℝ^n, u (PDE.Common.timeSpaceCons (n := n) t x) = 0 :=
  defocusingPowerField_eq_zero_of_spatialEnergy_eq_zero k hmassSq hcoupling hpositive hu t
    henergyIntegrable (henergyEq.trans hreferenceEnergy)

/-- If every time slice has the reference energy, zero reference energy and
a positive defocusing coefficient make the spacetime field identically
zero. -/
theorem eq_zero_of_defocusingPowerEnergy_eq_zero {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 ≤ massSq) (hcoupling : 0 ≤ coupling) (hpositive : 0 < massSq ∨ 0 < coupling)
    {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t₀ : ℝ)
    (henergyIntegrable : ∀ t,
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t))
    (henergyEq : ∀ t,
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t =
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀)
    (hreferenceEnergy :
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ = 0) :
    u = 0 := by
  funext p
  simpa only [PDE.Common.timeSpaceCons_spatialPart, Pi.zero_apply] using
    defocusingPowerField_eq_zero_of_referenceEnergy_eq_zero k hmassSq hcoupling hpositive hu t₀
      (p 0) (henergyIntegrable (p 0)) (henergyEq (p 0)) hreferenceEnergy (PDE.Common.spatialPart p)

/-- An energy equality transports the defocusing `L²` field bound to a
reference time. -/
theorem integral_defocusingPowerFieldSq_le_referenceEnergy_div {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 < massSq) (hcoupling : 0 ≤ coupling) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u)
    (t₀ t : ℝ)
    (henergyIntegrable :
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t))
    (henergyEq : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t =
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀) :
    (∫ x : ℝ^n, (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) ≤
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ /
      (massSq / 2) :=
  henergyEq ▸ integral_defocusingPowerFieldSq_le_spatialEnergy_div k hmassSq hcoupling hu t
    henergyIntegrable

/-- An energy equality transports the nonlinear even-power bound to a
reference time. -/
theorem integral_defocusingPowerFieldPow_le_referenceEnergy_div {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 ≤ massSq) (hcoupling : 0 < coupling) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u)
    (t₀ t : ℝ)
    (henergyIntegrable :
      Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t))
    (henergyEq : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t =
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀) :
    (∫ x : ℝ^n, (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * (k + 1))) ≤
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ /
      (coupling / (2 * (k + 1) : ℝ)) :=
  henergyEq ▸ integral_defocusingPowerFieldPow_le_spatialEnergy_div k hmassSq hcoupling hu t
    henergyIntegrable

/-- An energy equality rewrites the full defocusing energy decomposition at
time `t` in terms of the reference energy at `t₀`. -/
theorem integral_defocusingPowerEnergy_eq_two_mul_referenceEnergy (massSq coupling : ℝ) (k : ℕ)
    {u : ℝ^(n + 1) → ℝ} (t₀ t : ℝ)
    (henergyEq : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t =
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀) :
    (∫ x : ℝ^n, ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
      ‖classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2 +
      massSq * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 + coupling / (k + 1 : ℝ) *
      (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * (k + 1))) = 2 *
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ :=
  henergyEq ▸ integral_defocusingPowerEnergy_eq_two_mul_spatialEnergy massSq coupling k u t

end WaveEquation
