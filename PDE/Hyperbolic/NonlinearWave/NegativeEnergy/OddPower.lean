/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Scalar.OddPower
public import PDE.Hyperbolic.NonlinearWave.DominatedData
import PDE.Hyperbolic.NonlinearWave.DefocusingPower.Conservation
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Bounds
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.GlobalObstruction

/-!
# Negative-energy obstruction for odd-power waves

We specialize the abstract negative-energy concavity theorem to

`uₜₜ - Δu + massSq * u + coupling * u^(2 * k + 1) = 0`.

When `massSq ≥ 0`, the canonical odd-power potential satisfies

`z V'(z) ≤ 2 (k + 1) V(z)`.

For `k > 0`, the coefficient `2 * (k + 1)` is strictly larger than two, so
negative initial energy rules out continuation for all future or all past
times under explicit compact-support and differentiation hypotheses.
The coupling is left arbitrary: in the usual focusing application it is
negative, while the negative-energy assumption already captures the sign
needed by the continuation argument.

The first theorem makes this sign information precise: if `massSq ≥ 0` and
the spatial energy is negative, then the coupling must be negative. Thus the
negative-energy theory is a focusing phenomenon.

This is the classical setting of Levine's concavity method and of Evans, §12.5.1, Theorem 1, with
`λ = 2 (k + 1)` in the condition (2): the focusing power nonlinearity
`u_tt - Δu = |coupling| u^(2k+1)`, possibly with a mass term, has solutions with negative energy,
and none of them can be global classical solutions with compact spatial support.

## Main results

* `coupling_neg_of_oddPower_spatialEnergy_neg`: negative energy forces
  `coupling < 0`.
* `not_global_forward_oddPower_of_negative_conserved_energy`,
  `not_global_backward_oddPower_of_negative_conserved_energy`: the
  obstruction assuming conservation of energy.
* `not_global_forward_oddPower_of_negative_energy`,
  `not_global_backward_oddPower_of_negative_energy`: the same with
  conservation derived from the local energy identity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, Theorem 1, equations (2)-(3).
  <https://doi.org/10.1090/gsm/019>
* H. A. Levine, *Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `Pu_tt = -Au + F(u)`*, Trans. Amer. Math. Soc. 192 (1974), 1-21, Theorem I(A),
  pp. 4-5.
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Scalar
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Negative odd-power wave energy with nonnegative mass coefficient forces
the nonlinear coupling to be focusing.

If `coupling ≥ 0`, every term in the canonical potential is nonnegative, so
the full spatial energy cannot be negative. -/
theorem coupling_neg_of_oddPower_spatialEnergy_neg {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 ≤ massSq) (u : ℝ^(n + 1) → ℝ) (t : ℝ)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t < 0) :
    coupling < 0 := by
  by_contra hcoupling
  have hcouplingNonneg : 0 ≤ coupling := le_of_not_gt hcoupling
  exact (not_lt_of_ge <| semilinearWaveSpatialEnergy_nonneg (oddPowerPotential massSq coupling k)
      (oddPowerPotential_nonneg k hmassSq hcouplingNonneg) u t) henergyNeg

/-- An odd-power semilinear wave with nonnegative mass coefficient cannot
retain negative conserved energy while continuing classically for all future
times.

`DominatedVirialData` records the compact support and domination required by the concavity
method. -/
theorem not_global_forward_oddPower_of_negative_conserved_energy {massSq coupling : ℝ} {k : ℕ}
    {u : ℝ^(n + 1) → ℝ} {t₀ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, t₀ ≤ t → ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Ici t₀))
    (henergyConserved : ∀ t, t₀ ≤ t → semilinearWaveSpatialEnergy (n := n)
      (oddPowerPotential massSq coupling k) u t = semilinearWaveSpatialEnergy (n := n)
      (oddPowerPotential massSq coupling k) u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0) :
    False :=
  not_global_forward_semilinearWave_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
    (oddPowerPotential_zero massSq coupling k)
    ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
    (two_lt_oddPower_growth_factor hk) (mul_deriv_oddPowerPotential_le coupling k hmassSq)
    (fun t ht x ↦ by
      simpa only [semilinearWaveOperator, deriv_oddPowerPotential, oddPowerPolynomial,
        add_assoc] using hwave t ht x)
    hD henergyConserved henergyNeg

/-- An odd-power semilinear wave with nonnegative mass coefficient cannot
retain negative conserved energy while continuing classically for all past
times.

This is the past-time counterpart of
`not_global_forward_oddPower_of_negative_conserved_energy`. The
odd-power potential supplies the same growth coefficient `2 * (k + 1)`; the
generic backward concavity theorem handles the change of time direction. -/
theorem not_global_backward_oddPower_of_negative_conserved_energy {massSq coupling : ℝ} {k : ℕ}
    {u : ℝ^(n + 1) → ℝ} {t₀ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, t ≤ t₀ → ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Iic t₀))
    (henergyConserved : ∀ t, t ≤ t₀ → semilinearWaveSpatialEnergy (n := n)
      (oddPowerPotential massSq coupling k) u t = semilinearWaveSpatialEnergy (n := n)
      (oddPowerPotential massSq coupling k) u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0) :
    False :=
  not_global_backward_semilinearWave_of_negative_conserved_energy (Λ := 2 * (k + 1 : ℝ))
    (oddPowerPotential_zero massSq coupling k)
    ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp)) hu
    (two_lt_oddPower_growth_factor hk) (mul_deriv_oddPowerPotential_le coupling k hmassSq)
    (fun t ht x ↦ by
      simpa only [semilinearWaveOperator, deriv_oddPowerPotential, oddPowerPolynomial,
        add_assoc] using hwave t ht x)
    hD henergyConserved henergyNeg

/-- A `C²` odd-power wave conserves its energy on an order-connected set of times on which the
equation and the domination data of the energy hold: the energy at every time of the set is the
energy at a reference time `t₀` of the set. -/
private theorem oddPowerSpatialEnergy_eq_reference {massSq coupling : ℝ} {k : ℕ}
    {u : ℝ^(n + 1) → ℝ} {times : Set ℝ} {t₀ : ℝ} (htimes : times.OrdConnected) (ht₀ : t₀ ∈ times)
    (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t ∈ times, ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u times) :
    ∀ t ∈ times, semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t =
      semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u t₀ :=
  fun _ ht ↦ oddPowerSpatialEnergy_eq_of_wave_on_ordConnected massSq coupling k htimes ht ht₀
    (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ hu.contDiffAt) hwave hE.energy_integrable
    hE.mem_nhds hE.dominated hE.bound_integrable hE.flux_compact_support

/-- Negative initial energy prevents a classical odd-power wave from
continuing for all future times under the explicit hypotheses needed to
derive energy conservation.

The energy is conserved on the order-connected set `[t₀, ∞)`
(`oddPowerSpatialEnergy_eq_of_wave_on_ordConnected`); then
`not_global_forward_oddPower_of_negative_conserved_energy` applies. -/
theorem not_global_forward_oddPower_of_negative_energy {massSq coupling : ℝ} {k : ℕ}
    {u : ℝ^(n + 1) → ℝ} {t₀ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, t₀ ≤ t → ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Ici t₀))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Ici t₀))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0) :
    False :=
  not_global_forward_oddPower_of_negative_conserved_energy hmassSq hk hu hwave hD
    (oddPowerSpatialEnergy_eq_reference ordConnected_Ici self_mem_Ici hu hwave hE) henergyNeg

/-- Negative initial energy prevents a classical odd-power wave from
continuing for all past times under the explicit hypotheses needed to derive
energy conservation.

The energy is conserved on the order-connected set `(-∞, t₀]`
(`oddPowerSpatialEnergy_eq_of_wave_on_ordConnected`); then
`not_global_backward_oddPower_of_negative_conserved_energy` applies. -/
theorem not_global_backward_oddPower_of_negative_energy {massSq coupling : ℝ} {k : ℕ}
    {u : ℝ^(n + 1) → ℝ} {t₀ : ℝ} (hmassSq : 0 ≤ massSq) (hk : 0 < k) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, t ≤ t₀ → ∀ x : ℝ^n, waveOperator (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x) + massSq * u (PDE.Common.timeSpaceCons (n := n) t x) +
      coupling * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ (2 * k + 1) = 0)
    (hD : DominatedVirialData u (Iic t₀))
    (hE : DominatedEnergyData (oddPowerPotential massSq coupling k) u (Iic t₀))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) (oddPowerPotential massSq coupling k) u
      t₀ < 0) :
    False :=
  not_global_backward_oddPower_of_negative_conserved_energy hmassSq hk hu hwave hD
    (oddPowerSpatialEnergy_eq_reference ordConnected_Iic self_mem_Iic hu hwave hE) henergyNeg

end WaveEquation
