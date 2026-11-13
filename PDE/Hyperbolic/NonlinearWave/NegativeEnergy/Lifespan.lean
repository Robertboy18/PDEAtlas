/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.DominatedData
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.Concavity
import PDE.Solution.Singularity.FiniteTime.Comparison.Concavity.LeftEndpoint
import PDE.Solution.Singularity.FiniteTime.Comparison.Concavity.RightEndpoint

/-!
# Lifespan bounds for negative-energy semilinear waves

We combine the negative-energy virial inequality with the scalar
concavity theorem to bound finite forward and backward existence intervals.
Closed slabs give strict Riccati-horizon inequalities, while half-open slabs
give non-strict endpoint inequalities. The theorems assume a solution on the
indicated slab; they neither construct it nor require maximality.

The shifted estimates cover time-symmetric initial data whose quadratic
momentum vanishes at the reference time. `DominatedVirialData` holds compact
support and domination on the relevant time slab. The equation, regularity,
and conserved negative energy remain explicit hypotheses.

At each included time, `hu` requires `C²` regularity on a common time neighborhood
for all spatial points. An open `C²` time domain containing the slab supplies this
condition, as explained in `NegativeEnergy.Concavity`. No regularity is required
at an excluded endpoint of a half-open slab.

The argument is Levine's concavity method, as in the proof of Evans, §12.5.1, Theorem 1, made
quantitative. With `I = ½ ∫ u²`, `P = ∫ u u_t = I'` and `a = (Λ - 2)/4`, the concavity inequality of
`NegativeEnergy.Concavity` implies the Riccati inequality `(P/I)' ≥ a (P/I)²` on the slab, so when
`P(t₀) > 0` the ratio `P/I` blows up no later than `t₀ + (a P(t₀)/I(t₀))⁻¹`, and a solution on a
closed slab `[t₀, T]` forces `T` to be strictly below that horizon. With reference time zero,
`F = ∫ u² = 2I` and `α = a`, the horizon is the time `F(0)/(αF'(0))` at which Levine's lower bound
(II-4) becomes infinite. The shifted variants handle `P(t₀) ≥ 0` by moving the reference time
forward, and the left-endpoint theorems are the time-reversed statements.

## Main results

* `right_endpoint_lt_riccati_horizon_of_negative_conserved_energy`,
  `right_endpoint_le_riccati_horizon_of_negative_conserved_energy`: forward
  lifespan bounds on closed and half-open slabs.
* `riccati_horizon_lt_left_endpoint_of_negative_conserved_energy`,
  `riccati_horizon_le_left_endpoint_of_negative_conserved_energy`: the
  backward counterparts.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, Theorem 1 and its proof, equations (6)-(7).
  <https://doi.org/10.1090/gsm/019>
* H. A. Levine, *Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `Pu_tt = -Au + F(u)`*, Trans. Amer. Math. Soc. 192 (1974), 1-21, proof of Theorem I,
  equations (II-2)-(II-4), pp. 5-6.
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PDE.Solution.Singularity.FiniteTime.Concavity
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- The analytic inputs of the scalar concavity theorems on an arbitrary time set: the mass
derivative, differentiability of the momentum, positivity of the mass, the concavity inequality,
and positivity of the two Riccati coefficients. -/
private theorem concavity_inputs {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {Λ t₀ : ℝ} {times : Set ℝ}
    (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ times, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 < Λ) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ times, ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u times)
    (henergyConserved : ∀ t ∈ times, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0) :
    (∀ t ∈ times, HasDerivAt (waveSpatialQuadraticMass u) (waveSpatialQuadraticMomentum u t) t) ∧
      (∀ t ∈ times, DifferentiableAt ℝ (waveSpatialQuadraticMomentum u) t) ∧
      (∀ t ∈ times, 0 < waveSpatialQuadraticMass u t) ∧
      (∀ t ∈ times, (1 + (Λ - 2) / 4) * waveSpatialQuadraticMomentum u t ^ 2 ≤
        waveSpatialQuadraticMass u t * (deriv (waveSpatialQuadraticMomentum u) t -
        (-Λ * semilinearWaveSpatialEnergy V u t₀))) ∧
      0 < (Λ - 2) / 4 ∧ 0 < -Λ * semilinearWaveSpatialEnergy V u t₀ :=
  ⟨hasDerivAt_waveSpatialQuadraticMass_on
      (fun t ht ↦ (hu t ht).mono fun r hr x ↦ (hr x).of_le (by norm_num)) hD.compact_support
      hD.mass_mem_nhds hD.mass_dominated hD.mass_bound_integrable,
    differentiableAt_waveSpatialQuadraticMomentum_on hu hD.compact_support hD.momentum_mem_nhds
      hD.momentum_dominated hD.momentum_bound_integrable,
    waveSpatialQuadraticMass_pos_on_of_negative_conserved_energy hVzero
      (fun t ht x ↦ ((hu t ht).self_of_nhds x).of_le (by norm_num)) hD.compact_support
      henergyConserved henergyNeg,
    waveSpatialQuadraticMomentum_concavity_inequality_on_of_conserved_energy hVzero hV hu hΛ.le
      hgrowth hwave hD.compact_support hD.momentum_mem_nhds hD.momentum_dominated
      hD.momentum_bound_integrable henergyConserved,
    by linarith, mul_pos_of_neg_of_neg (by linarith) henergyNeg⟩

/-- A negative-energy semilinear wave with positive initial quadratic
momentum can persist only up to the explicit Riccati horizon

`t₀ + (((Λ - 2) / 4) P(t₀) / I(t₀))⁻¹`.

The equation and support hypotheses hold on `[t₀, T]`; regularity and
integrable domination are local near each time in this slab. -/
theorem right_endpoint_lt_riccati_horizon_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ t₀ T : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ Icc t₀ T, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 < Λ) (htime : t₀ ≤ T) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ Icc t₀ T, ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Icc t₀ T))
    (henergyConserved : ∀ t ∈ Icc t₀ T, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0)
    (hmomentumPos : 0 < waveSpatialQuadraticMomentum (n := n) u t₀) :
    T < t₀ + (((Λ - 2) / 4) * (waveSpatialQuadraticMomentum (n := n) u t₀ /
      waveSpatialQuadraticMass (n := n) u t₀))⁻¹ := by
  obtain ⟨hI, hP, hpos, hconc, ha, hb⟩ :=
    concavity_inputs hVzero hV hu hΛ hgrowth hwave hD henergyConserved henergyNeg
  exact right_endpoint_lt_riccati_horizon ha hb.le hI hP (hpos t₀ (left_mem_Icc.mpr htime))
    hmomentumPos hpos fun t ht ↦ hconc t (Ioo_subset_Icc_self ht)

/-- If a negative-energy solution is available on the half-open slab
`[t₀, T)`, then its right endpoint is at most the Riccati horizon

`t₀ + (((Λ - 2) / 4) P(t₀) / I(t₀))⁻¹`.

The corresponding closed-slab estimate is strict. The scalar concavity results
pass from closed intervals to this non-strict half-open endpoint bound,
which is the form used for maximal existence intervals. -/
theorem right_endpoint_le_riccati_horizon_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ t₀ T : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ Ico t₀ T, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 < Λ) (htime : t₀ < T) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ Ico t₀ T, ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Ico t₀ T))
    (henergyConserved : ∀ t ∈ Ico t₀ T, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0)
    (hmomentumPos : 0 < waveSpatialQuadraticMomentum (n := n) u t₀) :
    T ≤ t₀ + (((Λ - 2) / 4) * (waveSpatialQuadraticMomentum (n := n) u t₀ /
      waveSpatialQuadraticMass (n := n) u t₀))⁻¹ := by
  obtain ⟨hI, hP, hpos, hconc, ha, hb⟩ :=
    concavity_inputs hVzero hV hu hΛ hgrowth hwave hD henergyConserved henergyNeg
  exact right_endpoint_le_riccati_horizon ha hb.le hI hP (hpos t₀ ⟨le_rfl, htime⟩) hmomentumPos hpos
    fun t ht ↦ hconc t ⟨ht.1.le, ht.2⟩

/-- A negative-energy semilinear wave with nonnegative initial quadratic
momentum satisfies a shifted Riccati lifespan bound.

For every `δ > 0` with `t₀ + δ ≤ T`, the strictly negative conserved energy
forces the momentum to become positive by time `t₀ + δ`. The concavity method
then gives

`T < t₀ + δ + (((Λ - 2) / 4) P(t₀ + δ) / I(t₀ + δ))⁻¹`.

This includes the time-symmetric case `P(t₀) = 0`, which the unshifted lifespan
bound does not cover. -/
theorem right_endpoint_lt_shifted_riccati_horizon_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ t₀ T δ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ Icc t₀ T, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 < Λ) (hδ : 0 < δ) (hshift : t₀ + δ ≤ T) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ Icc t₀ T, ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Icc t₀ T))
    (henergyConserved : ∀ t ∈ Icc t₀ T, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0)
    (hmomentumNonneg : 0 ≤ waveSpatialQuadraticMomentum (n := n) u t₀) :
    T < t₀ + δ + (((Λ - 2) / 4) * (waveSpatialQuadraticMomentum (n := n) u (t₀ + δ) /
      waveSpatialQuadraticMass (n := n) u (t₀ + δ)))⁻¹ := by
  obtain ⟨hI, hP, hpos, hconc, ha, hb⟩ :=
    concavity_inputs hVzero hV hu hΛ hgrowth hwave hD henergyConserved henergyNeg
  exact right_endpoint_lt_shifted_riccati_horizon ha hb hδ hshift hI hP hmomentumNonneg hpos
    fun t ht ↦ hconc t (Ioo_subset_Icc_self ht)

/-- On a half-open lifespan `[t₀, T)`, nonnegative initial quadratic
momentum gives the shifted endpoint estimate

`T ≤ t₀ + δ + (((Λ - 2) / 4) P(t₀ + δ) / I(t₀ + δ))⁻¹`

for every `δ > 0` with `t₀ + δ < T`. This is the half-open counterpart of the
strict closed-slab theorem above and includes the time-symmetric case `P(t₀) = 0`. -/
theorem right_endpoint_le_shifted_riccati_horizon_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ t₀ T δ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ Ico t₀ T, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 < Λ) (hδ : 0 < δ) (hshift : t₀ + δ < T) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ Ico t₀ T, ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Ico t₀ T))
    (henergyConserved : ∀ t ∈ Ico t₀ T, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0)
    (hmomentumNonneg : 0 ≤ waveSpatialQuadraticMomentum (n := n) u t₀) :
    T ≤ t₀ + δ + (((Λ - 2) / 4) * (waveSpatialQuadraticMomentum (n := n) u (t₀ + δ) /
      waveSpatialQuadraticMass (n := n) u (t₀ + δ)))⁻¹ := by
  obtain ⟨hI, hP, hpos, hconc, ha, hb⟩ :=
    concavity_inputs hVzero hV hu hΛ hgrowth hwave hD henergyConserved henergyNeg
  exact right_endpoint_le_shifted_riccati_horizon ha hb hδ hshift hI hP hmomentumNonneg hpos
    fun t ht ↦ hconc t ⟨ht.1.le, ht.2⟩

/-- A negative-energy semilinear wave with negative quadratic momentum at
`t₀` cannot extend backward to the closed endpoint `T` unless

`t₀ - (((Λ - 2) / 4) * (-P(t₀) / I(t₀)))⁻¹ < T`.

The equation and support hypotheses hold on `[T, t₀]`, with regularity and
integrable domination local near its times. The estimate is the time-reflected
counterpart of the strict forward Riccati bound. -/
theorem riccati_horizon_lt_left_endpoint_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ T t₀ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ Icc T t₀, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 < Λ) (htime : T ≤ t₀) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ Icc T t₀, ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Icc T t₀))
    (henergyConserved : ∀ t ∈ Icc T t₀, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0)
    (hmomentumNeg : waveSpatialQuadraticMomentum (n := n) u t₀ < 0) :
    t₀ - (((Λ - 2) / 4) * (-waveSpatialQuadraticMomentum (n := n) u t₀ /
      waveSpatialQuadraticMass (n := n) u t₀))⁻¹ < T := by
  obtain ⟨hI, hP, hpos, hconc, ha, hb⟩ :=
    concavity_inputs hVzero hV hu hΛ hgrowth hwave hD henergyConserved henergyNeg
  exact riccati_horizon_lt_left_endpoint ha hb.le hI hP (hpos t₀ (right_mem_Icc.mpr htime))
    hmomentumNeg hpos fun t ht ↦ hconc t (Ioo_subset_Icc_self ht)

/-- On a half-open past time slab `(T, t₀]`, negative quadratic momentum at
`t₀` gives the non-strict endpoint estimate

`t₀ - (((Λ - 2) / 4) * (-P(t₀) / I(t₀)))⁻¹ ≤ T`.

The half-open time slab is the backward analogue of `[t₀, T)`. -/
theorem riccati_horizon_le_left_endpoint_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ T t₀ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ Ioc T t₀, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 < Λ) (htime : T < t₀) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ Ioc T t₀, ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Ioc T t₀))
    (henergyConserved : ∀ t ∈ Ioc T t₀, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0)
    (hmomentumNeg : waveSpatialQuadraticMomentum (n := n) u t₀ < 0) :
    t₀ - (((Λ - 2) / 4) * (-waveSpatialQuadraticMomentum (n := n) u t₀ /
      waveSpatialQuadraticMass (n := n) u t₀))⁻¹ ≤ T := by
  obtain ⟨hI, hP, hpos, hconc, ha, hb⟩ :=
    concavity_inputs hVzero hV hu hΛ hgrowth hwave hD henergyConserved henergyNeg
  exact riccati_horizon_le_left_endpoint ha hb.le hI hP (hpos t₀ ⟨htime, le_rfl⟩) hmomentumNeg hpos
    fun t ht ↦ hconc t ⟨ht.1, ht.2.le⟩

/-- If the quadratic momentum at `t₀` is nonpositive, then every earlier
shift `t₀ - δ` with `δ > 0` has strictly negative momentum. On `[T, t₀]`
this yields

`t₀ - δ - (((Λ - 2) / 4) * (-P(t₀ - δ) / I(t₀ - δ)))⁻¹ < T`

whenever `T ≤ t₀ - δ`. The positive forcing comes from the negative
conserved energy. -/
theorem shifted_riccati_horizon_lt_left_endpoint_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ T t₀ δ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ Icc T t₀, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 < Λ) (hδ : 0 < δ) (hshift : T ≤ t₀ - δ) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ Icc T t₀, ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Icc T t₀))
    (henergyConserved : ∀ t ∈ Icc T t₀, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0)
    (hmomentumNonpos : waveSpatialQuadraticMomentum (n := n) u t₀ ≤ 0) :
    t₀ - δ - (((Λ - 2) / 4) * (-waveSpatialQuadraticMomentum (n := n) u (t₀ - δ) /
      waveSpatialQuadraticMass (n := n) u (t₀ - δ)))⁻¹ < T := by
  obtain ⟨hI, hP, hpos, hconc, ha, hb⟩ :=
    concavity_inputs hVzero hV hu hΛ hgrowth hwave hD henergyConserved henergyNeg
  exact shifted_riccati_horizon_lt_left_endpoint ha hb hδ hshift hI hP hmomentumNonpos hpos
    fun t ht ↦ hconc t (Ioo_subset_Icc_self ht)

/-- On a half-open past time slab `(T, t₀]`, nonpositive momentum at `t₀`
gives the shifted non-strict estimate

`t₀ - δ - (((Λ - 2) / 4) * (-P(t₀ - δ) / I(t₀ - δ)))⁻¹ ≤ T`

for every `δ > 0` with `T < t₀ - δ`. This includes time-symmetric initial
data with zero quadratic momentum. -/
theorem shifted_riccati_horizon_le_left_endpoint_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ T t₀ δ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ Ioc T t₀, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 < Λ) (hδ : 0 < δ) (hshift : T < t₀ - δ) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ Ioc T t₀, ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Ioc T t₀))
    (henergyConserved : ∀ t ∈ Ioc T t₀, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0)
    (hmomentumNonpos : waveSpatialQuadraticMomentum (n := n) u t₀ ≤ 0) :
    t₀ - δ - (((Λ - 2) / 4) * (-waveSpatialQuadraticMomentum (n := n) u (t₀ - δ) /
      waveSpatialQuadraticMass (n := n) u (t₀ - δ)))⁻¹ ≤ T := by
  obtain ⟨hI, hP, hpos, hconc, ha, hb⟩ :=
    concavity_inputs hVzero hV hu hΛ hgrowth hwave hD henergyConserved henergyNeg
  exact shifted_riccati_horizon_le_left_endpoint ha hb hδ hshift hI hP hmomentumNonpos hpos
    fun t ht ↦ hconc t ⟨ht.1, ht.2.le⟩

end WaveEquation
