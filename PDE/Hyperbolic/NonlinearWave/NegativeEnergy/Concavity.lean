/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Basic
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Differentiation
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Estimates
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.Virial.Concavity

/-!
# Concavity inequality for negative-energy semilinear waves

We assemble the analytic input used by the concavity method for
semilinear wave equations. Conserved negative energy gives positivity of the
quadratic mass and turns the virial identity into the differential inequality
required by scalar Riccati comparison.

The regularity, positivity, and differential inequality conclusions are
separate theorems, each with only the hypotheses it needs.

The time-local regularity hypothesis uses one time neighborhood for all spatial
points at each included time. If `u` is `C²` on the strip `{p | p 0 ∈ J}` for
an open set `J`, every `t ∈ J` has this property: eventually `r ∈ J`, and the
open-strip regularity gives `ContDiffAt` at every `(r, x)`. In particular, `J`
may exclude a finite singular endpoint. Domination neighborhoods are intersected
with these regularity neighborhoods before differentiating the integrals.

This is Levine's concavity method, in the form of the proof of Evans, §12.5.1, Theorem 1. With
`I(t) = ½ ∫ u² dx` and `P(t) = ∫ u u_t dx = I'(t)`, the virial identity for `u_tt - Δu + V'(u) = 0`
under the growth condition `z V'(z) ≤ Λ V(z)` with `Λ ≥ 2`, combined with conserved negative energy,
gives

`(1 + (Λ - 2)/4) P² ≤ I (P' + Λ E(t₀))`,

the inequality (6) of Evans with `α = (Λ - 2)/4` and `β = -Λ E(t₀)`. The scalar comparison theorems
in `PDE.Solution.Singularity.FiniteTime.Comparison.Concavity` take it as input.

## Main results

* `hasDerivAt_waveSpatialQuadraticMass_on`,
  `differentiableAt_waveSpatialQuadraticMomentum_on`: `I' = P` and
  differentiability of `P` on a time set, from local dominated differentiation.
* `waveSpatialQuadraticMass_pos_on_of_negative_conserved_energy`: `I > 0` when
  the conserved energy is negative.
* `waveSpatialQuadraticMomentum_concavity_inequality_on_of_conserved_energy`:
  the displayed inequality on the time set.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, proof of Theorem 1, equations (4)-(6).
  <https://doi.org/10.1090/gsm/019>
* H. A. Levine, *Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `Pu_tt = -Au + F(u)`*, Trans. Amer. Math. Soc. 192 (1974), 1-21, Section II,
  hypothesis (F-II), and the proof of Theorem I, equations (II-2)-(II-6), pp. 3-6.
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Differentiate the spatial quadratic mass at every time in `times`.

The time-dependent neighborhoods and bounds allow the local domination data
for differentiation under the integral to vary along the lifespan. -/
theorem hasDerivAt_waveSpatialQuadraticMass_on {u : ℝ^(n + 1) → ℝ} {times : Set ℝ}
    {neighborhood : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ}
    (hu : ∀ t ∈ times, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 1 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hcompact : ∀ t ∈ times, HasCompactSupport (fun x : ℝ^n ↦
      u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hneighborhood : ∀ t ∈ times, neighborhood t ∈ 𝓝 t)
    (hdominated : ∀ t ∈ times, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ neighborhood t,
      ‖waveSpatialQuadraticMomentumDensity (n := n) u r x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t ∈ times, Integrable (bound t)) :
    ∀ t ∈ times, HasDerivAt (waveSpatialQuadraticMass (n := n) u)
      (waveSpatialQuadraticMomentum (n := n) u t) t := by
  intro t ht
  let s := neighborhood t ∩ {r | ∀ x : ℝ^n,
    ContDiffAt ℝ 1 u (PDE.Common.timeSpaceCons (n := n) r x)}
  exact hasDerivAt_waveSpatialQuadraticMass (s := s) (fun _ hr ↦ hr.2)
    (inter_mem (hneighborhood t ht) (hu t ht)) (hcompact t ht)
    (by
      filter_upwards [hdominated t ht] with x hx
      exact fun r hr ↦ hx r hr.1) (hboundIntegrable t ht)

/-- The spatial quadratic momentum is differentiable at every time in
`times` under local dominated-differentiation hypotheses. -/
theorem differentiableAt_waveSpatialQuadraticMomentum_on {u : ℝ^(n + 1) → ℝ} {times : Set ℝ}
    {neighborhood : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ}
    (hu : ∀ t ∈ times, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hcompact : ∀ t ∈ times, HasCompactSupport (fun x : ℝ^n ↦
      u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hneighborhood : ∀ t ∈ times, neighborhood t ∈ 𝓝 t)
    (hdominated : ∀ t ∈ times, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ neighborhood t,
      ‖waveSpatialQuadraticMomentumDerivativeDensity (n := n) u r x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t ∈ times, Integrable (bound t)) :
    ∀ t ∈ times, DifferentiableAt ℝ (waveSpatialQuadraticMomentum (n := n) u) t := by
  intro t ht
  let s := neighborhood t ∩ {r | ∀ x : ℝ^n,
    ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x)}
  exact (hasDerivAt_waveSpatialQuadraticMomentum (s := s) (fun _ hr ↦ hr.2)
      (inter_mem (hneighborhood t ht) (hu t ht)) (hcompact t ht)
      (by
        filter_upwards [hdominated t ht] with x hx
        exact fun r hr ↦ hx r hr.1) (hboundIntegrable t ht)).differentiableAt

/-- Conserved negative energy makes the spatial quadratic mass strictly
positive throughout `times`. -/
theorem waveSpatialQuadraticMass_pos_on_of_negative_conserved_energy {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {t₀ : ℝ} {times : Set ℝ} (hVzero : V 0 = 0)
    (hu : ∀ t ∈ times, ∀ x : ℝ^n, ContDiffAt ℝ 1 u (PDE.Common.timeSpaceCons (n := n) t x))
    (hcompact : ∀ t ∈ times, HasCompactSupport (fun x : ℝ^n ↦
      u (PDE.Common.timeSpaceCons (n := n) t x)))
    (henergyConserved : ∀ t ∈ times, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0) :
    ∀ t ∈ times, 0 < waveSpatialQuadraticMass (n := n) u t := by
  intro t ht
  apply waveSpatialQuadraticMass_pos_of_spatialEnergy_neg hVzero t (hu t ht) (hcompact t ht)
  rw [henergyConserved t ht]
  exact henergyNeg

/-- Conserved energy turns the virial estimate into the concavity
inequality

`(1 + (Λ - 2) / 4) P² ≤ I (P' + Λ E(t₀))`.

Keeping the time set abstract lets closed intervals, maximal half-open
intervals, and half-lines reuse the same analytic argument. -/
theorem waveSpatialQuadraticMomentum_concavity_inequality_on_of_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ t₀ : ℝ} {times : Set ℝ} {momentumNeighborhood : ℝ → Set ℝ}
    {momentumBound : ℝ → ℝ^n → ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ times, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 ≤ Λ) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t ∈ times, ∀ x : ℝ^n, semilinearWaveOperator (n := n) V u
      (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hcompact : ∀ t ∈ times, HasCompactSupport (fun x : ℝ^n ↦
      u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hmomentumNeighborhood : ∀ t ∈ times, momentumNeighborhood t ∈ 𝓝 t)
    (hmomentumDominated : ∀ t ∈ times, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ momentumNeighborhood t,
      ‖waveSpatialQuadraticMomentumDerivativeDensity (n := n) u r x‖ ≤ momentumBound t x)
    (hmomentumBoundIntegrable : ∀ t ∈ times, Integrable (momentumBound t))
    (henergyConserved : ∀ t ∈ times, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀) :
    ∀ t ∈ times,
      (1 + (Λ - 2) / 4) *
          waveSpatialQuadraticMomentum (n := n) u t ^ 2 ≤
        waveSpatialQuadraticMass (n := n) u t *
          (deriv (waveSpatialQuadraticMomentum (n := n) u) t -
            (-Λ * semilinearWaveSpatialEnergy (n := n) V u t₀)) := by
  intro t ht
  have hpointwise :=
    waveSpatialQuadraticMomentum_concavity_inequality
      (s := momentumNeighborhood t ∩ {r | ∀ x : ℝ^n,
        ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x)})
      hVzero hV (fun _ hr ↦ hr.2) hΛ
      (inter_mem (hmomentumNeighborhood t ht) (hu t ht)) (hcompact t ht)
      (by
        filter_upwards [hmomentumDominated t ht] with x hx
        exact fun r hr ↦ hx r hr.1)
      (hmomentumBoundIntegrable t ht)
      (hwave t ht) hgrowth
  rw [henergyConserved t ht] at hpointwise
  convert hpointwise using 1
  all_goals ring

end WaveEquation
