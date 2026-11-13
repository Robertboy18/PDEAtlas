/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Differentiating semilinear wave energy

We differentiate total semilinear wave energy under the spatial
integral. An explicit local integrable dominator justifies the exchange of
derivative and integral. Compact support of every fixed-time flux component
then removes the spatial divergence from the integrated local energy balance.

For classical solutions, these hypotheses imply that the global-energy
derivative vanishes at each time. Constancy on time intervals is proved in
`GlobalEnergy.Conservation`.

This is the first half of the conservation-of-energy computation for
`u_tt - Δu + V'(u) = 0` (Evans, §12.1.1, proof of Theorem 1):
`d/dt E(t) = ∫ ∂ₜ e dx = ∫ div(flux) dx = 0`.  The two steps are stated with the
exact dominated-convergence and compact-support hypotheses they need.

## Main results

* `hasDerivAt_semilinearWaveSpatialEnergy`: differentiation under the spatial
  integral, given a local integrable dominator for `∂ₜ e`.
* `integral_semilinearWaveEnergyBalanceResidual_timeSpaceCons_eq`: compactly
  supported flux components integrate to zero, so `∫ ∂ₜ e` equals the integral
  of the local energy-balance residual `∂ₜ e - div(flux)`.
* `hasDerivAt_semilinearWaveSpatialEnergy_eq_zero`: for a solution the
  residual vanishes pointwise, so `E'(t) = 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace WaveEquation

variable {n : ℕ}

/-- The time-coordinate derivative of the semilinear wave-energy density,
restricted to a fixed-time spatial slice. -/
def semilinearWaveSpatialEnergyTimeDerivative (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    ℝ :=
  (∂[0] (semilinearWaveEnergyDensity (n := n) V u)) (PDE.Common.timeSpaceCons (n := n) t x)

/-- The `i`th semilinear wave-energy flux restricted to a fixed-time spatial
slice. -/
def semilinearWaveSpatialEnergyFlux (u : ℝ^(n + 1) → ℝ) (i : Fin n) (t : ℝ) (x : ℝ^n) : ℝ :=
  classicalWaveEnergyFlux (n := n) u i (PDE.Common.timeSpaceCons (n := n) t x)

/-- A fixed-time semilinear wave-energy density is `C¹` in space. -/
theorem contDiff_semilinearWaveSpatialEnergyDensity {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ}
    (hV : ContDiff ℝ 1 V)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x)) :
    ContDiff ℝ 1 (semilinearWaveSpatialEnergyDensity (n := n) V u t) :=
  contDiff_iff_contDiffAt.mpr fun x ↦
    (contDiffAt_semilinearWaveEnergyDensity (n := n) hV.contDiffAt (hu x)).comp x
      (PDE.Common.contDiff_timeSpaceCons_spatial n t).contDiffAt

/-- Along a fixed spatial point, the derivative of the energy density is its
time-coordinate partial derivative. -/
theorem hasDerivAt_semilinearWaveSpatialEnergyDensity {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ}
    {x : ℝ^n} (hV : ContDiff ℝ 1 V)
    (hu : ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x)) :
    HasDerivAt (fun r ↦ semilinearWaveSpatialEnergyDensity (n := n) V u r x)
      (semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t x) t := by
  simpa [semilinearWaveSpatialEnergyDensity, semilinearWaveSpatialEnergyTimeDerivative] using
    PDE.hasDerivAt_timeSpaceCons (semilinearWaveEnergyDensity V u) t x
      ((contDiffAt_semilinearWaveEnergyDensity hV.contDiffAt hu).differentiableAt one_ne_zero)

/-- The time derivative of the energy density is continuous on every
fixed-time spatial slice. -/
theorem continuous_semilinearWaveSpatialEnergyTimeDerivative {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ}
    (hV : ContDiff ℝ 1 V)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x)) :
    Continuous (semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t) :=
  continuous_iff_continuousAt.mpr fun x ↦
    (PDE.contDiffAt_partialDeriv 0
      (contDiffAt_semilinearWaveEnergyDensity hV.contDiffAt (hu x)) 0).continuousAt.comp
        (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt

/-- Every fixed-time spatial energy-flux component of a `C²` field is `C¹`. -/
theorem contDiff_semilinearWaveSpatialEnergyFlux {u : ℝ^(n + 1) → ℝ} {t : ℝ}
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x)) (i : Fin n) :
    ContDiff ℝ 1 (semilinearWaveSpatialEnergyFlux (n := n) u i t) :=
  contDiff_iff_contDiffAt.mpr fun x ↦ (contDiffAt_classicalWaveEnergyFlux (n := n) (hu x) i).comp x
    (PDE.Common.contDiff_timeSpaceCons_spatial n t).contDiffAt

/-- A spatial derivative of a fixed-time energy-flux component is the
corresponding spacetime derivative. -/
theorem partialDeriv_semilinearWaveSpatialEnergyFlux {u : ℝ^(n + 1) → ℝ} {t : ℝ} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x)) (i : Fin n) :
    (∂[i] (semilinearWaveSpatialEnergyFlux (n := n) u i t)) x =
      (∂[i.succ] (classicalWaveEnergyFlux (n := n) u i)) (PDE.Common.timeSpaceCons (n := n) t x) :=
  PDE.partialDeriv_timeSpaceCons_spatial i (classicalWaveEnergyFlux u i) t x
    ((contDiffAt_classicalWaveEnergyFlux hu i).differentiableAt one_ne_zero)

/-- On a fixed-time slice, the local energy residual is the time derivative
of the energy density minus the spatial divergence of the flux. -/
theorem semilinearWaveEnergyBalanceResidual_timeSpaceCons_eq {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ}
    {x : ℝ^n} (hV : ContDiff ℝ 1 V)
    (hu : ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x)) :
    semilinearWaveEnergyBalanceResidual (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) =
      semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t x - ∑ i : Fin n,
      (∂[i] (semilinearWaveSpatialEnergyFlux (n := n) u i t)) x := by
  rw [semilinearWaveEnergyBalanceResidual_eq_partialDeriv_sub_sum hV hu]
  unfold semilinearWaveSpatialEnergyTimeDerivative
  congr 1
  exact sum_congr rfl fun i _ ↦ (partialDeriv_semilinearWaveSpatialEnergyFlux hu i).symm

/-- The pointwise semilinear wave equation turns the time derivative of the
energy density into the spatial divergence of the energy flux. -/
theorem semilinearWaveSpatialEnergyTimeDerivative_eq_sum_partialDeriv_flux {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {t : ℝ} {x : ℝ^n} (hV : ContDiff ℝ 1 V)
    (hu : ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x))
    (hwave : semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0) :
    semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t x = ∑ i : Fin n,
      (∂[i] (semilinearWaveSpatialEnergyFlux (n := n) u i t)) x :=
  sub_eq_zero.mp ((semilinearWaveEnergyBalanceResidual_timeSpaceCons_eq hV hu).symm.trans
    (semilinearWaveEnergyBalanceResidual_eq_zero hV hu hwave))

/-- Differentiation under the spatial integral for semilinear wave energy.

Regularity holds throughout one common time neighborhood for every spatial
point. Its intersection with the dominator's neighborhood suffices. -/
theorem hasDerivAt_semilinearWaveSpatialEnergy {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ} {s : Set ℝ}
    {bound : ℝ^n → ℝ} (hV : ContDiff ℝ 1 V)
    (hu : ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hs : s ∈ 𝓝 t)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) V u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound) :
    Integrable (semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t) ∧
      HasDerivAt (semilinearWaveSpatialEnergy (n := n) V u)
      (∫ x, semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t x) t := by
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := semilinearWaveSpatialEnergyTimeDerivative V u)
    (s := s ∩ {r | ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons r x)}) (inter_mem hs hu)
  · filter_upwards [hu] with r hr
    exact (contDiff_semilinearWaveSpatialEnergyDensity hV hr).continuous.aestronglyMeasurable
  · exact henergyIntegrable
  · exact (continuous_semilinearWaveSpatialEnergyTimeDerivative hV
      hu.self_of_nhds).aestronglyMeasurable
  · filter_upwards [hdominated] with x hx
    exact fun r hr ↦ hx r hr.1
  · exact hboundIntegrable
  · exact .of_forall fun x r hr ↦ hasDerivAt_semilinearWaveSpatialEnergyDensity hV (hr.2 x)

/-- The spatial divergence of a compactly supported fixed-time energy flux is integrable. -/
private theorem integrable_sum_partialDeriv_flux {u : ℝ^(n + 1) → ℝ} {t : ℝ}
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons t x))
    (hfluxCompact : ∀ i, HasCompactSupport (semilinearWaveSpatialEnergyFlux u i t)) :
    Integrable fun x ↦ ∑ i : Fin n, (∂[i] (semilinearWaveSpatialEnergyFlux u i t)) x := by
  simpa using integrable_finsetSum univ fun i _ ↦
    PDE.DistributionTheory.integrable_partialDeriv_of_hasCompactSupport i
      (contDiff_semilinearWaveSpatialEnergyFlux hu i) (hfluxCompact i)

/-- The fixed-time local energy residual is integrable when the time
derivative of the density is integrable and every flux component is compactly
supported. -/
theorem integrable_semilinearWaveEnergyBalanceResidual_timeSpaceCons {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {t : ℝ} (hV : ContDiff ℝ 1 V)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x))
    (henergyTimeIntegrable : Integrable (semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t))
    (hfluxCompact : ∀ i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t)) :
    Integrable fun x : ℝ^n ↦
      semilinearWaveEnergyBalanceResidual (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) :=
  (henergyTimeIntegrable.sub (integrable_sum_partialDeriv_flux hu hfluxCompact)).congr
    (.of_forall fun x ↦ (semilinearWaveEnergyBalanceResidual_timeSpaceCons_eq hV (hu x)).symm)

/-- Compact support of the fixed-time energy flux removes the spatial
divergence from the integral of the local energy residual. -/
theorem integral_semilinearWaveEnergyBalanceResidual_timeSpaceCons_eq {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {t : ℝ} (hV : ContDiff ℝ 1 V)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x))
    (henergyTimeIntegrable : Integrable (semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t))
    (hfluxCompact : ∀ i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t)) :
    (∫ x : ℝ^n,
      semilinearWaveEnergyBalanceResidual (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x)) =
      ∫ x, semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t x := by
  rw [integral_congr_ae (.of_forall fun x ↦
      semilinearWaveEnergyBalanceResidual_timeSpaceCons_eq hV (hu x)),
    integral_sub henergyTimeIntegrable (integrable_sum_partialDeriv_flux hu hfluxCompact),
    integral_finsetSum univ fun i _ ↦
      PDE.DistributionTheory.integrable_partialDeriv_of_hasCompactSupport i
        (contDiff_semilinearWaveSpatialEnergyFlux hu i) (hfluxCompact i)]
  simp [PDE.DistributionTheory.integral_partialDeriv_eq_zero_of_hasCompactSupport _
    (contDiff_semilinearWaveSpatialEnergyFlux hu _) (hfluxCompact _)]

/-- The derivative of global semilinear wave energy is the spatial integral
of the local energy-balance residual. -/
theorem hasDerivAt_semilinearWaveSpatialEnergy_eq_integral_balanceResidual {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {t : ℝ} {s : Set ℝ} {bound : ℝ^n → ℝ} (hV : ContDiff ℝ 1 V)
    (hu : ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hs : s ∈ 𝓝 t)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) V u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound)
    (hfluxCompact : ∀ i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t)) :
    HasDerivAt (semilinearWaveSpatialEnergy (n := n) V u)
      (∫ x : ℝ^n,
      semilinearWaveEnergyBalanceResidual (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x)) t :=
      by
  have hderivative :=
    hasDerivAt_semilinearWaveSpatialEnergy hV hu hs henergyIntegrable hdominated hboundIntegrable
  exact hderivative.2.congr_deriv (integral_semilinearWaveEnergyBalanceResidual_timeSpaceCons_eq
    hV hu.self_of_nhds hderivative.1 hfluxCompact).symm

/-- For a classical solution with compactly supported fixed-time flux, the
time derivative of the energy density is spatially integrable. -/
theorem integrable_semilinearWaveSpatialEnergyTimeDerivative_of_solution {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {t : ℝ} (hV : ContDiff ℝ 1 V)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x))
    (hwave : ∀ x, semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hfluxCompact : ∀ i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t)) :
    Integrable (semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t) :=
  (integrable_sum_partialDeriv_flux hu hfluxCompact).congr (.of_forall fun x ↦
    (semilinearWaveSpatialEnergyTimeDerivative_eq_sum_partialDeriv_flux hV (hu x) (hwave x)).symm)

/-- For a classical solution with compactly supported fixed-time flux, the
spatial integral of the time derivative of the energy density vanishes. -/
theorem integral_semilinearWaveSpatialEnergyTimeDerivative_eq_zero {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {t : ℝ} (hV : ContDiff ℝ 1 V)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x))
    (hwave : ∀ x, semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hfluxCompact : ∀ i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t)) :
    (∫ x, semilinearWaveSpatialEnergyTimeDerivative (n := n) V u t x) = 0 := by
  rw [← integral_semilinearWaveEnergyBalanceResidual_timeSpaceCons_eq hV hu
    (integrable_semilinearWaveSpatialEnergyTimeDerivative_of_solution hV hu hwave hfluxCompact)
    hfluxCompact]
  exact integral_eq_zero_of_ae
    (.of_forall fun x ↦ semilinearWaveEnergyBalanceResidual_eq_zero hV (hu x) (hwave x))

/-- At any fixed time, a classical solution satisfying the explicit
integrability, domination, and flux-decay hypotheses has zero global-energy
derivative. -/
theorem hasDerivAt_semilinearWaveSpatialEnergy_eq_zero {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ}
    {s : Set ℝ} {bound : ℝ^n → ℝ} (hV : ContDiff ℝ 1 V)
    (hu : ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hs : s ∈ 𝓝 t)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) V u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound)
    (hwave : ∀ x, semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hfluxCompact : ∀ i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t)) :
    HasDerivAt (semilinearWaveSpatialEnergy (n := n) V u) 0 t :=
  (hasDerivAt_semilinearWaveSpatialEnergy_eq_integral_balanceResidual hV hu hs henergyIntegrable
    hdominated hboundIntegrable hfluxCompact).congr_deriv (integral_eq_zero_of_ae <| .of_forall
      fun x ↦ semilinearWaveEnergyBalanceResidual_eq_zero hV (hu.self_of_nhds x) (hwave x))

end WaveEquation
