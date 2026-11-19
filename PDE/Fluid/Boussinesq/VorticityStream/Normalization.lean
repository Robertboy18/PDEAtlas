/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.RescaledSystem
public import PDE.Fluid.Boussinesq.VorticityStream.Symmetry
import PDE.FDeriv.SpaceTime
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Normalization of the dynamic rescaling at the origin

Chen and Hou fix the rescaling rates by the normalization (2.9)–(2.10) at the origin, and the
footnote that follows derives ODEs for the traces `ω_x(0)` and `θ_xx(0)`. The normalization is

```text
c_l = 2 θ_xx(0) / ω_x(0),
c_ω = c_l / 2 + u_x(0),
c_θ = c_l + 2 c_ω.
```

The denominator condition `ω_x(0) ≠ 0` is explicit. The ODE derivation uses
global smooth extensions so that mixed space–time derivatives commute. The
rescaled equations themselves are assumed only on the open upper half-plane;
their differentiated identities are extended continuously to the origin.

## Main results

* `SatisfiesRescalingNormalizationAt`: the three normalization identities at one time.
* `deriv_vorticityXAtOrigin`, `deriv_temperatureXXAtOrigin`: the two trace ODEs.
* `deriv_vorticityXAtOrigin_eq_zero`, `deriv_temperatureXXAtOrigin_eq_zero`: under the
  normalization both traces are stationary, and `vorticityXAtOrigin_eqOn_const`,
  `temperatureXXAtOrigin_eqOn_const` integrate this on an open connected time set.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.9)-(2.10) and
  footnote 3.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open PDE (advectiveDerivative)

namespace Boussinesq

open IncompressibleFlow
open PDE.Common

set_option linter.missingDocs true

noncomputable section

/-- Horizontal derivative of vorticity at the origin. -/
def vorticityXAtOrigin
    (fields : VorticityStreamFields) (t : ℝ) : ℝ :=
  (∂[(0 : Fin 2)] (fun x ↦ fields.vorticity x t)) 0

/-- Second horizontal derivative of temperature at the origin. -/
def temperatureXXAtOrigin
    (fields : VorticityStreamFields) (t : ℝ) : ℝ :=
  (∂[(0 : Fin 2)]
    (fun x ↦ (∂[(0 : Fin 2)]
      (fun y ↦ fields.temperature y t)) x)) 0

/-- Horizontal derivative of the tangential velocity at the origin. -/
def tangentialVelocityXAtOrigin
    (fields : VorticityStreamFields) (t : ℝ) : ℝ :=
  (∂[(0 : Fin 2)]
    (fun x ↦ vorticityStreamVelocity fields x t 0)) 0

/-- The three normalization identities of the dynamic rescaling at one time: the dilation
rate is `2 θ_xx(0)/ω_x(0)`, the vorticity amplitude rate is half of it plus `u_x(0)`, and
the temperature amplitude rate is the dilation rate plus twice the vorticity rate. These are
the conditions (2.9) of Chen and Hou. -/
structure SatisfiesRescalingNormalizationAt
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate temperatureRate : ℝ → ℝ)
    (t : ℝ) : Prop where
  /-- The vorticity trace used as the denominator is nonzero. -/
  vorticity_x_at_origin_ne_zero :
    vorticityXAtOrigin fields t ≠ 0
  /-- The spatial dilation rate is fixed by the two origin traces. -/
  spatial_rate_eq :
    spatialRate t =
      2 * temperatureXXAtOrigin fields t / vorticityXAtOrigin fields t
  /-- The vorticity amplitude rate is fixed by dilation and velocity strain. -/
  vorticity_rate_eq :
    vorticityRate t =
      spatialRate t / 2 + tangentialVelocityXAtOrigin fields t
  /-- The temperature amplitude rate satisfies the scaling compatibility law. -/
  temperature_rate_eq :
    temperatureRate t = spatialRate t + 2 * vorticityRate t

private theorem rescaledTransportVelocity_origin
    (fields : VorticityStreamFields) (spatialRate : ℝ → ℝ) (t : ℝ)
    (hvelocity : vorticityStreamVelocity fields 0 t = 0) :
    rescaledTransportVelocity fields spatialRate 0 t = 0 := by
  simp [rescaledTransportVelocity, hvelocity]

private theorem partialDeriv_zero_rescaledTransportVelocity_zero
    (fields : VorticityStreamFields) (spatialRate : ℝ → ℝ) (t : ℝ)
    (hstream : ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t)) :
    (∂[(0 : Fin 2)]
        (fun x ↦ rescaledTransportVelocity fields spatialRate x t 0)) 0 =
      spatialRate t + tangentialVelocityXAtOrigin fields t := by
  have hvelocity := contDiff_planarStreamVelocity
    (fun x ↦ fields.streamFunction x t) hstream
  rw [show
      (fun x ↦ rescaledTransportVelocity fields spatialRate x t 0) =
        fun x ↦ spatialRate t * x 0 +
          vorticityStreamVelocity fields x t 0 by
    funext x
    simp [rescaledTransportVelocity, smul_eq_mul]]
  rw [PDE.partialDeriv_add]
  · have hscale :
        (∂[(0 : Fin 2)]
            (fun x : ℝ^2 ↦ spatialRate t * x 0)) 0 = spatialRate t := by
      cas
    rw [hscale]
    rfl
  · fun_prop
  · exact (((contDiff_piLp (p := (2 : ENNReal))).1 hvelocity 0).differentiable
      (by norm_num)).differentiableAt

private theorem partialDeriv_zero_rescaledTransportVelocity_one
    (fields : VorticityStreamFields) (spatialRate : ℝ → ℝ) (t : ℝ)
    (hstream : ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t)) :
    (∂[(0 : Fin 2)]
        (fun x ↦ rescaledTransportVelocity fields spatialRate x t 1)) 0 =
      (∂[(0 : Fin 2)]
        (fun x ↦ vorticityStreamVelocity fields x t 1)) 0 := by
  have hvelocity := contDiff_planarStreamVelocity
    (fun x ↦ fields.streamFunction x t) hstream
  rw [show
      (fun x ↦ rescaledTransportVelocity fields spatialRate x t 1) =
        fun x ↦ spatialRate t * x 1 +
          vorticityStreamVelocity fields x t 1 by
    funext x
    simp [rescaledTransportVelocity, smul_eq_mul]]
  rw [PDE.partialDeriv_add]
  · have hscale :
        (∂[(0 : Fin 2)]
            (fun x : ℝ^2 ↦ spatialRate t * x 1)) 0 = 0 := by
      cas
    rw [hscale, zero_add]
  · fun_prop
  · exact (((contDiff_piLp (p := (2 : ENNReal))).1 hvelocity 1).differentiable
      (by norm_num)).differentiableAt

/-- At the origin the rescaled transport velocity vanishes, its horizontal component has
horizontal derivative `c_l + u_x(0)` and its vertical component horizontal derivative `0`. -/
private theorem rescaledTransportVelocity_origin_data
    (fields : VorticityStreamFields) (spatialRate : ℝ → ℝ) (t : ℝ)
    (hstream : ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t))
    (hsymmetry : HasReflectionSymmetryAtTime fields t) :
    rescaledTransportVelocity fields spatialRate 0 t = 0 ∧
      (∂[(0 : Fin 2)] (fun x ↦ rescaledTransportVelocity fields spatialRate x t 0)) 0 =
        spatialRate t + tangentialVelocityXAtOrigin fields t ∧
      (∂[(0 : Fin 2)] (fun x ↦ rescaledTransportVelocity fields spatialRate x t 1)) 0 = 0 := by
  have hvelocity : ContDiff ℝ 1 (fun x ↦ vorticityStreamVelocity fields x t) :=
    contDiff_planarStreamVelocity (fun x ↦ fields.streamFunction x t) hstream
  refine ⟨rescaledTransportVelocity_origin fields spatialRate t
      hsymmetry.vorticityStreamVelocity_origin_eq_zero,
    partialDeriv_zero_rescaledTransportVelocity_zero fields spatialRate t hstream, ?_⟩
  rw [partialDeriv_zero_rescaledTransportVelocity_one fields spatialRate t hstream]
  exact hsymmetry.partialDeriv_zero_normal_velocity_at_origin_eq_zero
    (((contDiff_piLp (p := (2 : ENNReal))).1 hvelocity 1).differentiable
      (by norm_num)).differentiableAt

private theorem partialDeriv_const_mul_apply (c : ℝ) (i : Fin 2) (f : ℝ^2 → ℝ) (x : ℝ^2) :
    (∂[i] (fun y ↦ c * f y)) x = c * (∂[i] f) x := by
  simpa only [smul_eq_mul] using PDE.partialDeriv_const_smul c (i := i) (f := f) (x := x)

/-- The first origin-trace ODE from the footnote following equation (2.10).
Second-order regularity suffices for this first spatial derivative of the vorticity equation. -/
theorem deriv_vorticityXAtOrigin
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate : ℝ → ℝ) (t : ℝ)
    (hωJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2))
    (hθJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t))
    (hequation : SatisfiesRescaledVorticityEquationAtTime fields
      spatialRate vorticityRate upperHalfPlane t)
    (hsymmetry : HasReflectionSymmetryAtTime fields t) :
    deriv (vorticityXAtOrigin fields) t =
      (vorticityRate t - spatialRate t -
          tangentialVelocityXAtOrigin fields t) *
        vorticityXAtOrigin fields t +
      temperatureXXAtOrigin fields t := by
  let ω : ℝ^2 → ℝ := fun x ↦ fields.vorticity x t
  let θ : ℝ^2 → ℝ := fun x ↦ fields.temperature x t
  let transport : ℝ^2 → ℝ^2 := fun x ↦ rescaledTransportVelocity fields spatialRate x t
  have hωSpatial : ContDiff ℝ 2 ω := hωJoint.comp (contDiff_id.prodMk contDiff_const)
  have hθSpatial : ContDiff ℝ 2 θ := hθJoint.comp (contDiff_id.prodMk contDiff_const)
  have htransport : ContDiff ℝ 1 transport :=
    contDiff_rescaledTransportVelocity fields spatialRate t hstream
  obtain ⟨htransportZero, htransportXZero, htransportXOne⟩ :=
    rescaledTransportVelocity_origin_data fields spatialRate t hstream hsymmetry
  have hωyZero : (∂[(1 : Fin 2)] ω) 0 = 0 :=
    hsymmetry.partialDeriv_one_vorticity_at_origin_eq_zero
      ((hωSpatial.differentiable (by norm_num)).differentiableAt)
  have hadvection : ContDiff ℝ 1 (fun x ↦ advectiveDerivative transport ω x) :=
    (hωSpatial.fderiv_right (m := 1) (n := 2) (by norm_num)).clm_apply htransport
  have htime : ContDiff ℝ 1 (fun x ↦ deriv (fun s ↦ fields.vorticity x s) t) := by
    simpa using PDE.contDiff_deriv_prod_timeSlice
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2) t hωJoint
  have hrate : ContDiff ℝ 1 (fun x ↦ vorticityRate t * ω x) :=
    (hωSpatial.const_smul (vorticityRate t)).of_le (by norm_num)
  have hθx : ContDiff ℝ 1 (∂[(0 : Fin 2)] θ) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) hθSpatial
  -- the horizontal derivative of the vorticity equation, at the origin
  have hpde := partialDeriv_rescaledVorticityEquationAtTime_eq_on_closure (0 : Fin 2) fields
    spatialRate vorticityRate t isOpen_upperHalfPlane hωJoint hθJoint hstream hequation
    (show (0 : ℝ^2) ∈ closure upperHalfPlane by simp [closure_upperHalfPlane])
  change (∂[(0 : Fin 2)] (fun x ↦ deriv (fun s ↦ fields.vorticity x s) t +
      advectiveDerivative transport ω x)) 0 =
    (∂[(0 : Fin 2)] (fun x ↦ vorticityRate t * ω x + (∂[(0 : Fin 2)] θ) x)) 0 at hpde
  rw [PDE.partialDeriv_add (htime.differentiable (by norm_num)).differentiableAt
      (hadvection.differentiable (by norm_num)).differentiableAt,
    PDE.partialDeriv_add (hrate.differentiable (by norm_num)).differentiableAt
      (hθx.differentiable (by norm_num)).differentiableAt] at hpde
  unfold vorticityXAtOrigin
  rw [PDE.deriv_partialDeriv_timeSlice_comm (0 : Fin 2)
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2) 0 t hωJoint, eq_sub_of_add_eq hpde,
    PDE.partialDeriv_advectiveDerivative (0 : Fin 2) transport ω 0 htransport.contDiffAt
      hωSpatial.contDiffAt]
  simp only [partialDeriv_const_mul_apply, Fin.sum_univ_two, transport, θ, htransportZero,
    htransportXZero, htransportXOne, hωyZero, PiLp.zero_apply, zero_mul, mul_zero, add_zero,
    temperatureXXAtOrigin, tangentialVelocityXAtOrigin]
  ring

/-- The second origin-trace ODE from the footnote following equation (2.10). -/
theorem deriv_temperatureXXAtOrigin
    (fields : VorticityStreamFields)
    (spatialRate temperatureRate : ℝ → ℝ) (t : ℝ)
    (hθJoint : ContDiff ℝ 3
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ContDiff ℝ 3 (fun x ↦ fields.streamFunction x t))
    (hequation : SatisfiesRescaledTemperatureEquationAtTime fields
      spatialRate temperatureRate upperHalfPlane t)
    (hsymmetry : HasReflectionSymmetryAtTime fields t) :
    deriv (temperatureXXAtOrigin fields) t =
      (temperatureRate t -
          2 * (spatialRate t + tangentialVelocityXAtOrigin fields t)) *
        temperatureXXAtOrigin fields t := by
  let θ : ℝ^2 → ℝ := fun x ↦ fields.temperature x t
  let transport : ℝ^2 → ℝ^2 := fun x ↦ rescaledTransportVelocity fields spatialRate x t
  have hθSpatial : ContDiff ℝ 3 θ := hθJoint.comp (contDiff_id.prodMk contDiff_const)
  have htransport : ContDiff ℝ 2 transport :=
    contDiff_rescaledTransportVelocity fields spatialRate t hstream
  obtain ⟨htransportZero, htransportXZero, htransportXOne⟩ :=
    rescaledTransportVelocity_origin_data fields spatialRate t (hstream.of_le (by norm_num))
      hsymmetry
  have hθxZero : (∂[(0 : Fin 2)] θ) 0 = 0 :=
    hsymmetry.partialDeriv_zero_temperature_at_origin_eq_zero
      ((hθSpatial.differentiable (by norm_num)).differentiableAt)
  have hθyZero : (∂[(1 : Fin 2)] θ) 0 = 0 :=
    hsymmetry.partialDeriv_one_temperature_at_origin_eq_zero
      ((hθSpatial.differentiable (by norm_num)).differentiableAt)
  have hadvection : ContDiff ℝ 2 (fun x ↦ advectiveDerivative transport θ x) :=
    (hθSpatial.fderiv_right (m := 2) (n := 3) (by norm_num)).clm_apply htransport
  have htime : ContDiff ℝ 2 (fun x ↦ deriv (fun s ↦ fields.temperature x s) t) := by
    simpa using PDE.contDiff_deriv_prod_timeSlice
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2) t hθJoint
  -- the second horizontal derivative of the temperature equation, at the origin
  have hpde := secondPartialDeriv_rescaledTemperatureEquationAtTime_eq_on_closure (0 : Fin 2)
    (0 : Fin 2) fields spatialRate temperatureRate t isOpen_upperHalfPlane hθJoint hstream
    hequation (show (0 : ℝ^2) ∈ closure upperHalfPlane by simp [closure_upperHalfPlane])
  change (∂[(0 : Fin 2)] (fun y ↦ (∂[(0 : Fin 2)] (fun x ↦
      deriv (fun s ↦ fields.temperature x s) t + advectiveDerivative transport θ x)) y)) 0 =
    (∂[(0 : Fin 2)] (fun y ↦ (∂[(0 : Fin 2)] (fun x ↦ temperatureRate t * θ x)) y)) 0 at hpde
  rw [PDE.secondPartialDeriv_add (0 : Fin 2) (0 : Fin 2) htime.contDiffAt
    hadvection.contDiffAt] at hpde
  unfold temperatureXXAtOrigin
  rw [PDE.deriv_secondPartialDeriv_timeSlice_comm (0 : Fin 2) (0 : Fin 2)
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2) 0 t hθJoint, eq_sub_of_add_eq hpde,
    PDE.secondPartialDeriv_advectiveDerivative (0 : Fin 2) (0 : Fin 2) transport θ 0
      htransport.contDiffAt hθSpatial.contDiffAt]
  simp only [partialDeriv_const_mul_apply, Fin.sum_univ_two, transport, θ, htransportZero,
    htransportXZero, htransportXOne, hθxZero, hθyZero, PiLp.zero_apply, zero_mul, mul_zero,
    zero_add, add_zero, tangentialVelocityXAtOrigin]
  ring

/-- The first trace-ODE right-hand side vanishes under the normalization
identities. -/
theorem vorticity_trace_ode_rhs_eq_zero_of_normalization
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate temperatureRate : ℝ → ℝ) (t : ℝ)
    (hnormalization : SatisfiesRescalingNormalizationAt fields
      spatialRate vorticityRate temperatureRate t) :
    (vorticityRate t - spatialRate t -
          tangentialVelocityXAtOrigin fields t) *
        vorticityXAtOrigin fields t +
      temperatureXXAtOrigin fields t = 0 := by
  have hrelation :
      spatialRate t * vorticityXAtOrigin fields t =
        2 * temperatureXXAtOrigin fields t := by
    rw [hnormalization.spatial_rate_eq]
    field_simp [hnormalization.vorticity_x_at_origin_ne_zero]
  rw [hnormalization.vorticity_rate_eq]
  nlinarith

/-- The second trace-ODE right-hand side vanishes under the normalization
identities. -/
theorem temperature_trace_ode_rhs_eq_zero_of_normalization
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate temperatureRate : ℝ → ℝ) (t : ℝ)
    (hnormalization : SatisfiesRescalingNormalizationAt fields
      spatialRate vorticityRate temperatureRate t) :
    (temperatureRate t -
          2 * (spatialRate t + tangentialVelocityXAtOrigin fields t)) *
        temperatureXXAtOrigin fields t = 0 := by
  rw [hnormalization.temperature_rate_eq, hnormalization.vorticity_rate_eq]
  ring

/-- At a smooth normalized solution, the vorticity origin trace has zero time
derivative. This is the first differential identity behind equation (2.10). -/
theorem deriv_vorticityXAtOrigin_eq_zero
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate temperatureRate : ℝ → ℝ) (t : ℝ)
    (hωJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2))
    (hθJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t))
    (hωEquation : SatisfiesRescaledVorticityEquationAtTime fields
      spatialRate vorticityRate upperHalfPlane t)
    (hsymmetry : HasReflectionSymmetryAtTime fields t)
    (hnormalization : SatisfiesRescalingNormalizationAt fields
      spatialRate vorticityRate temperatureRate t) :
    deriv (vorticityXAtOrigin fields) t = 0 := by
  rw [deriv_vorticityXAtOrigin fields spatialRate vorticityRate t hωJoint hθJoint hstream
    hωEquation hsymmetry]
  exact vorticity_trace_ode_rhs_eq_zero_of_normalization fields spatialRate vorticityRate
    temperatureRate t hnormalization

/-- At a smooth normalized solution, the temperature origin trace has zero
time derivative. This is the second differential identity behind equation
(2.10). -/
theorem deriv_temperatureXXAtOrigin_eq_zero
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate temperatureRate : ℝ → ℝ) (t : ℝ)
    (hθJoint : ContDiff ℝ 3
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ContDiff ℝ 3 (fun x ↦ fields.streamFunction x t))
    (hθEquation : SatisfiesRescaledTemperatureEquationAtTime fields
      spatialRate temperatureRate upperHalfPlane t)
    (hsymmetry : HasReflectionSymmetryAtTime fields t)
    (hnormalization : SatisfiesRescalingNormalizationAt fields
      spatialRate vorticityRate temperatureRate t) :
    deriv (temperatureXXAtOrigin fields) t = 0 := by
  rw [deriv_temperatureXXAtOrigin fields spatialRate temperatureRate t
    hθJoint hstream hθEquation hsymmetry]
  exact temperature_trace_ode_rhs_eq_zero_of_normalization
    fields spatialRate vorticityRate temperatureRate t hnormalization

/-- On an open connected time domain, the normalized vorticity origin trace
equals its value at any chosen reference time. -/
theorem vorticityXAtOrigin_eqOn_const
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate temperatureRate : ℝ → ℝ)
    (times : Set ℝ) (htimesOpen : IsOpen times)
    (htimesPreconnected : IsPreconnected times)
    (t₀ : ℝ) (ht₀ : t₀ ∈ times)
    (hωJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2))
    (hθJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ∀ ⦃t : ℝ⦄, t ∈ times →
      ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t))
    (hωEquation : SatisfiesRescaledVorticityEquationOn fields
      spatialRate vorticityRate upperHalfPlane times)
    (hsymmetry : ∀ ⦃t : ℝ⦄, t ∈ times →
      HasReflectionSymmetryAtTime fields t)
    (hnormalization : ∀ ⦃t : ℝ⦄, t ∈ times →
      SatisfiesRescalingNormalizationAt fields
        spatialRate vorticityRate temperatureRate t) :
    Set.EqOn (vorticityXAtOrigin fields)
      (fun _ ↦ vorticityXAtOrigin fields t₀) times := by
  have hωTrace : ContDiff ℝ 1 (vorticityXAtOrigin fields) :=
    PDE.contDiff_partialDeriv_timeTrace (0 : Fin 2)
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2) 0 hωJoint
  exact fun t ht ↦ htimesOpen.is_const_of_deriv_eq_zero htimesPreconnected
    (hωTrace.differentiable (by norm_num)).differentiableOn
    (fun s hs ↦ deriv_vorticityXAtOrigin_eq_zero fields spatialRate vorticityRate
      temperatureRate s hωJoint hθJoint (hstream hs) (hωEquation hs) (hsymmetry hs)
      (hnormalization hs)) ht ht₀

/-- On an open connected time domain, the normalized temperature origin trace
equals its value at any chosen reference time. -/
theorem temperatureXXAtOrigin_eqOn_const
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate temperatureRate : ℝ → ℝ)
    (times : Set ℝ) (htimesOpen : IsOpen times)
    (htimesPreconnected : IsPreconnected times)
    (t₀ : ℝ) (ht₀ : t₀ ∈ times)
    (hθJoint : ContDiff ℝ 3
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ∀ ⦃t : ℝ⦄, t ∈ times →
      ContDiff ℝ 3 (fun x ↦ fields.streamFunction x t))
    (hθEquation : SatisfiesRescaledTemperatureEquationOn fields
      spatialRate temperatureRate upperHalfPlane times)
    (hsymmetry : ∀ ⦃t : ℝ⦄, t ∈ times →
      HasReflectionSymmetryAtTime fields t)
    (hnormalization : ∀ ⦃t : ℝ⦄, t ∈ times →
      SatisfiesRescalingNormalizationAt fields
        spatialRate vorticityRate temperatureRate t) :
    Set.EqOn (temperatureXXAtOrigin fields)
      (fun _ ↦ temperatureXXAtOrigin fields t₀) times := by
  have hθTrace : ContDiff ℝ 1 (temperatureXXAtOrigin fields) :=
    PDE.contDiff_secondPartialDeriv_timeTrace (0 : Fin 2) (0 : Fin 2)
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2) 0 hθJoint
  exact fun t ht ↦ htimesOpen.is_const_of_deriv_eq_zero htimesPreconnected
    (hθTrace.differentiable (by norm_num)).differentiableOn
    (fun s hs ↦ deriv_temperatureXXAtOrigin_eq_zero fields spatialRate vorticityRate
      temperatureRate s hθJoint (hstream hs) (hθEquation hs) (hsymmetry hs)
      (hnormalization hs)) ht ht₀

end

end Boussinesq
