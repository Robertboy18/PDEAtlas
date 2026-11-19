/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.Model
import PDE.FDeriv.Calculus
import PDE.Analysis.Calculus.Prod.SliceDerivative

/-!
# Dynamically rescaled vorticity–streamfunction equations

We state the rescaled equation (2.8) of Chen and Hou independently of any particular
change of variables. Given rates `c_l`, `c_ω`, and `c_θ`, the transport
velocity is `c_l x + u` and the scalar equations are

```text
ω_t + (c_l x + u) · ∇ω = ∂₁θ + c_ω ω,
θ_t + (c_l x + u) · ∇θ = c_θ θ.
```

The transformation from the physical equations is proved separately in
`DynamicRescaling`; normalization at the origin is treated in
`Normalization`.

The residuals `rescaledVorticityResidual` and `rescaledTemperatureResidual` are the exact
algebraic defects of these equations. The `_closure` lemmas extend the equations, and their
first and second spatial derivatives, from an open domain to its closure by continuity.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.8).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open PDE (advectiveDerivative)

namespace Boussinesq

open IncompressibleFlow

set_option linter.missingDocs true

noncomputable section

/-- Transport velocity `c_l(t)x + u(x,t)` in rescaled coordinates. -/
def rescaledTransportVelocity
    (fields : VorticityStreamFields) (spatialRate : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ^2 :=
  spatialRate t • x + vorticityStreamVelocity fields x t

/-- Forming the rescaled transport velocity loses one spatial derivative from
the streamfunction. -/
theorem contDiff_rescaledTransportVelocity
    (fields : VorticityStreamFields) (spatialRate : ℝ → ℝ)
    (t : ℝ) {m : ℕ}
    (hstream : ContDiff ℝ (m + 1)
      (fun x ↦ fields.streamFunction x t)) :
    ContDiff ℝ m
      (fun x ↦ rescaledTransportVelocity fields spatialRate x t) := by
  have hlinear : ContDiff ℝ m
      (fun x : ℝ^2 ↦ spatialRate t • x) := by
    fun_prop
  exact hlinear.add
    (contDiff_planarStreamVelocity
      (fun x ↦ fields.streamFunction x t) hstream)

/-- Pointwise defect in the dynamically rescaled vorticity equation. Exact
solutions have zero defect. -/
def rescaledVorticityResidual
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.vorticity x s) t +
      advectiveDerivative
        (fun y ↦ rescaledTransportVelocity fields spatialRate y t)
        (fun y ↦ fields.vorticity y t) x -
    (vorticityRate t * fields.vorticity x t +
      (∂[(0 : Fin 2)] (fun y ↦ fields.temperature y t)) x)

/-- Pointwise defect in the dynamically rescaled temperature equation. -/
def rescaledTemperatureResidual
    (fields : VorticityStreamFields)
    (spatialRate temperatureRate : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.temperature x s) t +
      advectiveDerivative
        (fun y ↦ rescaledTransportVelocity fields spatialRate y t)
        (fun y ↦ fields.temperature y t) x -
    temperatureRate t * fields.temperature x t

/-- Rescaled vorticity equation on a spatial domain at one time. -/
def SatisfiesRescaledVorticityEquationAtTime
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (t : ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄, x ∈ domain →
    deriv (fun s ↦ fields.vorticity x s) t +
        advectiveDerivative
          (fun y ↦ rescaledTransportVelocity fields spatialRate y t)
          (fun y ↦ fields.vorticity y t) x =
      vorticityRate t * fields.vorticity x t +
        (∂[(0 : Fin 2)] (fun y ↦ fields.temperature y t)) x

/-- The exact rescaled vorticity equation is equivalent to vanishing of its
pointwise residual on the domain. -/
theorem satisfiesRescaledVorticityEquationAtTime_iff_residual_eq_zero
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (t : ℝ) :
    SatisfiesRescaledVorticityEquationAtTime fields
        spatialRate vorticityRate domain t ↔
      ∀ ⦃x : ℝ^2⦄, x ∈ domain →
        rescaledVorticityResidual fields spatialRate vorticityRate x t = 0 := by
  constructor <;> intro h x hx
  · unfold rescaledVorticityResidual
    rw [h hx]
    ring
  · have hzero := h hx
    unfold rescaledVorticityResidual at hzero
    linarith

/-- Rescaled vorticity equation on a spatial domain and set of times. -/
def SatisfiesRescaledVorticityEquationOn
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ times →
    SatisfiesRescaledVorticityEquationAtTime fields
      spatialRate vorticityRate domain t

/-- Rescaled temperature equation on a spatial domain at one time. -/
def SatisfiesRescaledTemperatureEquationAtTime
    (fields : VorticityStreamFields)
    (spatialRate temperatureRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (t : ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄, x ∈ domain →
    deriv (fun s ↦ fields.temperature x s) t +
        advectiveDerivative
          (fun y ↦ rescaledTransportVelocity fields spatialRate y t)
          (fun y ↦ fields.temperature y t) x =
      temperatureRate t * fields.temperature x t

/-- The exact rescaled temperature equation is equivalent to vanishing of its
pointwise residual on the domain. -/
theorem satisfiesRescaledTemperatureEquationAtTime_iff_residual_eq_zero
    (fields : VorticityStreamFields)
    (spatialRate temperatureRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (t : ℝ) :
    SatisfiesRescaledTemperatureEquationAtTime fields
        spatialRate temperatureRate domain t ↔
      ∀ ⦃x : ℝ^2⦄, x ∈ domain →
        rescaledTemperatureResidual fields spatialRate temperatureRate x t = 0 := by
  constructor <;> intro h x hx
  · unfold rescaledTemperatureResidual
    rw [h hx]
    ring
  · have hzero := h hx
    unfold rescaledTemperatureResidual at hzero
    linarith

/-- Rescaled temperature equation on a spatial domain and set of times. -/
def SatisfiesRescaledTemperatureEquationOn
    (fields : VorticityStreamFields)
    (spatialRate temperatureRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ times →
    SatisfiesRescaledTemperatureEquationAtTime fields
      spatialRate temperatureRate domain t

/-- Both scalar equations of the rescaled system on a space–time domain. -/
def SatisfiesRescaledScalarEquationsOn
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate temperatureRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  SatisfiesRescaledVorticityEquationOn fields spatialRate vorticityRate
      domain times ∧
    SatisfiesRescaledTemperatureEquationOn fields spatialRate temperatureRate
      domain times

namespace SatisfiesRescaledScalarEquationsOn

/-- Extract the vorticity equation from the paired scalar equations. -/
theorem vorticity_equation
    {fields : VorticityStreamFields}
    {spatialRate vorticityRate temperatureRate : ℝ → ℝ}
    {domain : Set (ℝ^2)} {times : Set ℝ}
    (h : SatisfiesRescaledScalarEquationsOn fields
      spatialRate vorticityRate temperatureRate domain times) :
    SatisfiesRescaledVorticityEquationOn fields spatialRate vorticityRate
      domain times :=
  h.1

/-- Extract the temperature equation from the paired scalar equations. -/
theorem temperature_equation
    {fields : VorticityStreamFields}
    {spatialRate vorticityRate temperatureRate : ℝ → ℝ}
    {domain : Set (ℝ^2)} {times : Set ℝ}
    (h : SatisfiesRescaledScalarEquationsOn fields
      spatialRate vorticityRate temperatureRate domain times) :
    SatisfiesRescaledTemperatureEquationOn fields spatialRate temperatureRate
      domain times :=
  h.2

end SatisfiesRescaledScalarEquationsOn

/-- A rescaled vorticity equation with jointly `C¹` scalars and a spatially `C¹`
streamfunction extends continuously to the closure of its spatial domain. -/
theorem satisfiesRescaledVorticityEquationAtTime_closure
    (fields : VorticityStreamFields)
    (spatialRate vorticityRate : ℝ → ℝ) (t : ℝ)
    {domain : Set (ℝ^2)}
    (hωJoint : ContDiff ℝ 1
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2))
    (hθJoint : ContDiff ℝ 1
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ContDiff ℝ 1 (fun x ↦ fields.streamFunction x t))
    (hequation : SatisfiesRescaledVorticityEquationAtTime fields
      spatialRate vorticityRate domain t) :
    SatisfiesRescaledVorticityEquationAtTime fields
      spatialRate vorticityRate (closure domain) t := by
  intro x hx
  let transport : ℝ^2 → ℝ^2 := fun y ↦
    rescaledTransportVelocity fields spatialRate y t
  let ω : ℝ^2 → ℝ := fun y ↦ fields.vorticity y t
  let θ : ℝ^2 → ℝ := fun y ↦ fields.temperature y t
  have hωSpatial : ContDiff ℝ 1 ω := by
    simpa [ω, Function.comp_def] using hωJoint.comp
      (contDiff_id.prodMk contDiff_const)
  have hθSpatial : ContDiff ℝ 1 θ := by
    simpa [θ, Function.comp_def] using hθJoint.comp
      (contDiff_id.prodMk contDiff_const)
  have htransport : ContDiff ℝ 0 transport :=
    contDiff_rescaledTransportVelocity fields spatialRate t hstream
  have htime : ContDiff ℝ 0
      (fun y ↦ deriv (fun s ↦ fields.vorticity y s) t) := by
    simpa using PDE.contDiff_deriv_prod_timeSlice
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2) t hωJoint
  have hadvection : ContDiff ℝ 0
      (fun y ↦ advectiveDerivative transport ω y) :=
    (hωSpatial.fderiv_right (m := 0) (n := 1)
      (by norm_num)).clm_apply htransport
  have hsource : ContDiff ℝ 0
      (fun y ↦ (∂[(0 : Fin 2)] θ) y) :=
    PDE.contDiff_partialDeriv_of_succ (m := 0) hθSpatial
  have heqOn : Set.EqOn
      (fun y ↦ deriv (fun s ↦ fields.vorticity y s) t +
        advectiveDerivative transport ω y)
      (fun y ↦ vorticityRate t * ω y +
        (∂[(0 : Fin 2)] θ) y) domain := by
    intro y hy
    exact hequation hy
  exact (heqOn.closure (htime.add hadvection).continuous
    ((hωSpatial.const_smul (vorticityRate t)).of_le
      (by norm_num) |>.add hsource).continuous) hx

/-- A rescaled temperature equation with jointly `C¹` temperature and a spatially `C¹`
streamfunction extends continuously to the closure of its spatial domain. -/
theorem satisfiesRescaledTemperatureEquationAtTime_closure
    (fields : VorticityStreamFields)
    (spatialRate temperatureRate : ℝ → ℝ) (t : ℝ)
    {domain : Set (ℝ^2)}
    (hθJoint : ContDiff ℝ 1
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ContDiff ℝ 1 (fun x ↦ fields.streamFunction x t))
    (hequation : SatisfiesRescaledTemperatureEquationAtTime fields
      spatialRate temperatureRate domain t) :
    SatisfiesRescaledTemperatureEquationAtTime fields
      spatialRate temperatureRate (closure domain) t := by
  intro x hx
  let transport : ℝ^2 → ℝ^2 := fun y ↦
    rescaledTransportVelocity fields spatialRate y t
  let θ : ℝ^2 → ℝ := fun y ↦ fields.temperature y t
  have hθSpatial : ContDiff ℝ 1 θ := by
    simpa [θ, Function.comp_def] using hθJoint.comp
      (contDiff_id.prodMk contDiff_const)
  have htransport : ContDiff ℝ 0 transport :=
    contDiff_rescaledTransportVelocity fields spatialRate t hstream
  have htime : ContDiff ℝ 0
      (fun y ↦ deriv (fun s ↦ fields.temperature y s) t) := by
    simpa using PDE.contDiff_deriv_prod_timeSlice
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2) t hθJoint
  have hadvection : ContDiff ℝ 0
      (fun y ↦ advectiveDerivative transport θ y) :=
    (hθSpatial.fderiv_right (m := 0) (n := 1)
      (by norm_num)).clm_apply htransport
  have heqOn : Set.EqOn
      (fun y ↦ deriv (fun s ↦ fields.temperature y s) t +
        advectiveDerivative transport θ y)
      (fun y ↦ temperatureRate t * θ y) domain := by
    intro y hy
    exact hequation hy
  have hright : ContDiff ℝ 0
      (fun y ↦ temperatureRate t * θ y) := by
    exact (hθSpatial.const_smul (temperatureRate t)).of_le (by norm_num)
  simpa [transport, θ] using
    (heqOn.closure (htime.add hadvection).continuous hright.continuous) hx

/-- On an open spatial domain, one spatial derivative of the smooth rescaled
vorticity equation extends as an equality on the closure. -/
theorem partialDeriv_rescaledVorticityEquationAtTime_eq_on_closure
    (i : Fin 2) (fields : VorticityStreamFields)
    (spatialRate vorticityRate : ℝ → ℝ) (t : ℝ)
    {domain : Set (ℝ^2)} (hdomain : IsOpen domain)
    (hωJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2))
    (hθJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t))
    (hequation : SatisfiesRescaledVorticityEquationAtTime fields
      spatialRate vorticityRate domain t) :
    Set.EqOn
      (fun x ↦ (∂[i]
        (fun y ↦ deriv (fun s ↦ fields.vorticity y s) t +
          advectiveDerivative
            (fun z ↦ rescaledTransportVelocity fields spatialRate z t)
            (fun z ↦ fields.vorticity z t) y)) x)
      (fun x ↦ (∂[i]
        (fun y ↦ vorticityRate t * fields.vorticity y t +
          (∂[(0 : Fin 2)]
            (fun z ↦ fields.temperature z t)) y)) x)
      (closure domain) := by
  let transport : ℝ^2 → ℝ^2 := fun y ↦
    rescaledTransportVelocity fields spatialRate y t
  let ω : ℝ^2 → ℝ := fun y ↦ fields.vorticity y t
  let θ : ℝ^2 → ℝ := fun y ↦ fields.temperature y t
  have hωSpatial : ContDiff ℝ 2 ω := by
    simpa [ω, Function.comp_def] using hωJoint.comp
      (contDiff_id.prodMk contDiff_const)
  have hθSpatial : ContDiff ℝ 2 θ := by
    simpa [θ, Function.comp_def] using hθJoint.comp
      (contDiff_id.prodMk contDiff_const)
  have htransport : ContDiff ℝ 1 transport :=
    contDiff_rescaledTransportVelocity fields spatialRate t hstream
  have htime : ContDiff ℝ 1
      (fun y ↦ deriv (fun s ↦ fields.vorticity y s) t) := by
    simpa using PDE.contDiff_deriv_prod_timeSlice
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2) t hωJoint
  have hadvection : ContDiff ℝ 1
      (fun y ↦ advectiveDerivative transport ω y) :=
    (hωSpatial.fderiv_right (m := 1) (n := 2)
      (by norm_num)).clm_apply htransport
  have hsource : ContDiff ℝ 1
      (fun y ↦ (∂[(0 : Fin 2)] θ) y) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) hθSpatial
  have heqOn : Set.EqOn
      (fun y ↦ deriv (fun s ↦ fields.vorticity y s) t +
        advectiveDerivative transport ω y)
      (fun y ↦ vorticityRate t * ω y +
        (∂[(0 : Fin 2)] θ) y) domain := by
    intro y hy
    exact hequation hy
  exact PDE.partialDeriv_eq_on_closure_of_eqOn_open i hdomain
    (htime.add hadvection)
    ((hωSpatial.const_smul (vorticityRate t)).of_le
      (by norm_num) |>.add hsource) heqOn

/-- On an open spatial domain, two spatial derivatives of the smooth rescaled
temperature equation extend as an equality on the closure. -/
theorem secondPartialDeriv_rescaledTemperatureEquationAtTime_eq_on_closure
    (i j : Fin 2) (fields : VorticityStreamFields)
    (spatialRate temperatureRate : ℝ → ℝ) (t : ℝ)
    {domain : Set (ℝ^2)} (hdomain : IsOpen domain)
    (hθJoint : ContDiff ℝ 3
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hstream : ContDiff ℝ 3 (fun x ↦ fields.streamFunction x t))
    (hequation : SatisfiesRescaledTemperatureEquationAtTime fields
      spatialRate temperatureRate domain t) :
    Set.EqOn
      (fun x ↦ (∂[i]
        (fun y ↦ (∂[j]
          (fun z ↦ deriv (fun s ↦ fields.temperature z s) t +
            advectiveDerivative
              (fun q ↦ rescaledTransportVelocity fields spatialRate q t)
              (fun q ↦ fields.temperature q t) z)) y)) x)
      (fun x ↦ (∂[i]
        (fun y ↦ (∂[j]
          (fun z ↦ temperatureRate t * fields.temperature z t)) y)) x)
      (closure domain) := by
  let transport : ℝ^2 → ℝ^2 := fun y ↦
    rescaledTransportVelocity fields spatialRate y t
  let θ : ℝ^2 → ℝ := fun y ↦ fields.temperature y t
  have hθSpatial : ContDiff ℝ 3 θ := by
    simpa [θ, Function.comp_def] using hθJoint.comp
      (contDiff_id.prodMk contDiff_const)
  have htransport : ContDiff ℝ 2 transport :=
    contDiff_rescaledTransportVelocity fields spatialRate t hstream
  have htime : ContDiff ℝ 2
      (fun y ↦ deriv (fun s ↦ fields.temperature y s) t) := by
    simpa using PDE.contDiff_deriv_prod_timeSlice
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2) t hθJoint
  have hadvection : ContDiff ℝ 2
      (fun y ↦ advectiveDerivative transport θ y) :=
    (hθSpatial.fderiv_right (m := 2) (n := 3)
      (by norm_num)).clm_apply htransport
  have heqOn : Set.EqOn
      (fun y ↦ deriv (fun s ↦ fields.temperature y s) t +
        advectiveDerivative transport θ y)
      (fun y ↦ temperatureRate t * θ y) domain := by
    intro y hy
    exact hequation hy
  exact PDE.secondPartialDeriv_eq_on_closure_of_eqOn_open i j
    hdomain (htime.add hadvection)
    ((hθSpatial.const_smul (temperatureRate t)).of_le
      (by norm_num)) heqOn

end

end Boussinesq
