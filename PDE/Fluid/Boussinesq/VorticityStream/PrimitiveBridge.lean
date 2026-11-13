/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.Model
public import PDE.Fluid.Boussinesq.VorticityStream.Model
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.FDeriv.SpaceTime
import PDE.Fluid.Incompressible.VorticityTransport

/-!
# Primitive-variable and vorticity bridges for planar Boussinesq flow

Passing from a primitive velocity–pressure equation to clockwise scalar vorticity fixes the
sign of the buoyancy source. If the
primitive force is `κ θ e₂`, then clockwise curl gives the source
`-κ ∂₁θ`. Consequently, the Chen–Hou convention

```text
ω_t + u · ∇ω = ∂₁θ
```

corresponds to `κ = -1`, whereas upward buoyancy `κ = 1` gives the opposite
source sign.

"Downward buoyancy" below names the primitive-variable system with `κ = -1`,
which realizes this sign convention.

The results are local differential identities, and the streamfunction is an input
(`BoussinesqFields.toVorticityStreamFields_isClassicalSolutionOn`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2, (2.3a)-(2.3c).
  <https://arxiv.org/abs/2210.07191v4>
-/

open scoped Gradient

@[expose] public section

open PDE (laplacian advectiveDerivative)

namespace Boussinesq

open IncompressibleFlow

set_option linter.missingDocs true

noncomputable section

/-- The clockwise scalar vorticity associated with primitive Boussinesq
velocity fields. -/
def BoussinesqFields.clockwiseVorticity
    (fields : BoussinesqFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  spatialPlanarClockwiseVorticity (fun y ↦ fields.velocity y t) x

/-- The clockwise curl of the signed vertical buoyancy force is
`-κ ∂₁θ`. -/
theorem spatialPlanarClockwiseVorticity_buoyancyForceWithCoefficient
    (κ : ℝ) (theta : ℝ^2 → ℝ) (x : ℝ^2) :
    spatialPlanarClockwiseVorticity
        (fun y ↦ buoyancyForceWithCoefficient κ (theta y)) x =
      -κ * (∂[(0 : Fin 2)] theta) x := by
  unfold spatialPlanarClockwiseVorticity
  have hzero :
      (fun y ↦ buoyancyForceWithCoefficient κ (theta y) 0) =
        fun _ : ℝ^2 ↦ 0 := by
    funext y
    simp
  have hone :
      (fun y ↦ buoyancyForceWithCoefficient κ (theta y) 1) =
        fun y ↦ κ • theta y := by
    funext y
    simp [smul_eq_mul]
  rw [hzero, hone, PDE.partialDeriv_const, PDE.partialDeriv_const_smul]
  simp [smul_eq_mul]

/-- A primitive velocity with buoyancy coefficient `κ` satisfies the
clockwise vorticity equation with source `-κ ∂₁θ`.

The global `C²` assumptions provide the spatial and space–time mixed
derivatives used by the curl calculation. The primitive momentum equation is
needed only on an open neighborhood of the evaluation point. -/
theorem BoussinesqFields.clockwiseVorticity_equation_of_momentum
    (fields : BoussinesqFields) (κ t : ℝ)
    (spatialDomain : Set (ℝ^2))
    (hspatialDomain : IsOpen spatialDomain)
    (hvelocityJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.velocity xt.1 xt.2))
    (hpressure : ContDiff ℝ 2 (fun x ↦ fields.pressure x t))
    (htemperature : ContDiff ℝ 1 (fun x ↦ fields.temperature x t))
    (hdivergence : ∀ x ∈ spatialDomain,
      ∇· (fun y ↦ fields.velocity y t) x = 0)
    (hmomentum : ∀ x ∈ spatialDomain,
      deriv (fun s ↦ fields.velocity x s) t +
          advectiveDerivative
            (fun y ↦ fields.velocity y t)
            (fun y ↦ fields.velocity y t) x +
          ∇ (fun y ↦ fields.pressure y t) x =
        buoyancyForceWithCoefficient κ (fields.temperature x t))
    (x : ℝ^2) (hx : x ∈ spatialDomain) :
    deriv (fields.clockwiseVorticity x) t +
        advectiveDerivative
          (fun y ↦ fields.velocity y t)
          (fun y ↦ fields.clockwiseVorticity y t) x =
      -κ * (∂[(0 : Fin 2)]
        (fun y ↦ fields.temperature y t)) x := by
  have hforce : ContDiff ℝ 1
      (fun y ↦ buoyancyForceWithCoefficient κ (fields.temperature y t)) := by
    refine (contDiff_piLp (p := (2 : ENNReal))).2 fun i ↦ ?_
    fin_cases i
    · simpa [buoyancyForceWithCoefficient, buoyancyForce] using
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ^2 ↦ (0 : ℝ)))
    · simpa [buoyancyForceWithCoefficient, buoyancyForce, smul_eq_mul] using
        htemperature.const_smul κ
  have hcurl := spatialPlanarClockwiseVorticity_equation_of_momentum fields.velocity
    (fun y s ↦ buoyancyForceWithCoefficient κ (fields.temperature y s)) fields.pressure t
    spatialDomain hspatialDomain hvelocityJoint hpressure hforce hdivergence hmomentum x hx
  rw [spatialPlanarClockwiseVorticity_buoyancyForceWithCoefficient] at hcurl
  exact hcurl

/-- Downward buoyancy gives the positive horizontal temperature source used
in the Chen–Hou clockwise-vorticity convention. -/
theorem BoussinesqFields.clockwiseVorticity_equation_of_downwardMomentum
    (fields : BoussinesqFields) (t : ℝ)
    (spatialDomain : Set (ℝ^2))
    (hspatialDomain : IsOpen spatialDomain)
    (hvelocityJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.velocity xt.1 xt.2))
    (hpressure : ContDiff ℝ 2 (fun x ↦ fields.pressure x t))
    (htemperature : ContDiff ℝ 1 (fun x ↦ fields.temperature x t))
    (hdivergence : ∀ x ∈ spatialDomain,
      ∇· (fun y ↦ fields.velocity y t) x = 0)
    (hmomentum : ∀ x ∈ spatialDomain,
      deriv (fun s ↦ fields.velocity x s) t +
          advectiveDerivative
            (fun y ↦ fields.velocity y t)
            (fun y ↦ fields.velocity y t) x +
          ∇ (fun y ↦ fields.pressure y t) x =
        buoyancyForceWithCoefficient (-1) (fields.temperature x t))
    (x : ℝ^2) (hx : x ∈ spatialDomain) :
    deriv (fields.clockwiseVorticity x) t +
        advectiveDerivative
          (fun y ↦ fields.velocity y t)
          (fun y ↦ fields.clockwiseVorticity y t) x =
      (∂[(0 : Fin 2)]
        (fun y ↦ fields.temperature y t)) x := by
  simpa using fields.clockwiseVorticity_equation_of_momentum (-1) t
    spatialDomain hspatialDomain hvelocityJoint hpressure htemperature
    hdivergence hmomentum x hx

/-- Package primitive temperature, clockwise vorticity, and a chosen
streamfunction as upper-half-plane vorticity–stream fields. -/
def BoussinesqFields.toVorticityStreamFields
    (fields : BoussinesqFields) (streamFunction : ℝ^2 → ℝ → ℝ) :
    VorticityStreamFields where
  vorticity := fields.clockwiseVorticity
  temperature := fields.temperature
  streamFunction := streamFunction

/-- A sufficiently smooth downward-buoyancy primitive solution with a given
streamfunction induces a classical Chen–Hou vorticity–stream solution.

This is the differential passage from primitive momentum to the paper's clockwise
vorticity equation. The streamfunction is supplied together with the identity
`u = (-∂₂φ, ∂₁φ)`. -/
theorem BoussinesqFields.toVorticityStreamFields_isClassicalSolutionOn
    (fields : BoussinesqFields) (streamFunction : ℝ^2 → ℝ → ℝ)
    (times : Set ℝ)
    (hvelocityJoint : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ fields.velocity xt.1 xt.2))
    (htemperatureJoint : ContDiff ℝ 1
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2))
    (hpressure : ∀ ⦃t : ℝ⦄, t ∈ times →
      ContDiff ℝ 2 (fun x ↦ fields.pressure x t))
    (hstream : ∀ ⦃t : ℝ⦄, t ∈ times →
      ContDiff ℝ 2 (fun x ↦ streamFunction x t))
    (hvelocity : ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, t ∈ times →
      fields.velocity x t =
        planarStreamVelocity (fun y ↦ streamFunction y t) x)
    (hmomentum :
      SatisfiesMomentumEquationWithBuoyancyCoefficientOn
        fields (-1) upperHalfPlane times)
    (htemperatureEquation : ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄,
      x ∈ upperHalfPlane → t ∈ times →
      deriv (fun s ↦ fields.temperature x s) t +
        advectiveDerivative
          (fun y ↦ fields.velocity y t)
          (fun y ↦ fields.temperature y t) x = 0)
    (hboundary : ∀ (x₁ : ℝ) ⦃t : ℝ⦄, t ∈ times →
      streamFunction (horizontalBoundaryPoint x₁) t = 0) :
    IsClassicalVorticityStreamSolutionOn
      (fields.toVorticityStreamFields streamFunction) times := by
  have hvelocityFunction {t : ℝ} (ht : t ∈ times) : (fun y ↦ fields.velocity y t) =
      fun y ↦ vorticityStreamVelocity (fields.toVorticityStreamFields streamFunction) y t :=
    funext fun _ ↦ hvelocity ht
  have hslice {f : ℝ^2 × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ^2) :
      Differentiable ℝ (fun s ↦ f (x, s)) :=
    (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero
  have hvelocityComponent (j : Fin 2) :
      ContDiff ℝ 2 (fun xt : ℝ^2 × ℝ ↦ fields.velocity xt.1 xt.2 j) := by
    simpa [Function.comp_def] using
      (PiLp.proj (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) j).contDiff.comp hvelocityJoint
  have hvorticityJoint :
      ContDiff ℝ 1 (fun xt : ℝ^2 × ℝ ↦ fields.clockwiseVorticity xt.1 xt.2) :=
    (PDE.contDiff_partialDeriv_prod_spaceSlice 1 _ (hvelocityComponent 0)).sub
      (PDE.contDiff_partialDeriv_prod_spaceSlice 0 _ (hvelocityComponent 1))
  have hregularity : HasClassicalVorticityStreamRegularityOn
      (fields.toVorticityStreamFields streamFunction) times :=
    { vorticity_contDiffOn := hvorticityJoint.contDiffOn
      temperature_contDiffOn := htemperatureJoint.contDiffOn
      vorticity_differentiableAt_time := fun {x t} _ ↦ hslice hvorticityJoint x t
      temperature_differentiableAt_time := fun {x t} _ ↦ hslice htemperatureJoint x t
      streamFunction_spatial_contDiff := fun ht ↦ hstream ht }
  refine
    { regularity := hregularity
      vorticity_equation := fun x t hx ht ↦ ?_
      temperature_equation := fun x t hx ht ↦ ?_
      streamFunction_equation := fun x t hx ht ↦ ?_
      zero_streamFunction_boundary := hboundary }
  · rw [← hvelocityFunction ht]
    refine fields.clockwiseVorticity_equation_of_downwardMomentum t upperHalfPlane
      isOpen_upperHalfPlane hvelocityJoint (hpressure ht)
      (htemperatureJoint.comp (contDiff_id.prodMk contDiff_const)) (fun y _ ↦ ?_)
      (fun y hy ↦ hmomentum hy ht) x hx
    rw [hvelocityFunction ht]
    exact divergence_vorticityStreamVelocity_eq_zero _ times hregularity ht
  · rw [← hvelocityFunction ht]
    exact htemperatureEquation hx ht
  · change _ = spatialPlanarClockwiseVorticity (fun y ↦ fields.velocity y t) x
    rw [hvelocityFunction ht]
    exact (spatialPlanarClockwiseVorticity_planarStreamVelocity _ x).symm

end

end Boussinesq
