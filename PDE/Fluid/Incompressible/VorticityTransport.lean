/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Vorticity
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Planar vorticity transport

The scalar vorticity of a two-dimensional incompressible Euler flow satisfies

```text
∂ₜω + u · ∇ω = 0.
```

The left-hand side is the pointwise residual `spacetimePlanarVorticityTransportResidual`, and a
sufficiently regular momentum equation implies, locally, the forced
clockwise-vorticity equation. The momentum equation is assumed on an open
neighborhood of the evaluation point, which is exactly what is needed before
taking its spatial curl.

Both sign conventions for the planar curl are covered, since downstream modules
use each of `spatialPlanarVorticity` (counterclockwise, `∂ₓu₂ - ∂ᵧu₁`) and
`spatialPlanarClockwiseVorticity`.

## Main results

* `spatialPlanarVorticity_gradient_eq_zero`: a `C²` gradient field has zero planar curl.
* `spatialPlanarVorticity_advectiveDerivative_eq`: for a `C²` divergence-free planar
  velocity, `curl((u · ∇)u) = (u · ∇) curl u`.
* `deriv_spatialPlanarVorticity_timeSlice_eq`: time differentiation commutes with the
  spatial curl of a jointly `C²` velocity.
* `spatialPlanarVorticity_equation_of_momentum`: the forced vorticity equation
  `∂ₜω + u · ∇ω = curl f` at a point, from a momentum equation and incompressibility
  holding on an open spatial neighborhood.
* `spacetimePlanarVorticityTransportResidual`: the residual `∂ₜω + u · ∇ω` for a velocity
  field on spacetime `ℝ^3`.

## How it works

We take the spatial curl of the momentum equation on the open neighborhood. Two vector-calculus
identities do the work: pressure gradients have zero planar curl
(`spatialPlanarClockwiseVorticity_gradient_eq_zero`), and for a `C²` divergence-free planar velocity
the curl of convection is convection of curl
(`spatialPlanarClockwiseVorticity_advectiveDerivative_eq`); time differentiation commutes with the
curl (`deriv_spatialPlanarClockwiseVorticity_timeSlice_eq`). The second identity is where two space
dimensions enter: the vortex-stretching term `(ω · ∇)u` of the three-dimensional vorticity equation
has no planar analogue, so the scalar vorticity is simply transported by the flow. The
counterclockwise equation `spatialPlanarVorticity_equation_of_momentum` follows from the clockwise
one `spatialPlanarClockwiseVorticity_equation_of_momentum` by a change of sign.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1, for the vorticity equation and its
  two-dimensional specialization to pure transport, and Chapter 2, for the vorticity-stream
  formulation of planar flows.
  <https://doi.org/10.1017/CBO9780511613203>
-/

open scoped Gradient

@[expose] public section

open PDE (divergence advectiveDerivative)

namespace IncompressibleFlow

open EuclideanSpace

set_option linter.missingDocs true

noncomputable section

/-- The clockwise planar curl of a `C²` pressure gradient vanishes. -/
theorem spatialPlanarClockwiseVorticity_gradient_eq_zero
    (p : ℝ^2 → ℝ) (hp : ContDiff ℝ 2 p) (x : ℝ^2) :
    spatialPlanarClockwiseVorticity (∇ p) x = 0 := by
  simp only [spatialPlanarClockwiseVorticity,
    PDE.gradient_apply_eq_partialDeriv]
  rw [PDE.partialDeriv_partialDeriv_comm (1 : Fin 2) (0 : Fin 2) hp x]
  ring

/-- The counterclockwise planar curl of a `C²` pressure gradient vanishes. -/
theorem spatialPlanarVorticity_gradient_eq_zero
    (p : ℝ^2 → ℝ) (hp : ContDiff ℝ 2 p) (x : ℝ^2) :
    spatialPlanarVorticity (∇ p) x = 0 := by
  have hcurl :=
    spatialPlanarClockwiseVorticity_gradient_eq_zero p hp x
  rw [spatialPlanarClockwiseVorticity_eq_neg_spatialPlanarVorticity] at hcurl
  linarith

/-- For a `C²` divergence-free planar velocity, taking clockwise curl
commutes with the nonlinear convective derivative. -/
theorem spatialPlanarClockwiseVorticity_advectiveDerivative_eq
    (u : ℝ^2 → ℝ^2) (hu : ContDiff ℝ 2 u) (x : ℝ^2)
    (hdiv : ∇· u x = 0) :
    spatialPlanarClockwiseVorticity
        (fun y ↦ advectiveDerivative u u y) x =
      advectiveDerivative u (spatialPlanarClockwiseVorticity u) x := by
  have huComponent (i : Fin 2) : ContDiff ℝ 2 (fun y ↦ u y i) := by
    simpa [Function.comp_def] using (PiLp.proj (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) i).contDiff.comp hu
  have hadvectionComponent (i : Fin 2) :
      (fun y ↦ advectiveDerivative u u y i) = fun y ↦ advectiveDerivative u (fun z ↦ u z i) y := by
    funext y
    have hcomponent : HasFDerivAt (fun z ↦ u z i)
        ((PiLp.proj (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) i).comp (fderiv ℝ u y)) y := by
      exact (PiLp.proj (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) i).hasFDerivAt.comp y
        ((hu.differentiable two_ne_zero) y).hasFDerivAt
    simp [advectiveDerivative, hcomponent.fderiv]
  have hpartialDiff (i j : Fin 2) :
      DifferentiableAt ℝ (fun y ↦ (∂[i] (fun z ↦ u z j)) y) x :=
    ((PDE.contDiff_partialDeriv_of_succ (huComponent j)).differentiable one_ne_zero) x
  simp only [divergence, Fin.sum_univ_two] at hdiv
  rw [spatialPlanarClockwiseVorticity, hadvectionComponent 0, hadvectionComponent 1,
    PDE.partialDeriv_advectiveDerivative 1 u _ x (hu.contDiffAt.of_le (by norm_num))
      (huComponent 0).contDiffAt,
    PDE.partialDeriv_advectiveDerivative 0 u _ x (hu.contDiffAt.of_le (by norm_num))
      (huComponent 1).contDiffAt,
    PDE.advectiveDerivative_eq_sum_mul_partialDeriv]
  simp only [Fin.sum_univ_two]
  rw [show spatialPlanarClockwiseVorticity u = fun y ↦
      (∂[(1 : Fin 2)] (fun z ↦ u z 0)) y - (∂[(0 : Fin 2)] (fun z ↦ u z 1)) y from rfl,
    PDE.partialDeriv_sub (hpartialDiff 1 0) (hpartialDiff 0 1),
    PDE.partialDeriv_sub (hpartialDiff 1 0) (hpartialDiff 0 1),
    PDE.partialDeriv_partialDeriv_comm 1 0 (huComponent 0) x,
    PDE.partialDeriv_partialDeriv_comm 0 1 (huComponent 1) x]
  linear_combination
    ((∂[(1 : Fin 2)] (fun y ↦ u y 0)) x - (∂[(0 : Fin 2)] (fun y ↦ u y 1)) x) * hdiv

/-- For a `C²` divergence-free planar velocity, taking counterclockwise curl
commutes with the nonlinear convective derivative. -/
theorem spatialPlanarVorticity_advectiveDerivative_eq
    (u : ℝ^2 → ℝ^2) (hu : ContDiff ℝ 2 u) (x : ℝ^2)
    (hdiv : ∇· u x = 0) :
    spatialPlanarVorticity
        (fun y ↦ advectiveDerivative u u y) x =
      advectiveDerivative u (spatialPlanarVorticity u) x := by
  have hcurl :=
    spatialPlanarClockwiseVorticity_advectiveDerivative_eq
      u hu x hdiv
  have hleft :
      spatialPlanarClockwiseVorticity
          (fun y ↦ advectiveDerivative u u y) =
        -spatialPlanarVorticity
          (fun y ↦ advectiveDerivative u u y) := by
    funext y
    exact spatialPlanarClockwiseVorticity_eq_neg_spatialPlanarVorticity _ _
  have hright :
      spatialPlanarClockwiseVorticity u =
        -spatialPlanarVorticity u := by
    funext y
    exact spatialPlanarClockwiseVorticity_eq_neg_spatialPlanarVorticity _ _
  rw [hleft, hright] at hcurl
  unfold advectiveDerivative at hcurl ⊢
  simp only [fderiv_neg, Pi.neg_apply, neg_apply] at hcurl
  linarith

/-- For a jointly `C²` planar velocity, one time derivative commutes with
taking the clockwise spatial curl of a fixed-time slice. -/
theorem deriv_spatialPlanarClockwiseVorticity_timeSlice_eq
    (u : ℝ^2 → ℝ → ℝ^2) (x : ℝ^2) (t : ℝ)
    (hu : ContDiff ℝ 2 (fun xt : ℝ^2 × ℝ ↦ u xt.1 xt.2)) :
    deriv
        (fun s ↦ spatialPlanarClockwiseVorticity
          (fun y ↦ u y s) x) t =
      (∂[(1 : Fin 2)]
          (fun y ↦ deriv (fun s ↦ u y s 0) t)) x -
        (∂[(0 : Fin 2)]
          (fun y ↦ deriv (fun s ↦ u y s 1) t)) x := by
  have huComponent (j : Fin 2) : ContDiff ℝ 2
      (fun xt : ℝ^2 × ℝ ↦ u xt.1 xt.2 j) := by
    simpa [Function.comp_def] using
      (PiLp.proj (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) j).contDiff.comp hu
  have htraceDiff (i j : Fin 2) : DifferentiableAt ℝ
      (fun s ↦ (∂[i] (fun y ↦ u y s j)) x) t :=
    ((PDE.contDiff_partialDeriv_timeTrace i
      (fun xt : ℝ^2 × ℝ ↦ u xt.1 xt.2 j) x
      (huComponent j)).differentiable (by norm_num)).differentiableAt
  simp only [spatialPlanarClockwiseVorticity]
  rw [deriv_fun_sub (htraceDiff 1 0) (htraceDiff 0 1),
    PDE.deriv_partialDeriv_timeSlice_comm (1 : Fin 2)
      (fun xt : ℝ^2 × ℝ ↦ u xt.1 xt.2 0) x t (huComponent 0),
    PDE.deriv_partialDeriv_timeSlice_comm (0 : Fin 2)
      (fun xt : ℝ^2 × ℝ ↦ u xt.1 xt.2 1) x t (huComponent 1)]

/-- For a jointly `C²` planar velocity, one time derivative commutes with
taking the counterclockwise spatial curl of a fixed-time slice. -/
theorem deriv_spatialPlanarVorticity_timeSlice_eq
    (u : ℝ^2 → ℝ → ℝ^2) (x : ℝ^2) (t : ℝ)
    (hu : ContDiff ℝ 2 (fun xt : ℝ^2 × ℝ ↦ u xt.1 xt.2)) :
    deriv
        (fun s ↦ spatialPlanarVorticity
          (fun y ↦ u y s) x) t =
      (∂[(0 : Fin 2)]
          (fun y ↦ deriv (fun s ↦ u y s 1) t)) x -
        (∂[(1 : Fin 2)]
          (fun y ↦ deriv (fun s ↦ u y s 0) t)) x := by
  have hcurl :=
    deriv_spatialPlanarClockwiseVorticity_timeSlice_eq u x t hu
  have hsign :
      (fun s ↦ spatialPlanarClockwiseVorticity
        (fun y ↦ u y s) x) =
        -(fun s ↦ spatialPlanarVorticity
          (fun y ↦ u y s) x) := by
    funext s
    exact spatialPlanarClockwiseVorticity_eq_neg_spatialPlanarVorticity _ _
  rw [hsign] at hcurl
  unfold deriv at hcurl ⊢
  simp only [fderiv_neg, neg_apply] at hcurl
  linarith

/-- Taking clockwise spatial curl of a regular planar momentum equation gives
the forced vorticity equation.

The momentum identity and incompressibility are required on an open spatial
neighborhood of `x`. This local hypothesis justifies differentiating the
component equations there; no global equation or boundary condition is used. -/
theorem spatialPlanarClockwiseVorticity_equation_of_momentum
    (u force : ℝ^2 → ℝ → ℝ^2) (p : ℝ^2 → ℝ → ℝ)
    (t : ℝ) (spatialDomain : Set (ℝ^2))
    (hspatialDomain : IsOpen spatialDomain)
    (huJoint : ContDiff ℝ 2 (fun xt : ℝ^2 × ℝ ↦ u xt.1 xt.2))
    (hp : ContDiff ℝ 2 (fun y ↦ p y t))
    (hforce : ContDiff ℝ 1 (fun y ↦ force y t))
    (hdivergence : ∀ y ∈ spatialDomain,
      ∇· (fun z ↦ u z t) y = 0)
    (hmomentum : ∀ y ∈ spatialDomain,
      deriv (fun s ↦ u y s) t +
          advectiveDerivative (fun z ↦ u z t) (fun z ↦ u z t) y +
          ∇ (fun z ↦ p z t) y =
        force y t)
    (x : ℝ^2) (hx : x ∈ spatialDomain) :
    deriv
          (fun s ↦ spatialPlanarClockwiseVorticity
            (fun y ↦ u y s) x) t +
        advectiveDerivative
          (fun y ↦ u y t)
          (fun y ↦ spatialPlanarClockwiseVorticity
            (fun z ↦ u z t) y) x =
      spatialPlanarClockwiseVorticity (fun y ↦ force y t) x := by
  have hvelocity : ContDiff ℝ 2 (fun y ↦ u y t) :=
    huJoint.comp (contDiff_id.prodMk contDiff_const)
  have hconvection : ContDiff ℝ 1 (fun y ↦ advectiveDerivative (fun z ↦ u z t) (fun z ↦ u z t) y) :=
    (hvelocity.fderiv_right (m := 1) (n := 2) (by norm_num)).clm_apply
      (hvelocity.of_le (by norm_num))
  have hcomp {f : ℝ^2 → ℝ^2} (hf : ContDiff ℝ 1 f) (j : Fin 2) :
      DifferentiableAt ℝ (fun y ↦ f y j) x :=
    (((PiLp.proj (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) j).contDiff.comp hf).differentiable
      one_ne_zero x :)
  have hpressure (j : Fin 2) : DifferentiableAt ℝ (fun y ↦ ∇ (fun z ↦ p z t) y j) x := by
    simpa using
      ((PDE.contDiff_partialDeriv_of_succ (i := j) hp).differentiable one_ne_zero).differentiableAt
  -- near `x`, the momentum equation gives `∂ₜuⱼ = fⱼ - ((u · ∇)u)ⱼ - ∂ⱼp`
  have htime (j : Fin 2) : (fun y ↦ deriv (fun s ↦ u y s j) t) =ᶠ[nhds x] fun y ↦
      force y t j - advectiveDerivative (fun z ↦ u z t) (fun z ↦ u z t) y j -
        ∇ (fun z ↦ p z t) y j := by
    filter_upwards [hspatialDomain.mem_nhds hx] with y hy
    have hderiv : HasDerivAt (fun s ↦ u y s j) (deriv (fun s ↦ u y s) t j) t :=
      (PiLp.proj (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) j).hasFDerivAt.comp_hasDerivAt t
        (((huJoint.differentiable two_ne_zero) (y, t)).comp t (by fun_prop)).hasDerivAt
    have h := congrArg (fun v : ℝ^2 ↦ v j) (hmomentum y hy)
    simp only [WithLp.ofLp_add, Pi.add_apply] at h
    rw [hderiv.deriv]
    linarith
  rw [deriv_spatialPlanarClockwiseVorticity_timeSlice_eq u x t huJoint,
    PDE.partialDeriv_congr_nhds 1 (htime 0), PDE.partialDeriv_congr_nhds 0 (htime 1),
    PDE.partialDeriv_sub ((hcomp hforce 0).fun_sub (hcomp hconvection 0)) (hpressure 0),
    PDE.partialDeriv_sub ((hcomp hforce 1).fun_sub (hcomp hconvection 1)) (hpressure 1),
    PDE.partialDeriv_sub (hcomp hforce 0) (hcomp hconvection 0),
    PDE.partialDeriv_sub (hcomp hforce 1) (hcomp hconvection 1),
    ← spatialPlanarClockwiseVorticity_advectiveDerivative_eq _ hvelocity x (hdivergence x hx)]
  have hpressureCurl := spatialPlanarClockwiseVorticity_gradient_eq_zero (fun y ↦ p y t) hp x
  simp only [spatialPlanarClockwiseVorticity] at hpressureCurl ⊢
  linarith

/-- Taking counterclockwise spatial curl of a regular planar momentum equation
gives the forced vorticity equation.

The momentum identity and incompressibility are required on an open spatial
neighborhood of `x`, exactly as in the clockwise-sign theorem. -/
theorem spatialPlanarVorticity_equation_of_momentum
    (u force : ℝ^2 → ℝ → ℝ^2) (p : ℝ^2 → ℝ → ℝ)
    (t : ℝ) (spatialDomain : Set (ℝ^2))
    (hspatialDomain : IsOpen spatialDomain)
    (huJoint : ContDiff ℝ 2 (fun xt : ℝ^2 × ℝ ↦ u xt.1 xt.2))
    (hp : ContDiff ℝ 2 (fun y ↦ p y t))
    (hforce : ContDiff ℝ 1 (fun y ↦ force y t))
    (hdivergence : ∀ y ∈ spatialDomain,
      ∇· (fun z ↦ u z t) y = 0)
    (hmomentum : ∀ y ∈ spatialDomain,
      deriv (fun s ↦ u y s) t +
          advectiveDerivative (fun z ↦ u z t) (fun z ↦ u z t) y +
          ∇ (fun z ↦ p z t) y =
        force y t)
    (x : ℝ^2) (hx : x ∈ spatialDomain) :
    deriv
          (fun s ↦ spatialPlanarVorticity
            (fun y ↦ u y s) x) t +
        advectiveDerivative
          (fun y ↦ u y t)
          (fun y ↦ spatialPlanarVorticity
            (fun z ↦ u z t) y) x =
      spatialPlanarVorticity (fun y ↦ force y t) x := by
  have hcurl := spatialPlanarClockwiseVorticity_equation_of_momentum u force p t spatialDomain
    hspatialDomain huJoint hp hforce hdivergence hmomentum x hx
  simp only [spatialPlanarClockwiseVorticity_eq_neg_spatialPlanarVorticity, deriv.fun_neg,
    advectiveDerivative, fderiv_fun_neg, neg_apply] at hcurl
  rw [advectiveDerivative]
  linarith

/-- Material-derivative residual `∂ₜω + u · ∇ω` for
the planar vorticity of a spacetime velocity field. -/
def spacetimePlanarVorticityTransportResidual
    (u : ℝ^3 → ℝ^2) (x : ℝ^3) : ℝ :=
  scalarMaterialDerivative 2 u (spacetimePlanarVorticity u) x

/-- The planar vorticity-transport residual expands as
`∂ₜω + u · ∇ω`. -/
@[simp]
theorem spacetimePlanarVorticityTransportResidual_apply
    (u : ℝ^3 → ℝ^2) (x : ℝ^3) :
    spacetimePlanarVorticityTransportResidual u x =
      (∂[(0 : Fin 3)] (spacetimePlanarVorticity u)) x +
        ∑ j : Fin 2,
          u x j * (∂[j.succ] (spacetimePlanarVorticity u)) x :=
  scalarMaterialDerivative_apply 2 u (spacetimePlanarVorticity u) x

/-- A spatially and temporally constant planar vorticity has zero transport
residual. -/
theorem spacetimePlanarVorticityTransportResidual_eq_zero_of_eq_const
    (u : ℝ^3 → ℝ^2) (omega : ℝ)
    (homega : ∀ y, spacetimePlanarVorticity u y = omega) (x : ℝ^3) :
    spacetimePlanarVorticityTransportResidual u x = 0 := by
  have hfun : spacetimePlanarVorticity u = fun _ ↦ omega := funext homega
  rw [spacetimePlanarVorticityTransportResidual, hfun]
  simp

end

end IncompressibleFlow
