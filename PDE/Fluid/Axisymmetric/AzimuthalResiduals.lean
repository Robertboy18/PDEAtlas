/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.ReducedNavierStokes
import CAS.ExactTactic

/-!
# Physical azimuthal residuals away from the axis

Multiplying a reduced field by `r` intertwines its radial-four diffusion operator with
the cylindrical azimuthal operator. The physical swirl and vorticity residuals are therefore
`r` times the corresponding reduced residuals, under the displayed regularity hypotheses. The
partial derivatives of the products with `r` are computed by the `cas` tactic of SymLean, our
computer algebra system for Lean.

The reduced variables follow Hou and Li. Their vector-potential streamfunction divided by `r`
corresponds to our scalar Stokes streamfunction divided by `r²`.

## References

* T. Y. Hou and C. Li, "Dynamic stability of the three-dimensional axisymmetric Navier-Stokes
  equations with swirl", Comm. Pure Appl. Math. 61 (2008), no. 5, 661-697, for the reduced
  variables.
  <https://doi.org/10.1002/cpa.20212>
-/

@[expose] public section

namespace AxisymmetricFlow

open EuclideanSpace
open PDE.Common
open PDE.CoordinateSystems

set_option linter.missingDocs true

noncomputable section

/-! ## Off-axis physical residuals -/

/-- Cylindrical scalar operator acting on an azimuthal vector component:
`∂ᵣᵣ + r⁻¹∂ᵣ + ∂_zz - r⁻²`. -/
def azimuthalScalarLaplacian (f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  (∂[(0 : Fin 2)] (fun y ↦ (∂[(0 : Fin 2)] f) y)) x +
    (x (0 : Fin 2))⁻¹ * (∂[(0 : Fin 2)] f) x +
    (∂[(1 : Fin 2)] (fun y ↦ (∂[(1 : Fin 2)] f) y)) x -
    ((x (0 : Fin 2)) ^ 2)⁻¹ * f x

/-- Multiplication by the radial coordinate. -/
def radialMul (f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  x (0 : Fin 2) * f x

/-- The radial derivative of `r f` is `f + r ∂ᵣf`. -/
theorem partialDeriv_zero_radialMul
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ^2) :
    (∂[(0 : Fin 2)] (radialMul f)) x =
      f x + x (0 : Fin 2) * (∂[(0 : Fin 2)] f) x := by
  have hcoord : DifferentiableAt ℝ
      (fun y : ℝ^2 ↦ y (0 : Fin 2)) x := by
    cas
  change (∂[(0 : Fin 2)]
    (fun y : ℝ^2 ↦ y (0 : Fin 2) * f y)) x = _
  rw [PDE.partialDeriv_mul hcoord
    (hf.differentiable (by norm_num)).differentiableAt]
  simp [PDE.partialDeriv_coord]

/-- The axial derivative of `r f` is `r ∂_z f`. -/
theorem partialDeriv_one_radialMul
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ^2) :
    (∂[(1 : Fin 2)] (radialMul f)) x =
      x (0 : Fin 2) * (∂[(1 : Fin 2)] f) x := by
  have hcoord : DifferentiableAt ℝ
      (fun y : ℝ^2 ↦ y (0 : Fin 2)) x := by
    cas
  change (∂[(1 : Fin 2)]
    (fun y : ℝ^2 ↦ y (0 : Fin 2) * f y)) x = _
  rw [PDE.partialDeriv_mul hcoord
    (hf.differentiable (by norm_num)).differentiableAt]
  simp [PDE.partialDeriv_coord]

/-- The second radial derivative of `r f` is
`2 ∂ᵣf + r ∂ᵣᵣf`. -/
theorem partialDeriv_zero_zero_radialMul
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ^2) :
    (∂[(0 : Fin 2)]
        (fun y ↦ (∂[(0 : Fin 2)] (radialMul f)) y)) x =
      2 * (∂[(0 : Fin 2)] f) x +
        x (0 : Fin 2) *
          (∂[(0 : Fin 2)]
            (fun y ↦ (∂[(0 : Fin 2)] f) y)) x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  rw [show (fun y ↦ (∂[(0 : Fin 2)] (radialMul f)) y) =
      fun y ↦ f y + y (0 : Fin 2) * (∂[(0 : Fin 2)] f) y by
    funext y
    exact partialDeriv_zero_radialMul hf1 y]
  have hfr : DifferentiableAt ℝ
      (fun y ↦ (∂[(0 : Fin 2)] f) y) x :=
    ((PDE.contDiff_partialDeriv_of_succ hf).differentiable
      (by norm_num)).differentiableAt
  have hcoord : DifferentiableAt ℝ
      (fun y : ℝ^2 ↦ y (0 : Fin 2)) x := by
    cas
  change (∂[(0 : Fin 2)]
      (f + fun y : ℝ^2 ↦ y (0 : Fin 2) * (∂[(0 : Fin 2)] f) y)) x = _
  rw [show
    (f + fun y : ℝ^2 ↦ y (0 : Fin 2) * (∂[(0 : Fin 2)] f) y) =
      fun y ↦ f y + y (0 : Fin 2) * (∂[(0 : Fin 2)] f) y by
        rfl]
  rw [PDE.partialDeriv_add (f := f)
    (g := fun y : ℝ^2 ↦ y (0 : Fin 2) * (∂[(0 : Fin 2)] f) y)
    (hf.differentiable (by norm_num)).differentiableAt
    (hcoord.mul hfr)]
  rw [PDE.partialDeriv_mul hcoord hfr]
  simp [PDE.partialDeriv_coord]
  ring

/-- The second axial derivative of `r f` is `r ∂_zz f`. -/
theorem partialDeriv_one_one_radialMul
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ^2) :
    (∂[(1 : Fin 2)]
        (fun y ↦ (∂[(1 : Fin 2)] (radialMul f)) y)) x =
      x (0 : Fin 2) *
        (∂[(1 : Fin 2)]
          (fun y ↦ (∂[(1 : Fin 2)] f) y)) x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  rw [show (fun y ↦ (∂[(1 : Fin 2)] (radialMul f)) y) =
      fun y ↦ y (0 : Fin 2) * (∂[(1 : Fin 2)] f) y by
    funext y
    exact partialDeriv_one_radialMul hf1 y]
  have hfz : DifferentiableAt ℝ
      (fun y ↦ (∂[(1 : Fin 2)] f) y) x :=
    ((PDE.contDiff_partialDeriv_of_succ hf).differentiable
      (by norm_num)).differentiableAt
  have hcoord : DifferentiableAt ℝ
      (fun y : ℝ^2 ↦ y (0 : Fin 2)) x := by
    cas
  rw [PDE.partialDeriv_mul hcoord hfz]
  simp [PDE.partialDeriv_coord]

/-- Multiplication by `r` conjugates the reduced four-dimensional radial
Laplacian to the physical azimuthal vector-component Laplacian away from the
axis. -/
theorem azimuthalScalarLaplacian_radialMul
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ^2)
    (hr : x (0 : Fin 2) ≠ 0) :
    azimuthalScalarLaplacian (radialMul f) x =
      x (0 : Fin 2) * radialFourAxialLaplacian f x := by
  rw [azimuthalScalarLaplacian,
    partialDeriv_zero_zero_radialMul hf,
    partialDeriv_zero_radialMul (hf.of_le (by norm_num)),
    partialDeriv_one_one_radialMul hf]
  unfold radialFourAxialLaplacian
  simp only [radialMul]
  field_simp
  ring

/-! ## Physical azimuthal residuals -/

/-- Pointwise physical cylindrical equation for the azimuthal velocity
`u_θ = r u₁`, with all terms moved to the left-hand side. -/
def physicalAzimuthalVelocityResidual
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ azimuthalVelocity fields x s) t +
    reducedRadialVelocity fields x t *
      (∂[(0 : Fin 2)]
        (fun y ↦ azimuthalVelocity fields y t)) x +
    reducedAxialVelocity fields x t *
      (∂[(1 : Fin 2)]
        (fun y ↦ azimuthalVelocity fields y t)) x +
    reducedRadialVelocity fields x t * (x (0 : Fin 2))⁻¹ *
      azimuthalVelocity fields x t -
    ν * azimuthalScalarLaplacian
      (fun y ↦ azimuthalVelocity fields y t) x

/-- Pointwise physical cylindrical equation for azimuthal vorticity
`ω_θ = r ω₁`, with all terms moved to the left-hand side. -/
def physicalAzimuthalVorticityResidual
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ physicalAzimuthalVorticity fields x s) t +
    reducedRadialVelocity fields x t *
      (∂[(0 : Fin 2)]
        (fun y ↦ physicalAzimuthalVorticity fields y t)) x +
    reducedAxialVelocity fields x t *
      (∂[(1 : Fin 2)]
        (fun y ↦ physicalAzimuthalVorticity fields y t)) x -
    reducedRadialVelocity fields x t * (x (0 : Fin 2))⁻¹ *
      physicalAzimuthalVorticity fields x t -
    2 * (x (0 : Fin 2))⁻¹ * azimuthalVelocity fields x t *
      (∂[(1 : Fin 2)]
        (fun y ↦ azimuthalVelocity fields y t)) x -
    ν * azimuthalScalarLaplacian
      (fun y ↦ physicalAzimuthalVorticity fields y t) x

/-- Away from the axis, the physical azimuthal-velocity residual is exactly
`r` times the reduced swirl residual. -/
theorem physicalAzimuthalVelocityResidual_eq_radial_mul_reducedSwirlResidual
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ)
    (hr : x (0 : Fin 2) ≠ 0)
    (htime : DifferentiableAt ℝ (fun s ↦ fields.swirl x s) t)
    (hspace : ContDiff ℝ 2 (fun y ↦ fields.swirl y t)) :
    physicalAzimuthalVelocityResidual ν fields x t =
      x (0 : Fin 2) * reducedSwirlResidual ν fields x t := by
  have hspace1 : ContDiff ℝ 1 (fun y ↦ fields.swirl y t) :=
    hspace.of_le (by norm_num)
  have htimeMul :
      deriv (fun s ↦ azimuthalVelocity fields x s) t =
        x (0 : Fin 2) * deriv (fun s ↦ fields.swirl x s) t := by
    change deriv (fun s ↦ x (0 : Fin 2) * fields.swirl x s) t = _
    exact deriv_const_mul (x (0 : Fin 2)) htime
  have hradial :
      (∂[(0 : Fin 2)]
          (fun y ↦ azimuthalVelocity fields y t)) x =
        fields.swirl x t + x (0 : Fin 2) *
          (∂[(0 : Fin 2)] (fun y ↦ fields.swirl y t)) x := by
    change (∂[(0 : Fin 2)]
      (radialMul (fun y ↦ fields.swirl y t))) x = _
    exact partialDeriv_zero_radialMul hspace1 x
  have haxial :
      (∂[(1 : Fin 2)]
          (fun y ↦ azimuthalVelocity fields y t)) x =
        x (0 : Fin 2) *
          (∂[(1 : Fin 2)] (fun y ↦ fields.swirl y t)) x := by
    change (∂[(1 : Fin 2)]
      (radialMul (fun y ↦ fields.swirl y t))) x = _
    exact partialDeriv_one_radialMul hspace1 x
  have hdiffusion :
      azimuthalScalarLaplacian
          (fun y ↦ azimuthalVelocity fields y t) x =
        x (0 : Fin 2) * radialFourAxialLaplacian
          (fun y ↦ fields.swirl y t) x := by
    change azimuthalScalarLaplacian
      (radialMul (fun y ↦ fields.swirl y t)) x = _
    exact azimuthalScalarLaplacian_radialMul hspace x hr
  rw [physicalAzimuthalVelocityResidual, htimeMul, hradial, haxial,
    hdiffusion, reducedSwirlResidual, reducedAdvection_eq]
  unfold azimuthalVelocity reducedSwirlSource reducedRadialVelocity
  field_simp
  ring

/-- Away from the axis, the physical azimuthal-vorticity residual is exactly
`r` times the reduced vorticity residual. -/
theorem physicalAzimuthalVorticityResidual_eq_radial_mul_reducedVorticityResidual
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ)
    (hr : x (0 : Fin 2) ≠ 0)
    (hvorticityTime :
      DifferentiableAt ℝ (fun s ↦ fields.vorticity x s) t)
    (hvorticitySpace :
      ContDiff ℝ 2 (fun y ↦ fields.vorticity y t))
    (hswirlSpace : ContDiff ℝ 1 (fun y ↦ fields.swirl y t)) :
    physicalAzimuthalVorticityResidual ν fields x t =
      x (0 : Fin 2) * reducedVorticityResidual ν fields x t := by
  have htimeMul :
      deriv (fun s ↦ physicalAzimuthalVorticity fields x s) t =
        x (0 : Fin 2) * deriv (fun s ↦ fields.vorticity x s) t := by
    change deriv (fun s ↦ x (0 : Fin 2) * fields.vorticity x s) t = _
    exact deriv_const_mul (x (0 : Fin 2)) hvorticityTime
  have hradial :
      (∂[(0 : Fin 2)]
          (fun y ↦ physicalAzimuthalVorticity fields y t)) x =
        fields.vorticity x t + x (0 : Fin 2) *
          (∂[(0 : Fin 2)] (fun y ↦ fields.vorticity y t)) x := by
    change (∂[(0 : Fin 2)]
      (radialMul (fun y ↦ fields.vorticity y t))) x = _
    exact partialDeriv_zero_radialMul
      (hvorticitySpace.of_le (by norm_num)) x
  have haxialVorticity :
      (∂[(1 : Fin 2)]
          (fun y ↦ physicalAzimuthalVorticity fields y t)) x =
        x (0 : Fin 2) *
          (∂[(1 : Fin 2)] (fun y ↦ fields.vorticity y t)) x := by
    change (∂[(1 : Fin 2)]
      (radialMul (fun y ↦ fields.vorticity y t))) x = _
    exact partialDeriv_one_radialMul
      (hvorticitySpace.of_le (by norm_num)) x
  have haxialSwirl :
      (∂[(1 : Fin 2)]
          (fun y ↦ azimuthalVelocity fields y t)) x =
        x (0 : Fin 2) *
          (∂[(1 : Fin 2)] (fun y ↦ fields.swirl y t)) x := by
    change (∂[(1 : Fin 2)]
      (radialMul (fun y ↦ fields.swirl y t))) x = _
    exact partialDeriv_one_radialMul hswirlSpace x
  have hdiffusion :
      azimuthalScalarLaplacian
          (fun y ↦ physicalAzimuthalVorticity fields y t) x =
        x (0 : Fin 2) * radialFourAxialLaplacian
          (fun y ↦ fields.vorticity y t) x := by
    change azimuthalScalarLaplacian
      (radialMul (fun y ↦ fields.vorticity y t)) x = _
    exact azimuthalScalarLaplacian_radialMul hvorticitySpace x hr
  rw [physicalAzimuthalVorticityResidual, htimeMul, hradial,
    haxialVorticity, haxialSwirl, hdiffusion, reducedVorticityResidual,
    reducedAdvection_eq]
  unfold physicalAzimuthalVorticity azimuthalVelocity
    reducedVorticitySource
  field_simp
  ring

/-- A classical reduced swirl solution yields the physical azimuthal-velocity
equation at every admitted off-axis point. -/
theorem physicalAzimuthalVelocityResidual_eq_zero_of_reduced
    (ν : ℝ) (fields : ReducedFields) (domain : Set (ℝ^2))
    (times : Set ℝ)
    (hregularity : HasClassicalReducedRegularityOn fields times)
    (hequation : SatisfiesReducedSwirlEquationOn ν fields domain times)
    {x : ℝ^2} {t : ℝ} (hx : x ∈ domain) (ht : t ∈ times)
    (hr : x (0 : Fin 2) ≠ 0) :
    physicalAzimuthalVelocityResidual ν fields x t = 0 := by
  rw [physicalAzimuthalVelocityResidual_eq_radial_mul_reducedSwirlResidual
    ν fields x t hr (hregularity.swirl_differentiableAt_time ht)
    (hregularity.swirl_spatial_contDiff ht), hequation hx ht, mul_zero]

/-- A classical reduced vorticity solution yields the physical
azimuthal-vorticity equation at every admitted off-axis point. -/
theorem physicalAzimuthalVorticityResidual_eq_zero_of_reduced
    (ν : ℝ) (fields : ReducedFields) (domain : Set (ℝ^2))
    (times : Set ℝ)
    (hregularity : HasClassicalReducedRegularityOn fields times)
    (hequation : SatisfiesReducedVorticityEquationOn ν fields domain times)
    {x : ℝ^2} {t : ℝ} (hx : x ∈ domain) (ht : t ∈ times)
    (hr : x (0 : Fin 2) ≠ 0) :
    physicalAzimuthalVorticityResidual ν fields x t = 0 := by
  rw [physicalAzimuthalVorticityResidual_eq_radial_mul_reducedVorticityResidual
    ν fields x t hr (hregularity.vorticity_differentiableAt_time ht)
    (hregularity.vorticity_spatial_contDiff ht)
    ((hregularity.swirl_spatial_contDiff ht).of_le (by norm_num)),
    hequation hx ht, mul_zero]

end

end AxisymmetricFlow
