/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.Model
import PDE.FDeriv.Reflection.Coordinate

/-!
# Reflection symmetries for the upper-half-plane model

Chen and Hou impose odd horizontal parity on vorticity, even horizontal parity
on temperature, and a zero temperature trace on the vertical axis. These give
elementary vanishing statements at the origin (`HasReflectionSymmetryAtTime.*`).
The required velocity parity follows from odd streamfunction parity
(`hasReflectionSymmetryAtTime_of_streamFunction`). Odd streamfunction parity in turn
follows from odd vorticity parity through the Dirichlet Poisson problem under the
hypotheses of `PoissonSymmetry`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (Sym).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace Boussinesq

open IncompressibleFlow
open PDE.Common

set_option linter.missingDocs true

noncomputable section

/-- Reflection `(x₁,x₂) ↦ (-x₁,x₂)` in the vertical axis. -/
def tangentialReflection (x : ℝ^2) : ℝ^2 :=
  PDE.Common.coordinateReflection (0 : Fin 2) x

/-- The horizontal boundary parametrization sends zero to the origin. -/
@[simp]
theorem horizontalBoundaryPoint_zero :
    horizontalBoundaryPoint 0 = (0 : ℝ^2) := by
  ext i
  fin_cases i <;> simp

/-- Reflection fixes the vertical axis. -/
@[simp]
theorem tangentialReflection_verticalAxisPoint (x₂ : ℝ) :
    tangentialReflection !₂[0, x₂] = !₂[0, x₂] := by
  ext i
  fin_cases i <;> simp [tangentialReflection]

/-- Reflection in the vertical axis preserves the open upper half-plane. -/
@[simp]
theorem tangentialReflection_mem_upperHalfPlane_iff {x : ℝ^2} :
    tangentialReflection x ∈ upperHalfPlane ↔ x ∈ upperHalfPlane := by
  exact coordinateReflection_mem_coordinateUpperHalfSpace_iff_of_ne
    (0 : Fin 2) (1 : Fin 2) (by decide) x

/-- Reflection in the vertical axis negates the horizontal boundary
parameter. -/
@[simp]
theorem tangentialReflection_horizontalBoundaryPoint (x₁ : ℝ) :
    tangentialReflection (horizontalBoundaryPoint x₁) =
      horizontalBoundaryPoint (-x₁) := by
  ext i
  fin_cases i <;> simp [tangentialReflection]

/-- An odd streamfunction generates an odd tangential velocity component. -/
theorem planarStreamVelocity_zero_isOddUnderTangentialReflection
    {streamFunction : ℝ^2 → ℝ}
    (hodd : IsOddUnderCoordinateReflection (0 : Fin 2) streamFunction)
    (hcont : ContDiff ℝ 1 streamFunction) :
    IsOddUnderCoordinateReflection (0 : Fin 2)
      (fun x ↦ planarStreamVelocity streamFunction x 0) := by
  intro x
  simp only [planarStreamVelocity_apply_zero]
  exact congrArg Neg.neg (hodd.partialDeriv_of_ne (by decide) hcont x)

/-- An odd streamfunction generates an even normal velocity component. -/
theorem planarStreamVelocity_one_isEvenUnderTangentialReflection
    {streamFunction : ℝ^2 → ℝ}
    (hodd : IsOddUnderCoordinateReflection (0 : Fin 2) streamFunction)
    (hcont : ContDiff ℝ 1 streamFunction) :
    IsEvenUnderCoordinateReflection (0 : Fin 2)
      (fun x ↦ planarStreamVelocity streamFunction x 1) := by
  simpa only [planarStreamVelocity_apply_one] using
    hodd.partialDeriv_same hcont

/-- The reflection symmetry at one time: odd vorticity and even temperature in `x₁`,
temperature zero on the vertical axis, odd tangential velocity and zero normal velocity on
the boundary. These are the minimal scalar and velocity conditions used by the
normalization calculation. -/
structure HasReflectionSymmetryAtTime
    (fields : VorticityStreamFields) (t : ℝ) : Prop where
  /-- Vorticity is odd under reflection in the vertical axis. -/
  vorticity_tangentially_odd :
    IsOddUnderCoordinateReflection (0 : Fin 2)
      (fun x ↦ fields.vorticity x t)
  /-- Temperature is even under reflection in the vertical axis. -/
  temperature_tangentially_even :
    IsEvenUnderCoordinateReflection (0 : Fin 2)
      (fun x ↦ fields.temperature x t)
  /-- Temperature vanishes on the vertical axis. -/
  temperature_vanishes_on_vertical_axis :
    VanishesOnCoordinateHyperplane (0 : Fin 2)
      (fun x ↦ fields.temperature x t)
  /-- Tangential velocity is odd under reflection in the vertical axis. -/
  tangential_velocity_tangentially_odd :
    IsOddUnderCoordinateReflection (0 : Fin 2)
      (fun x ↦ vorticityStreamVelocity fields x t 0)
  /-- Normal velocity vanishes on the horizontal boundary. -/
  normal_velocity_vanishes_on_horizontal_boundary :
    VanishesOnCoordinateHyperplane (1 : Fin 2)
      (fun x ↦ vorticityStreamVelocity fields x t 1)

/-- Odd streamfunction parity and the Dirichlet trace imply the velocity
conditions used in the normalization calculation. -/
theorem hasReflectionSymmetryAtTime_of_streamFunction
    {fields : VorticityStreamFields} {t : ℝ}
    (hvorticity :
      IsOddUnderCoordinateReflection (0 : Fin 2)
        (fun x ↦ fields.vorticity x t))
    (htemperatureEven :
      IsEvenUnderCoordinateReflection (0 : Fin 2)
        (fun x ↦ fields.temperature x t))
    (htemperatureZero :
      VanishesOnCoordinateHyperplane (0 : Fin 2)
        (fun x ↦ fields.temperature x t))
    (hstreamOdd :
      IsOddUnderCoordinateReflection (0 : Fin 2)
        (fun x ↦ fields.streamFunction x t))
    (hstreamBoundary :
      VanishesOnCoordinateHyperplane (1 : Fin 2)
        (fun x ↦ fields.streamFunction x t))
    (hstream : ContDiff ℝ 1 (fun x ↦ fields.streamFunction x t)) :
    HasReflectionSymmetryAtTime fields t := by
  refine
    { vorticity_tangentially_odd := hvorticity
      temperature_tangentially_even := htemperatureEven
      temperature_vanishes_on_vertical_axis := htemperatureZero
      tangential_velocity_tangentially_odd := ?_
      normal_velocity_vanishes_on_horizontal_boundary := ?_ }
  · simpa [vorticityStreamVelocity] using
      planarStreamVelocity_zero_isOddUnderTangentialReflection
        hstreamOdd hstream
  · intro x hx
    simpa [vorticityStreamVelocity] using
      hstreamBoundary
        |>.partialDeriv_eq_zero_of_ne (by decide) hx
        ((hstream.differentiable (by norm_num)).differentiableAt)

/-- The reflection symmetry forces the reconstructed velocity to vanish
at the origin. -/
theorem HasReflectionSymmetryAtTime.vorticityStreamVelocity_origin_eq_zero
    {fields : VorticityStreamFields} {t : ℝ}
    (hsymmetry : HasReflectionSymmetryAtTime fields t) :
    vorticityStreamVelocity fields 0 t = 0 := by
  ext j
  fin_cases j
  · have h :=
      hsymmetry.tangential_velocity_tangentially_odd.vanishesOnCoordinateHyperplane
        (show (0 : ℝ^2) ∈ coordinateHyperplane (0 : Fin 2) by
          simp [coordinateHyperplane])
    simpa using h
  · have h := hsymmetry.normal_velocity_vanishes_on_horizontal_boundary
        (show (0 : ℝ^2) ∈ coordinateHyperplane (1 : Fin 2) by
          simp [coordinateHyperplane])
    simpa using h

/-- The tangential derivative of the normal velocity vanishes at the origin
under the horizontal no-flow trace. -/
theorem HasReflectionSymmetryAtTime.partialDeriv_zero_normal_velocity_at_origin_eq_zero
    {fields : VorticityStreamFields} {t : ℝ}
    (hsymmetry : HasReflectionSymmetryAtTime fields t)
    (hdiff : DifferentiableAt ℝ
      (fun x ↦ vorticityStreamVelocity fields x t 1) 0) :
    (∂[(0 : Fin 2)]
        (fun x ↦ vorticityStreamVelocity fields x t 1)) 0 = 0 := by
  exact hsymmetry.normal_velocity_vanishes_on_horizontal_boundary
    |>.partialDeriv_eq_zero_of_ne (by decide)
      (show (0 : ℝ^2) ∈ coordinateHyperplane (1 : Fin 2) by
        simp [coordinateHyperplane]) hdiff

/-- The normal derivative of tangentially odd vorticity vanishes at the
origin. -/
theorem HasReflectionSymmetryAtTime.partialDeriv_one_vorticity_at_origin_eq_zero
    {fields : VorticityStreamFields} {t : ℝ}
    (hsymmetry : HasReflectionSymmetryAtTime fields t)
    (hdiff : DifferentiableAt ℝ (fun x ↦ fields.vorticity x t) 0) :
    (∂[(1 : Fin 2)] (fun x ↦ fields.vorticity x t)) 0 = 0 := by
  exact hsymmetry.vorticity_tangentially_odd.vanishesOnCoordinateHyperplane
    |>.partialDeriv_eq_zero_of_ne
      (by decide)
      (show (0 : ℝ^2) ∈ coordinateHyperplane (0 : Fin 2) by
        simp [coordinateHyperplane]) hdiff

/-- The tangential derivative of tangentially even temperature vanishes at
the origin. -/
theorem HasReflectionSymmetryAtTime.partialDeriv_zero_temperature_at_origin_eq_zero
    {fields : VorticityStreamFields} {t : ℝ}
    (hsymmetry : HasReflectionSymmetryAtTime fields t)
    (hdiff : DifferentiableAt ℝ (fun x ↦ fields.temperature x t) 0) :
    (∂[(0 : Fin 2)] (fun x ↦ fields.temperature x t)) 0 = 0 := by
  exact hsymmetry.temperature_tangentially_even.partialDeriv_eq_zero
      (show (0 : ℝ^2) ∈ coordinateHyperplane (0 : Fin 2) by
        simp [coordinateHyperplane]) hdiff

/-- The normal derivative of the zero vertical-axis temperature trace
vanishes at the origin. -/
theorem HasReflectionSymmetryAtTime.partialDeriv_one_temperature_at_origin_eq_zero
    {fields : VorticityStreamFields} {t : ℝ}
    (hsymmetry : HasReflectionSymmetryAtTime fields t)
    (hdiff : DifferentiableAt ℝ (fun x ↦ fields.temperature x t) 0) :
    (∂[(1 : Fin 2)] (fun x ↦ fields.temperature x t)) 0 = 0 := by
  exact hsymmetry.temperature_vanishes_on_vertical_axis
    |>.partialDeriv_eq_zero_of_ne (by decide)
      (show (0 : ℝ^2) ∈ coordinateHyperplane (0 : Fin 2) by
        simp [coordinateHyperplane]) hdiff

end

end Boussinesq
