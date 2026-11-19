/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderProfiles
public import PDE.Fluid.Axisymmetric.LocalEvolution
public import PDE.Fluid.NavierStokes.PressureFromVorticity
public import PDE.Fluid.Incompressible.ParametricPressure
import PDE.FDeriv.SpaceTime
import PDE.FDeriv.Reflection.Coordinate
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Fluid.Incompressible.Locality
import PDE.Analysis.Calculus.Potential.Convex

/-!
# Cartesian Euler flows in the cylinder from squared-radius profiles

A `ProfileSolution L T` is a triple of squared-radius profiles `U`, `Ω`, `Ψ` of `(t, s, z)`,
smooth on an open set containing `[0, T) × ℝ²`, that solves the reduced Euler equations on
`0 < s < 1` with the wall condition `Ψ(t, 1, z) = 0` (`SatisfiesProfileSystemOn`), is
`L`-periodic in `z`, and lies in the reflection class (`U` even and `Ψ` odd in `z`). By
`satisfiesMeridianSystemOn_ofProfiles_iff` these are the axis-regular solutions of the meridian
system (6.2)-(6.4) of Chen and Hou. The theorem `ProfileSolution.smoothSolution` reconstructs a
classical Euler solution in the periodic cylinder (`Euler.Cylinder.SmoothSolution`) with zero
forcing and velocity `spacetimeAxisymmetricVelocity U Ψ`.

## Main definitions

* `ProfileSolution`: the profile data and hypotheses.
* `ProfileSolution.velocity`, `ProfileSolution.pressure`: the reconstructed fields.

## Main results

* `ProfileSolution.smoothSolution`: the reconstructed classical solution.
* `exists_smoothSolution_of_satisfiesMeridianSystemOn`: the same from a solution of the meridian
  system (6.2)-(6.4) for axis-regular fields `(r U, r Ω, r Ψ)`.
* `ProfileSolution.mul_abs_vorticity_le_norm_curl`: `r |Ω| ≤ |curl u|` in the open cylinder off the
  axis, which turns bounds on `ω̃ = ω^θ / r` into bounds on the Cartesian vorticity.

## How it works

The velocity `spacetimeAxisymmetricVelocity U Ψ` is built from the profiles without dividing by `r`,
so it is smooth through the axis (`ProfileSolution.contDiffAt_velocity`). Off the axis the reduced
equations give the Cartesian vorticity equation
(`AxisymmetricFlow.eulerVorticityTransportResidual_axisymmetric_eq_zero_on`), so the spatial
derivatives of `g = -D_t u` commute there, and by continuity they commute on the axis too. The
pressure is the segment integral `IncompressibleFlow.normalizedPressure 0 g` over the convex
cylinder (`ProfileSolution.hasGradientAt_pressure`), and a cutoff in time near each `t₀ ∈ (0, T)`
makes it jointly smooth (`ProfileSolution.contDiffAt_pressure`). Its periodicity uses the reflection
class: `g(t, Rx) = R g(t, x)` for the reflection `R` of `z`, so the pressure is even in `z`. Since
`∇p` is periodic, `p(x + L e_z) - p(x)` is a constant, equal to `p(L/2 e_z) - p(-L/2 e_z) = 0`
(`ProfileSolution.normalizedPressure_add`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6, (6.2)-(6.4).
  <https://arxiv.org/abs/2210.07191v4>
* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapters 1 and 2.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

open PDE (laplacian advectiveDerivative partialDeriv time coordinateLine spatialGradient)

namespace Euler.Cylinder

open EuclideanSpace Filter
open PDE.Common PDE.CoordinateSystems AxisymmetricFlow IncompressibleFlow
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-- Squared-radius profiles `(U, Ω, Ψ)` of an `L`-periodic axisymmetric Euler flow in the
cylinder on `[0, T)`, in the reflection class, solving the reduced equations with the wall
condition. The profiles extend smoothly to an open set containing `[0, T) × ℝ²`, so across the
axis, the wall and the initial time; this is a sufficient class for the construction, not a
description of every classical solution. Only `U` and `Ψ` enter the velocity, so periodicity and
parity are required of them; `Ω` is tied to `Ψ` by the stream equation on `0 < s < 1`. -/
structure ProfileSolution (L T : ℝ) where
  /-- Swirl profile `U = u^θ / r`. -/
  swirl : ℝ^3 → ℝ
  /-- Vorticity profile `Ω = ω^θ / r`. -/
  vorticity : ℝ^3 → ℝ
  /-- Stream function profile `Ψ = φ̃ / r`. -/
  streamFunction : ℝ^3 → ℝ
  /-- An open set of `(t, s, z)` on which the profiles are smooth. -/
  profileDomain : Set (ℝ^3)
  /-- The profile domain is open. -/
  isOpen_profileDomain : IsOpen profileDomain
  /-- The profile domain contains `[0, T) × ℝ²`. -/
  mem_profileDomain : ∀ q : ℝ^3, 0 ≤ q 0 → q 0 < T → q ∈ profileDomain
  /-- Smooth swirl profile. -/
  swirl_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) swirl profileDomain
  /-- Smooth vorticity profile. -/
  vorticity_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) vorticity profileDomain
  /-- Smooth stream function profile. -/
  streamFunction_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) streamFunction profileDomain
  /-- The reduced Euler equations on `0 < s < 1` and the wall condition, for `0 < t < T`. -/
  equations : SatisfiesProfileSystemOn swirl vorticity streamFunction (Set.Ioo 0 T)
  /-- The axial period is positive. -/
  period_pos : 0 < L
  /-- The final time is positive. -/
  time_pos : 0 < T
  /-- Periodic swirl profile. -/
  swirl_periodic : ∀ q, swirl (q + EuclideanSpace.single (2 : Fin 3) L) = swirl q
  /-- Periodic stream function profile. -/
  streamFunction_periodic :
    ∀ q, streamFunction (q + EuclideanSpace.single (2 : Fin 3) L) = streamFunction q
  /-- Even swirl profile. -/
  swirl_even : IsEvenUnderCoordinateReflection (2 : Fin 3) swirl
  /-- Odd stream function profile. -/
  streamFunction_odd : IsOddUnderCoordinateReflection (2 : Fin 3) streamFunction

namespace ProfileSolution

variable {L T : ℝ} (P : ProfileSolution L T)

/-- The reconstructed Cartesian velocity. -/
def velocity : ℝ^4 → ℝ^3 :=
  spacetimeAxisymmetricVelocity P.swirl P.streamFunction

/-- Spacetime points at times in `[0, T)` map into the profile domain. -/
theorem squaredMap_mem_profileDomain {xt : ℝ^4} (h0 : 0 ≤ xt 0) (h1 : xt 0 < T) :
    spacetimeSquaredCylindricalMap xt ∈ P.profileDomain :=
  P.mem_profileDomain _ (by simpa [spacetimeSquaredCylindricalMap, time] using h0)
    (by simpa [spacetimeSquaredCylindricalMap, time] using h1)

/-- The velocity is smooth at every time in `[0, T)`. -/
theorem contDiffAt_velocity {xt : ℝ^4} (h0 : 0 ≤ xt 0) (h1 : xt 0 < T) :
    ContDiffAt ℝ (⊤ : ℕ∞) P.velocity xt :=
  contDiffAt_top_spacetimeAxisymmetricVelocity
    (P.swirl_contDiffOn.contDiffAt
      (P.isOpen_profileDomain.mem_nhds (P.squaredMap_mem_profileDomain h0 h1)))
    (P.streamFunction_contDiffOn.contDiffAt
      (P.isOpen_profileDomain.mem_nhds (P.squaredMap_mem_profileDomain h0 h1)))

/-- A profile is smooth on every time slice `t ∈ [0, T)`. -/
theorem contDiff_profileSlice {Φ : ℝ^3 → ℝ} (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ P.profileDomain)
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t < T) : ContDiff ℝ (⊤ : ℕ∞) (profileSlice Φ t) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  have hq : timeSpaceCons t q ∈ P.profileDomain :=
    P.mem_profileDomain _ (by simpa using h0) (by simpa using h1)
  exact (hΦ.contDiffAt (P.isOpen_profileDomain.mem_nhds hq)).comp q
    (contDiff_timeSpaceCons_spatial 2 t).contDiffAt

/-- The velocity at `(t, x)` is the reconstruction from the profile slices at time `t`. -/
theorem velocity_timeSpaceCons (t : ℝ) (x : ℝ^3) :
    P.velocity (timeSpaceCons t x) =
      axisymmetricVelocity (profileSlice P.swirl t) (profileSlice P.streamFunction t) x :=
  spacetimeAxisymmetricVelocity_timeSpaceCons _ _ t x

end ProfileSolution

/-- Adding a coordinate vector to the spatial part shifts the next spacetime coordinate. -/
theorem timeSpaceCons_add_single {n : ℕ} (t : ℝ) (x : ℝ^n) (i : Fin n) (c : ℝ) :
    timeSpaceCons t (x + EuclideanSpace.single i c) =
      timeSpaceCons t x + EuclideanSpace.single i.succ c := by
  ext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp
  · by_cases h : k = i
    · subst h
      simp
    · simp [h, Fin.succ_inj]

/-- The spacetime axial shift is the axial shift of the spatial part. -/
theorem timeSpaceCons_add_axialShift (t L : ℝ) (x : ℝ^3) :
    timeSpaceCons t x + axialShift L =
      timeSpaceCons t (x + EuclideanSpace.single (2 : Fin 3) L) := by
  rw [timeSpaceCons_add_single]
  ext j
  simp [axialShift]

/-- The squared-cylindrical map turns an axial shift into a shift of `z`. -/
theorem squaredCylindricalMap_add_single_two (x : ℝ^3) (L : ℝ) :
    squaredCylindricalMap (x + EuclideanSpace.single (2 : Fin 3) L) =
      squaredCylindricalMap x + EuclideanSpace.single (1 : Fin 2) L := by
  ext i
  fin_cases i <;> simp [cylindricalRadiusSq, axialCoordinate]

/-- A profile periodic in `z` has periodic slices. -/
theorem profileSlice_add_single_one {Φ : ℝ^3 → ℝ} {L : ℝ}
    (hΦ : ∀ q, Φ (q + EuclideanSpace.single (2 : Fin 3) L) = Φ q) (t : ℝ) (y : ℝ^2) :
    profileSlice Φ t (y + EuclideanSpace.single (1 : Fin 2) L) = profileSlice Φ t y := by
  simp only [profileSlice_apply, timeSpaceCons_add_single]
  exact hΦ _

/-- Partial derivatives of a periodic function are periodic. -/
theorem partialDeriv_add_of_periodic {n : ℕ} {f : ℝ^n → ℝ} {c : ℝ^n}
    (hf : ∀ y, f (y + c) = f y) (i : Fin n) (y : ℝ^n) :
    (∂[i] f) (y + c) = (∂[i] f) y := by
  have hfun : f = fun z ↦ f (z + c) := funext fun z ↦ (hf z).symm
  unfold partialDeriv
  conv_rhs => rw [hfun]
  rw [fderiv_comp_add_right]

/-- Coordinate `1` of the spacetime point `(t, x)`, `x ∈ ℝ³`, is `x 0`. -/
private theorem timeSpaceCons_three_apply_one (t : ℝ) (x : ℝ^3) :
    timeSpaceCons t x 1 = x 0 :=
  timeSpaceCons_succ t x 0

/-- Coordinate `2` of the spacetime point `(t, x)`, `x ∈ ℝ³`, is `x 1`. -/
private theorem timeSpaceCons_three_apply_two (t : ℝ) (x : ℝ^3) :
    timeSpaceCons t x 2 = x 1 :=
  timeSpaceCons_succ t x 1

/-- Coordinate `3` of the spacetime point `(t, x)`, `x ∈ ℝ³`, is `x 2`. -/
private theorem timeSpaceCons_three_apply_three (t : ℝ) (x : ℝ^3) :
    timeSpaceCons t x 3 = x 2 :=
  timeSpaceCons_succ t x 2

/-- Coordinate `1` of the spacetime point `(t, y)`, `y ∈ ℝ²`, is `y 0`. -/
private theorem timeSpaceCons_two_apply_one (t : ℝ) (y : ℝ^2) :
    timeSpaceCons t y 1 = y 0 :=
  timeSpaceCons_succ t y 0

/-- Coordinate `2` of the spacetime point `(t, y)`, `y ∈ ℝ²`, is `y 1`. -/
private theorem timeSpaceCons_two_apply_two (t : ℝ) (y : ℝ^2) :
    timeSpaceCons t y 2 = y 1 :=
  timeSpaceCons_succ t y 1

/-- The reflection `z ↦ -z` of space commutes with forming spacetime points. -/
theorem timeSpaceCons_coordinateReflection (t : ℝ) (x : ℝ^3) :
    timeSpaceCons t (coordinateReflection (2 : Fin 3) x) =
      coordinateReflection (3 : Fin 4) (timeSpaceCons t x) := by
  ext j
  fin_cases j <;>
    simp [timeSpaceCons_three_apply_one, timeSpaceCons_three_apply_two,
      timeSpaceCons_three_apply_three, coordinateReflection_apply_same]

/-- The reflection `z ↦ -z` of profile space commutes with forming profile points. -/
theorem timeSpaceCons_coordinateReflection_profile (t : ℝ) (y : ℝ^2) :
    timeSpaceCons t (coordinateReflection (1 : Fin 2) y) =
      coordinateReflection (2 : Fin 3) (timeSpaceCons t y) := by
  ext j
  fin_cases j <;>
    simp [timeSpaceCons_two_apply_one, timeSpaceCons_two_apply_two,
      coordinateReflection_apply_same]

/-- The squared-cylindrical map intertwines the reflections of `z`. -/
theorem squaredCylindricalMap_coordinateReflection (x : ℝ^3) :
    squaredCylindricalMap (coordinateReflection (2 : Fin 3) x) =
      coordinateReflection (1 : Fin 2) (squaredCylindricalMap x) := by
  ext i
  fin_cases i <;>
    simp [cylindricalRadiusSq, axialCoordinate, coordinateReflection_apply_same]

namespace ProfileSolution

variable {L T : ℝ} (P : ProfileSolution L T)

/-- The velocity is `L`-periodic in `z`. -/
theorem velocity_add_axialShift (xt : ℝ^4) :
    P.velocity (xt + axialShift L) = P.velocity xt := by
  rw [← timeSpaceCons_spatialPart xt, timeSpaceCons_add_axialShift, velocity_timeSpaceCons,
    velocity_timeSpaceCons]
  have hU := profileSlice_add_single_one P.swirl_periodic (xt 0)
  have hΨ := profileSlice_add_single_one P.streamFunction_periodic (xt 0)
  have hlift {Φ : ℝ^2 → ℝ} (hΦ : ∀ y, Φ (y + EuclideanSpace.single (1 : Fin 2) L) = Φ y)
      (x : ℝ^3) : squaredCylindricalLift Φ (x + EuclideanSpace.single (2 : Fin 3) L) =
        squaredCylindricalLift Φ x := by
    simp only [squaredCylindricalLift, squaredCylindricalMap_add_single_two, hΦ]
  have hd (i : Fin 2) := partialDeriv_add_of_periodic hΨ i
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, axisymmetricVelocity_apply_zero]
    rw [hlift hU, hlift (hd 1)]
    simp
  · simp only [Fin.mk_one, Fin.isValue, axisymmetricVelocity_apply_one]
    rw [hlift hU, hlift (hd 1)]
    simp
  · simp only [Fin.reduceFinMk, Fin.isValue, axisymmetricVelocity_apply_two]
    rw [hlift hΨ, hlift (hd 0)]
    simp [cylindricalRadiusSq]

/-- On a time slice in `[0, T)` the swirl profile is even and the stream function profile is
odd in `z`, and so are their derivatives with the corresponding parities. -/
theorem slice_parity {t : ℝ} (h0 : 0 ≤ t) (h1 : t < T) :
    IsEvenUnderCoordinateReflection (1 : Fin 2) (profileSlice P.swirl t) ∧
      IsOddUnderCoordinateReflection (1 : Fin 2) (profileSlice P.streamFunction t) ∧
      IsOddUnderCoordinateReflection (1 : Fin 2)
        (fun y ↦ (∂[(0 : Fin 2)] (profileSlice P.streamFunction t)) y) ∧
      IsEvenUnderCoordinateReflection (1 : Fin 2)
        (fun y ↦ (∂[(1 : Fin 2)] (profileSlice P.streamFunction t)) y) := by
  have hU : IsEvenUnderCoordinateReflection (1 : Fin 2) (profileSlice P.swirl t) := by
    intro y
    simp only [profileSlice_apply, timeSpaceCons_coordinateReflection_profile]
    exact P.swirl_even _
  have hΨ : IsOddUnderCoordinateReflection (1 : Fin 2) (profileSlice P.streamFunction t) := by
    intro y
    simp only [profileSlice_apply, timeSpaceCons_coordinateReflection_profile]
    exact P.streamFunction_odd _
  have hc : ContDiff ℝ 1 (profileSlice P.streamFunction t) :=
    (P.contDiff_profileSlice P.streamFunction_contDiffOn h0 h1).of_le (by simp)
  exact ⟨hU, hΨ, hΨ.partialDeriv_of_ne (by decide) hc, hΨ.partialDeriv_same hc⟩

/-- In the reflection class the velocity is reflection equivariant: `u(R x) = R u(x)` for the
reflection `R` of `z`, at every time in `[0, T)`. -/
theorem velocity_coordinateReflection {xt : ℝ^4} (h0 : 0 ≤ xt 0) (h1 : xt 0 < T) :
    P.velocity (coordinateReflection (3 : Fin 4) xt) =
      coordinateReflection (2 : Fin 3) (P.velocity xt) := by
  obtain ⟨hU, hΨ, hΨs, hΨz⟩ := P.slice_parity h0 h1
  rw [← timeSpaceCons_spatialPart xt, ← timeSpaceCons_coordinateReflection,
    velocity_timeSpaceCons, velocity_timeSpaceCons]
  have hlift {Φ : ℝ^2 → ℝ} (x : ℝ^3) : squaredCylindricalLift Φ
      (coordinateReflection (2 : Fin 3) x) =
      Φ (coordinateReflection (1 : Fin 2) (squaredCylindricalMap x)) := by
    simp [squaredCylindricalLift, squaredCylindricalMap_coordinateReflection]
  have hsq (x : ℝ^3) : cylindricalRadiusSq (coordinateReflection (2 : Fin 3) x) =
      cylindricalRadiusSq x := by
    simp [cylindricalRadiusSq]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, axisymmetricVelocity_apply_zero, hlift, hU _,
      hΨz _]
    simp [squaredCylindricalLift]
  · simp only [Fin.mk_one, Fin.isValue, axisymmetricVelocity_apply_one, hlift, hU _, hΨz _]
    simp [squaredCylindricalLift]
  · simp only [Fin.reduceFinMk, Fin.isValue, axisymmetricVelocity_apply_two, hlift, hΨ _,
      hΨs _, hsq]
    simp [squaredCylindricalLift, coordinateReflection_apply_same]
    ring

/-- The velocity is divergence free at every time in `[0, T)`. -/
theorem divergenceFreeAt_velocity {xt : ℝ^4} (h0 : 0 ≤ xt 0) (h1 : xt 0 < T) :
    DivergenceFreeAt P.velocity xt := by
  have hxt : timeSpaceCons (xt 0) (squaredCylindricalMap (spatialPart xt)) ∈ P.profileDomain :=
    P.mem_profileDomain _ (by simpa using h0) (by simpa using h1)
  rw [← timeSpaceCons_spatialPart xt]
  change spatialDivergence 3 P.velocity _ = 0
  rw [← spatialFieldDivergence_velocitySlice _ _
    ((P.contDiffAt_velocity (by simpa using h0) (by simpa using h1)).differentiableAt
      (by simp))]
  exact spatialFieldDivergence_velocitySlice_eq_zero_of_contDiffOn P.isOpen_profileDomain
    (P.swirl_contDiffOn.of_le (by simp)) (P.streamFunction_contDiffOn.of_le (by simp)) _ _
    hxt

/-- Impermeability: the normal velocity vanishes on the wall. -/
theorem wallNormalVelocity_velocity {xt : ℝ^4} (hxt : xt ∈ wallSpacetime T) :
    wallNormalVelocity P.velocity xt = 0 := by
  obtain ⟨ht0, htT, hwall⟩ := hxt
  rw [← timeSpaceCons_spatialPart xt]
  set t := xt 0
  set x := spatialPart xt
  have hwall' : cylindricalRadiusSq x = 1 := hwall
  have hzero :
      (∂[(1 : Fin 2)] (profileSlice P.streamFunction t)) (squaredCylindricalMap x) = 0 := by
    have hd : DifferentiableAt ℝ (profileSlice P.streamFunction t) (squaredCylindricalMap x) :=
      ((P.contDiff_profileSlice P.streamFunction_contDiffOn ht0.le htT).differentiable
        (by simp)) _
    rw [PDE.partialDeriv_eq_deriv_coordinateLine 1 _ hd]
    have hline : profileSlice P.streamFunction t ∘ coordinateLine 1 (squaredCylindricalMap x) =
        fun _ ↦ 0 := by
      funext σ
      have hpt : timeSpaceCons t (coordinateLine 1 (squaredCylindricalMap x) σ) =
          profilePoint t 1 σ := by
        ext j
        fin_cases j <;> simp [coordinateLine, profilePoint, timeSpaceCons_two_apply_one,
          timeSpaceCons_two_apply_two, hwall']
      simp only [Function.comp_apply, profileSlice_apply, hpt]
      exact P.equations.wall ⟨ht0, htT⟩ σ
    rw [hline, deriv_const]
  simp only [wallNormalVelocity, timeSpaceCons_three_apply_one, timeSpaceCons_three_apply_two,
    velocity_timeSpaceCons, axisymmetricVelocity_apply_zero, axisymmetricVelocity_apply_one]
  simp only [squaredCylindricalLift, hzero]
  ring

end ProfileSolution

/-- A component of the derivative of a vector field is the derivative of the component. -/
theorem fderiv_apply_component {n m : ℕ} {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u x) (v : ℝ^n) (i : Fin m) :
    fderiv ℝ u x v i = fderiv ℝ (fun y ↦ u y i) x v := by
  have h : fderiv ℝ (fun y ↦ u y i) x =
      (EuclideanSpace.proj i : ℝ^m →L[ℝ] ℝ).comp (fderiv ℝ u x) :=
    ((EuclideanSpace.proj i : ℝ^m →L[ℝ] ℝ).hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  rw [h]
  rfl

/-- The material derivative `D_t u = ∂_t u + (u · ∇) u` is the derivative of `u` along the
spacetime direction `(1, u)`. -/
theorem materialDerivative_self_eq_fderiv {n : ℕ} {u : ℝ^(n + 1) → ℝ^n} {xt : ℝ^(n + 1)}
    (hu : DifferentiableAt ℝ u xt) :
    materialDerivative n u u xt = fderiv ℝ u xt (timeSpaceCons 1 (u xt)) := by
  ext i
  rw [materialDerivative_apply, fderiv_apply_component hu, PDE.fderiv_apply_eq_sum_partialDeriv_mul,
    Fin.sum_univ_succ]
  simp only [timeSpaceCons_zero, mul_one, timeSpaceCons_succ]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- The material derivative is smooth where the velocity is. -/
theorem contDiffAt_materialDerivative_self {n : ℕ} {u : ℝ^(n + 1) → ℝ^n} {xt : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) u xt) :
    ContDiffAt ℝ (⊤ : ℕ∞) (materialDerivative n u u) xt := by
  apply (contDiffAt_piLp (2 : ENNReal)).2
  intro i
  have hui : ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ u y i) xt :=
    (contDiffAt_piLp (2 : ENNReal)).1 hu i
  have hd (k : Fin (n + 1)) : ContDiffAt ℝ (⊤ : ℕ∞) (∂[k] (fun y ↦ u y i)) xt :=
    hui.partialDeriv k (by simp)
  simp only [materialDerivative_apply]
  exact (hd 0).add (ContDiffAt.sum fun j _ ↦
    ((contDiffAt_piLp (2 : ENNReal)).1 hu j).mul (hd j.succ))

/-- A periodic field has a periodic material derivative. -/
theorem materialDerivative_self_add_of_periodic {n : ℕ} {u : ℝ^(n + 1) → ℝ^n} {c : ℝ^(n + 1)}
    (hu : ∀ y, u (y + c) = u y) (xt : ℝ^(n + 1)) :
    materialDerivative n u u (xt + c) = materialDerivative n u u xt := by
  ext i
  have hi : ∀ y, u (y + c) i = u y i := fun y ↦ by rw [hu]
  have hd (k : Fin (n + 1)) := partialDeriv_add_of_periodic (f := fun z ↦ u z i) hi k xt
  simp only [materialDerivative_apply, hu, hd]

/-- Points at times in `(0, T)` have a neighbourhood of times in `(0, T)`. -/
theorem eventually_time_mem_Ioo {T : ℝ} {xt : ℝ^4} (h0 : 0 < xt 0) (h1 : xt 0 < T) :
    ∀ᶠ y in 𝓝 xt, 0 < y 0 ∧ y 0 < T := by
  have hc : Continuous (fun y : ℝ^4 ↦ y 0) := by fun_prop
  exact (hc.continuousAt.eventually (lt_mem_nhds h0)).and
    (hc.continuousAt.eventually (gt_mem_nhds h1))

namespace ProfileSolution

variable {L T : ℝ} (P : ProfileSolution L T)

/-- In the reflection class the material derivative is reflection equivariant at interior
times. -/
theorem materialDerivative_coordinateReflection {xt : ℝ^4} (h0 : 0 < xt 0) (h1 : xt 0 < T) :
    materialDerivative 3 P.velocity P.velocity (coordinateReflection (3 : Fin 4) xt) =
      coordinateReflection (2 : Fin 3) (materialDerivative 3 P.velocity P.velocity xt) := by
  set Rt := (coordinateReflectionLinearIsometryEquiv (3 : Fin 4)).toContinuousLinearEquiv
  set Rx := (coordinateReflectionLinearIsometryEquiv (2 : Fin 3)).toContinuousLinearEquiv
  have hRt (y : ℝ^4) : Rt y = coordinateReflection (3 : Fin 4) y := rfl
  have hRx (y : ℝ^3) : Rx y = coordinateReflection (2 : Fin 3) y := rfl
  have htime : (coordinateReflection (3 : Fin 4) xt) 0 = xt 0 := by
    simp
  have hu : DifferentiableAt ℝ P.velocity xt :=
    (P.contDiffAt_velocity h0.le h1).differentiableAt (by simp)
  have huR : DifferentiableAt ℝ P.velocity (Rt xt) :=
    (P.contDiffAt_velocity (by rw [hRt, htime]; exact h0.le)
      (by rw [hRt, htime]; exact h1)).differentiableAt (by simp)
  have heq : (fun y ↦ P.velocity (Rt y)) =ᶠ[𝓝 xt] fun y ↦ Rx (P.velocity y) := by
    filter_upwards [eventually_time_mem_Ioo h0 h1] with y hy
    exact P.velocity_coordinateReflection hy.1.le hy.2
  have hderiv : fderiv ℝ (fun y ↦ P.velocity (Rt y)) xt =
      (fderiv ℝ P.velocity (Rt xt)).comp (Rt : ℝ^4 →L[ℝ] ℝ^4) :=
    (huR.hasFDerivAt.comp xt Rt.hasFDerivAt).fderiv
  have hderiv' : fderiv ℝ (fun y ↦ Rx (P.velocity y)) xt =
      (Rx : ℝ^3 →L[ℝ] ℝ^3).comp (fderiv ℝ P.velocity xt) :=
    (Rx.hasFDerivAt.comp xt hu.hasFDerivAt).fderiv
  have hcomm (v : ℝ^4) :
      fderiv ℝ P.velocity (Rt xt) (Rt v) = Rx (fderiv ℝ P.velocity xt v) := by
    have h1 := heq.fderiv_eq (𝕜 := ℝ)
    rw [hderiv, hderiv'] at h1
    exact congrArg (fun A : ℝ^4 →L[ℝ] ℝ^3 ↦ A v) h1
  have hdir : Rt (timeSpaceCons 1 (P.velocity xt)) =
      timeSpaceCons 1 (P.velocity (Rt xt)) := by
    rw [hRt, ← timeSpaceCons_coordinateReflection, hRt,
      P.velocity_coordinateReflection h0.le h1]
  rw [← hRt, materialDerivative_self_eq_fderiv huR, materialDerivative_self_eq_fderiv hu, ← hdir,
    hcomm, hRx]

/-- The pressure gradient field `g(t, x) = -D_t u(t, x)`. -/
def pressureGradient (t : ℝ) (x : ℝ^3) : ℝ^3 :=
  -materialDerivative 3 P.velocity P.velocity (timeSpaceCons t x)

/-- The pressure gradient field is reflection equivariant at interior times. -/
theorem pressureGradient_coordinateReflection {t : ℝ} (h0 : 0 < t) (h1 : t < T) (x : ℝ^3) :
    P.pressureGradient t (coordinateReflection (2 : Fin 3) x) =
      coordinateReflection (2 : Fin 3) (P.pressureGradient t x) := by
  simp only [pressureGradient, timeSpaceCons_coordinateReflection]
  rw [P.materialDerivative_coordinateReflection (by simpa using h0) (by simpa using h1)]
  exact (map_neg (coordinateReflectionLinearIsometryEquiv (2 : Fin 3)) _).symm

/-- The pressure gradient field is `L`-periodic in `z`. -/
theorem pressureGradient_add (t : ℝ) (x : ℝ^3) :
    P.pressureGradient t (x + EuclideanSpace.single (2 : Fin 3) L) = P.pressureGradient t x := by
  simp only [pressureGradient, ← timeSpaceCons_add_axialShift]
  rw [materialDerivative_self_add_of_periodic P.velocity_add_axialShift]

/-- The pressure gradient field is jointly smooth at interior times. -/
theorem contDiffAt_pressureGradient {t : ℝ} (h0 : 0 < t) (h1 : t < T) (x : ℝ^3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry P.pressureGradient) (t, x) := by
  have hmd := contDiffAt_materialDerivative_self (P.contDiffAt_velocity
    (xt := timeSpaceCons t x) (by simpa using h0.le) (by simpa using h1))
  exact (hmd.comp (t, x) (contDiff_timeSpaceCons_uncurry 3).contDiffAt).neg

end ProfileSolution

/-- The profile strip over the open time interval is open. -/
theorem isOpen_profileStrip_Ioo (T : ℝ) : IsOpen (profileStrip (Set.Ioo 0 T)) := by
  have h0 : Continuous (fun q : ℝ^3 ↦ q 0) := by fun_prop
  have h1 : Continuous (fun q : ℝ^3 ↦ q 1) := by fun_prop
  exact ((isOpen_Ioo.preimage h0).inter ((isOpen_lt continuous_const h1).inter
    (isOpen_lt h1 continuous_const)))

/-- Points of the open spacetime cylinder off the axis. -/
def offAxisDomain (T : ℝ) : Set (ℝ^4) :=
  {xt | xt ∈ spacetimeDomain T ∧ 0 < cylindricalRadiusSq (spatialPart xt)}

/-- The off-axis part of the open spacetime cylinder is open. -/
theorem isOpen_offAxisDomain (T : ℝ) : IsOpen (offAxisDomain T) :=
  (isOpen_spacetimeDomain T).inter
    (isOpen_lt continuous_const (continuous_cylindricalRadiusSq.comp continuous_spatialPart))

/-- Off-axis points of the open cylinder map into the profile strip. -/
theorem squaredMap_mem_profileStrip {T : ℝ} {xt : ℝ^4} (hxt : xt ∈ offAxisDomain T) :
    spacetimeSquaredCylindricalMap xt ∈ profileStrip (Set.Ioo 0 T) := by
  obtain ⟨⟨h0, h1, hdom⟩, hpos⟩ := hxt
  refine ⟨?_, ?_, ?_⟩
  · simpa [spacetimeSquaredCylindricalMap, time] using ⟨h0, h1⟩
  · simpa [spacetimeSquaredCylindricalMap, time, timeSpaceCons_two_apply_one] using hpos
  · have hlt : cylindricalRadiusSq (spatialPart xt) < 1 := hdom
    simpa [spacetimeSquaredCylindricalMap, time, timeSpaceCons_two_apply_one] using hlt

/-- Two continuous functions that agree on the open cylinder off the axis agree on the whole
open cylinder. -/
theorem eq_of_eq_offAxis {f₁ f₂ : ℝ^3 → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂) {x : ℝ^3}
    (hx : x ∈ domain) (h : ∀ y ∈ domain, 0 < cylindricalRadiusSq y → f₁ y = f₂ y) :
    f₁ x = f₂ x := by
  by_cases hpos : 0 < cylindricalRadiusSq x
  · exact h x hx hpos
  have hzero : x 0 = 0 ∧ x 1 = 0 := by
    have hnn := cylindricalRadiusSq_nonneg x
    have h0 : cylindricalRadiusSq x = 0 := le_antisymm (not_lt.1 hpos) hnn
    unfold cylindricalRadiusSq at h0
    constructor <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  let γ : ℝ → ℝ^3 := fun ε ↦ x + ε • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have hγ : Continuous γ := by fun_prop
  have hγ0 : γ 0 = x := by simp [γ]
  have hnear : ∀ᶠ ε in 𝓝[>] (0 : ℝ), γ ε ∈ domain ∧ 0 < cylindricalRadiusSq (γ ε) := by
    have hdom : ∀ᶠ ε in 𝓝 (0 : ℝ), γ ε ∈ domain :=
      hγ.continuousAt.eventually (by rw [hγ0]; exact isOpen_domain.mem_nhds hx)
    filter_upwards [nhdsWithin_le_nhds hdom, self_mem_nhdsWithin] with ε hε hεpos
    refine ⟨hε, ?_⟩
    simp only [γ, cylindricalRadiusSq, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
      hzero.1, hzero.2, smul_eq_mul]
    simp only [Fin.isValue, ↓reduceIte, mul_one, zero_add, one_ne_zero, mul_zero, add_zero]
    have hε2 := pow_pos (Set.mem_Ioi.1 hεpos) 2
    simpa using hε2
  have heq : (f₁ ∘ γ) =ᶠ[𝓝[>] (0 : ℝ)] (f₂ ∘ γ) :=
    hnear.mono fun ε hε ↦ h _ hε.1 hε.2
  have ht₁ : Tendsto (f₁ ∘ γ) (𝓝[>] (0 : ℝ)) (𝓝 (f₁ x)) := by
    rw [← hγ0]
    exact ((h₁.comp hγ).tendsto 0).mono_left nhdsWithin_le_nhds
  have ht₂ : Tendsto (f₂ ∘ γ) (𝓝[>] (0 : ℝ)) (𝓝 (f₂ x)) := by
    rw [← hγ0]
    exact ((h₂.comp hγ).tendsto 0).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (ht₁.congr' heq) ht₂

namespace ProfileSolution

variable {L T : ℝ} (P : ProfileSolution L T)

/-- The profile strip lies in the profile domain. -/
theorem profileStrip_subset_profileDomain : profileStrip (Set.Ioo 0 T) ⊆ P.profileDomain :=
  fun q hq ↦ P.mem_profileDomain q hq.1.1.le hq.1.2

/-- Off the axis the curl of the velocity is the vorticity reconstructed from `U` and `Ω`. -/
theorem curl_eq_vorticityFromCoefficients {xt : ℝ^4} (hxt : xt ∈ offAxisDomain T) :
    spacetimeSpatialCurl P.velocity xt =
      spacetimeAxisymmetricVorticityFromCoefficients P.swirl P.vorticity xt := by
  have hstrip := squaredMap_mem_profileStrip hxt
  rw [← timeSpaceCons_spatialPart xt, spacetimeSpatialCurl_timeSpaceCons]
  have hmem : timeSpaceCons (xt 0) (squaredCylindricalMap (spatialPart xt)) ∈
      profileStrip (Set.Ioo 0 T) := by
    simpa [spacetimeSquaredCylindricalMap, time] using hstrip
  exact spatialCurl_velocitySlice_eq_vorticityFromCoefficients_of_contDiffOn
    (isOpen_profileStrip_Ioo T)
    ((P.swirl_contDiffOn.mono P.profileStrip_subset_profileDomain).of_le (by simp))
    ((P.streamFunction_contDiffOn.mono P.profileStrip_subset_profileDomain).of_le (by simp))
    P.equations.streamFunction_equation _ _ hmem

/-- Off the axis the velocity and its curl satisfy the Euler vorticity equation. -/
theorem vorticityTransportResidual_eq_zero {xt : ℝ^4} (hxt : xt ∈ offAxisDomain T) :
    vorticityTransportResidual 3 0 P.velocity (spacetimeSpatialCurl P.velocity) xt = 0 := by
  have hcurl : spacetimeSpatialCurl P.velocity =ᶠ[𝓝 xt]
      spacetimeAxisymmetricVorticityFromCoefficients P.swirl P.vorticity := by
    filter_upwards [(isOpen_offAxisDomain T).mem_nhds hxt] with y hy
    exact P.curl_eq_vorticityFromCoefficients hy
  have hres := vorticityTransportResidual_eventuallyEq (n := 3) 0
    (EventuallyEq.refl (𝓝 xt) P.velocity) hcurl
  rw [hres.eq_of_nhds]
  exact eulerVorticityTransportResidual_axisymmetric_eq_zero_on (isOpen_profileStrip_Ioo T)
    ((P.swirl_contDiffOn.mono P.profileStrip_subset_profileDomain).of_le (by simp))
    ((P.vorticity_contDiffOn.mono P.profileStrip_subset_profileDomain).of_le (by simp))
    ((P.streamFunction_contDiffOn.mono P.profileStrip_subset_profileDomain).of_le (by simp))
    P.equations.swirl_equation P.equations.vorticity_equation (squaredMap_mem_profileStrip hxt)

/-- Each slice of the pressure gradient field at an interior time is smooth. -/
theorem contDiff_pressureGradient_slice {t : ℝ} (h0 : 0 < t) (h1 : t < T) :
    ContDiff ℝ (⊤ : ℕ∞) (P.pressureGradient t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (P.contDiffAt_pressureGradient h0 h1 x).comp x
    ((contDiff_const.prodMk contDiff_id).contDiffAt)

/-- The spatial derivatives of the pressure gradient field commute in the open cylinder at
interior times. -/
theorem partialDeriv_pressureGradient_comm {t : ℝ} (h0 : 0 < t) (h1 : t < T) {x : ℝ^3}
    (hx : x ∈ Euler.Cylinder.domain) (i j : Fin 3) :
    (∂[i] (fun y ↦ P.pressureGradient t y j)) x =
      (∂[j] (fun y ↦ P.pressureGradient t y i)) x := by
  have hg := P.contDiff_pressureGradient_slice h0 h1
  have hgk (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ P.pressureGradient t y k) :=
    (contDiff_piLp (2 : ENNReal)).1 hg k
  refine eq_of_eq_offAxis (PDE.contDiff_top_partialDeriv (i := i) (hgk j)).continuous
    (PDE.contDiff_top_partialDeriv (i := j) (hgk i)).continuous hx fun y hy hpos ↦ ?_
  set yt := timeSpaceCons t y
  have hyt : yt ∈ offAxisDomain T := ⟨timeSpaceCons_mem_spacetimeDomain ⟨h0, h1⟩ hy,
    by simpa [yt] using hpos⟩
  have hu : ContDiffAt ℝ (⊤ : ℕ∞) P.velocity yt :=
    P.contDiffAt_velocity (by simpa [yt] using h0.le) (by simpa [yt] using h1)
  have hform := vorticityFormTransportResidual_eq_zero_of_vectorVorticity_of_contDiffAt 0
    P.velocity yt (hu.of_le (by simp)) (P.divergenceFreeAt_velocity (by simpa [yt] using h0.le)
      (by simpa [yt] using h1)) (P.vorticityTransportResidual_eq_zero hyt)
  have hanti := antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual_of_contDiffAt
    0 P.velocity i j yt (hu.of_le (by simp))
  rw [hform] at hanti
  have hcand (k : Fin 3) : (fun z ↦ (NavierStokes.viscousTerm 3 0 P.velocity z -
      materialDerivative 3 P.velocity P.velocity z) k) =
      fun z ↦ -(materialDerivative 3 P.velocity P.velocity z k) := by
    funext z
    simp [NavierStokes.viscousTerm]
  have hmd : ContDiffAt ℝ (⊤ : ℕ∞) (materialDerivative 3 P.velocity P.velocity) yt :=
    contDiffAt_materialDerivative_self hu
  have hslice (k : Fin 3) (l : Fin 3) : (∂[l] (fun z ↦ P.pressureGradient t z k)) y =
      (∂[l.succ] (fun z ↦ -(materialDerivative 3 P.velocity P.velocity z k))) yt := by
    have hdk : DifferentiableAt ℝ (fun z ↦ -(materialDerivative 3 P.velocity P.velocity z k)) yt :=
      (((contDiffAt_piLp (2 : ENNReal)).1 hmd k).neg).differentiableAt (by simp)
    rw [← PDE.partialDeriv_timeSpaceCons_spatial l _ t y hdk]
    rfl
  rw [hslice j i, hslice i j]
  rw [hcand j, hcand i] at hanti
  simpa [sub_eq_zero] using hanti

/-- The pressure `p(t, x) = ∫₀¹ g(t, σ x) · x dσ`, the segment integral of `g = -D_t u` from
the origin. -/
def pressure (xt : ℝ^4) : ℝ :=
  normalizedPressure 0 P.pressureGradient (xt 0) (spatialPart xt)

/-- The pressure at `(t, x)`. -/
@[simp]
theorem pressure_timeSpaceCons (t : ℝ) (x : ℝ^3) :
    P.pressure (timeSpaceCons t x) = normalizedPressure 0 P.pressureGradient t x := by
  simp [pressure]

/-- In the open cylinder at interior times the pressure has spatial gradient `g = -D_t u`. -/
theorem hasGradientAt_pressure {t : ℝ} (h0 : 0 < t) (h1 : t < T) {x : ℝ^3}
    (hx : x ∈ Euler.Cylinder.domain) :
    HasGradientAt (normalizedPressure 0 P.pressureGradient t) (P.pressureGradient t x) x := by
  have hg := P.contDiff_pressureGradient_slice h0 h1
  refine hasGradientAt_normalizedPressure convex_domain isOpen_domain zero_mem_domain t
    (hg.differentiable (by simp)).differentiableOn (fun y hy a b ↦ ?_) hx
  exact EuclideanSpace.inner_fderiv_apply_comm_of_partialDeriv_comm (P.pressureGradient t) y
    ((hg.differentiable (by simp)) y) (fun i j ↦ P.partialDeriv_pressureGradient_comm h0 h1 hy i j)
    a b

end ProfileSolution

/-- The segment-integral pressure is linear in a time-dependent scalar factor. -/
theorem normalizedPressure_smul {n : ℕ} (χ : ℝ → ℝ) (a : ℝ^n) (g : ℝ → ℝ^n → ℝ^n) (t : ℝ)
    (x : ℝ^n) :
    normalizedPressure a (fun t x ↦ χ t • g t x) t x = χ t * normalizedPressure a g t x := by
  simp only [normalizedPressure, real_inner_smul_left]
  exact MeasureTheory.integral_const_mul _ _

namespace ProfileSolution

variable {L T : ℝ} (P : ProfileSolution L T)

/-- The pressure is jointly smooth in the open spacetime cylinder. A smooth cutoff in time
equal to one near the given time makes the field `g` globally smooth without changing the
pressure nearby. -/
theorem contDiffAt_pressure {xt : ℝ^4} (h0 : 0 < xt 0) (h1 : xt 0 < T) :
    ContDiffAt ℝ (⊤ : ℕ∞) P.pressure xt := by
  set t₀ := xt 0
  set δ := min t₀ (T - t₀) / 2
  have hδ : 0 < δ := by
    have : 0 < min t₀ (T - t₀) := lt_min h0 (by linarith)
    positivity
  let χ : ContDiffBump t₀ := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hsupp : tsupport χ ⊆ Set.Ioo 0 T := by
    rw [χ.tsupport_eq]
    intro τ hτ
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hτ
    have hmin1 : min t₀ (T - t₀) ≤ t₀ := min_le_left _ _
    have hmin2 : min t₀ (T - t₀) ≤ T - t₀ := min_le_right _ _
    have hδ' : δ = min t₀ (T - t₀) / 2 := rfl
    constructor <;> nlinarith
  let gc : ℝ → ℝ^3 → ℝ^3 := fun t x ↦ χ t • P.pressureGradient t x
  have hgc : ContDiff ℝ (⊤ : ℕ∞) gc.uncurry := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨t, x⟩
    by_cases ht : t ∈ Set.Ioo 0 T
    · exact ((χ.contDiff (n := (⊤ : ℕ∞))).contDiffAt.comp (t, x) contDiffAt_fst).smul
        (P.contDiffAt_pressureGradient ht.1 ht.2 x)
    · have hnot : t ∉ tsupport χ := fun h ↦ ht (hsupp h)
      have hmem : (tsupport (χ : ℝ → ℝ))ᶜ ∈ 𝓝 t :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds hnot
      have hopen : ∀ᶠ q : ℝ × ℝ^3 in 𝓝 (t, x), q.1 ∈ (tsupport (χ : ℝ → ℝ))ᶜ :=
        continuousAt_fst.preimage_mem_nhds hmem
      refine contDiffAt_const (c := (0 : ℝ^3)).congr_of_eventuallyEq ?_
      filter_upwards [hopen] with q hq
      obtain ⟨a, b⟩ := q
      simp only [Function.uncurry_apply_pair, gc]
      rw [image_eq_zero_of_notMem_tsupport hq, zero_smul]
  have hpc := contDiff_infty_normalizedPressure 0 hgc
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^4 ↦ (y 0, spatialPart y)) := by
    have h₀ : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^4 ↦ y 0) :=
      (EuclideanSpace.proj (0 : Fin 4) : ℝ^4 →L[ℝ] ℝ).contDiff
    have hs : (spatialPart : ℝ^4 → ℝ^3) = spatialPartCLM 3 :=
      funext fun z ↦ (spatialPartCLM_eq_spatialPart 3 z).symm
    rw [hs]
    exact h₀.prodMk (spatialPartCLM 3).contDiff
  have heq : (fun y : ℝ^4 ↦ (normalizedPressure 0 gc).uncurry (y 0, spatialPart y)) =ᶠ[𝓝 xt]
      P.pressure := by
    have hnear : ∀ᶠ y : ℝ^4 in 𝓝 xt, y 0 ∈ Metric.closedBall t₀ (δ / 2) := by
      have hc : Continuous (fun y : ℝ^4 ↦ y 0) := by fun_prop
      exact hc.continuousAt.eventually (Metric.closedBall_mem_nhds _ (by positivity))
    filter_upwards [hnear] with y hy
    simp only [Function.uncurry_apply_pair, gc, normalizedPressure_smul,
      χ.one_of_mem_closedBall hy, one_mul, pressure]
  exact ((hpc.comp hmap).contDiffAt).congr_of_eventuallyEq heq.symm

/-- The Euler momentum equation without forcing holds in the open spacetime cylinder. -/
theorem momentum_eq {xt : ℝ^4} (hxt : xt ∈ spacetimeDomain T) :
    materialDerivative 3 P.velocity P.velocity xt + spatialGradient P.pressure xt = 0 := by
  obtain ⟨h0, h1, hx⟩ := hxt
  have hp := (P.contDiffAt_pressure h0 h1).differentiableAt (by simp)
  rw [← timeSpaceCons_spatialPart xt] at hp ⊢
  have hgrad := (P.hasGradientAt_pressure h0 h1 hx).gradient
  ext i
  rw [PiLp.add_apply, PDE.spatialGradient_apply,
    ← PDE.partialDeriv_timeSpaceCons_spatial i _ _ _ hp]
  simp only [pressure_timeSpaceCons]
  rw [← PDE.gradient_apply_eq_partialDeriv, hgrad]
  simp [pressureGradient]

/-- The pressure is even in `z` at interior times. -/
theorem normalizedPressure_coordinateReflection {t : ℝ} (h0 : 0 < t) (h1 : t < T) (x : ℝ^3) :
    normalizedPressure 0 P.pressureGradient t (coordinateReflection (2 : Fin 3) x) =
      normalizedPressure 0 P.pressureGradient t x := by
  set R := coordinateReflectionLinearIsometryEquiv (2 : Fin 3)
  have hR (y : ℝ^3) : coordinateReflection (2 : Fin 3) y = R y := rfl
  simp only [normalizedPressure, sub_zero]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun σ ↦ ?_)
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero]
  rw [hR, ← map_smul, ← hR, P.pressureGradient_coordinateReflection h0 h1, hR]
  exact LinearIsometryEquiv.inner_map_map R _ _

/-- The pressure is `L`-periodic in `z` in the open cylinder at interior times. -/
theorem normalizedPressure_add {t : ℝ} (h0 : 0 < t) (h1 : t < T) {x : ℝ^3}
    (hx : x ∈ Euler.Cylinder.domain) :
    normalizedPressure 0 P.pressureGradient t (x + EuclideanSpace.single (2 : Fin 3) L) =
      normalizedPressure 0 P.pressureGradient t x := by
  set e := EuclideanSpace.single (2 : Fin 3) L
  have hshift {y : ℝ^3} (hy : y ∈ Euler.Cylinder.domain) (c : ℝ) :
      y + EuclideanSpace.single (2 : Fin 3) c ∈ Euler.Cylinder.domain := by
    simpa [Euler.Cylinder.domain, cylindricalRadiusSq] using hy
  let H : ℝ^3 → ℝ := fun z ↦ normalizedPressure 0 P.pressureGradient t (z + e) -
    normalizedPressure 0 P.pressureGradient t z
  have hderiv : ∀ y ∈ Euler.Cylinder.domain, HasFDerivAt H (0 : ℝ^3 →L[ℝ] ℝ) y := by
    intro y hy
    have h₁ := (P.hasGradientAt_pressure h0 h1 (hshift hy L)).hasFDerivAt
    have h₂ := (P.hasGradientAt_pressure h0 h1 hy).hasFDerivAt
    have h₃ := (h₁.comp y ((hasFDerivAt_id y).add_const e)).sub h₂
    rw [P.pressureGradient_add] at h₃
    exact h₃.congr_fderiv (by ext v; simp)
  have hconst : H x = H (EuclideanSpace.single (2 : Fin 3) (-(L / 2))) := by
    refine convex_domain.is_const_of_fderivWithin_eq_zero
      (fun y hy ↦ (hderiv y hy).differentiableAt.differentiableWithinAt) (fun y hy ↦ ?_) hx ?_
    · rw [fderivWithin_of_isOpen isOpen_domain hy]
      exact (hderiv y hy).fderiv
    · simp [Euler.Cylinder.domain, cylindricalRadiusSq]
  have hmid : EuclideanSpace.single (2 : Fin 3) (-(L / 2)) + e =
      coordinateReflection (2 : Fin 3) (EuclideanSpace.single (2 : Fin 3) (-(L / 2))) := by
    ext i
    fin_cases i
    · simp [e]
    · simp [e]
    · simp [e]
      ring
  have hzero : H (EuclideanSpace.single (2 : Fin 3) (-(L / 2))) = 0 := by
    simp only [H]
    rw [hmid, P.normalizedPressure_coordinateReflection h0 h1, sub_self]
  rw [hzero] at hconst
  exact sub_eq_zero.1 hconst

/-- The pressure is `L`-periodic in `z` on the open spacetime cylinder. -/
theorem pressure_add_axialShift {xt : ℝ^4} (hxt : xt ∈ spacetimeDomain T) :
    P.pressure (xt + axialShift L) = P.pressure xt := by
  obtain ⟨h0, h1, hx⟩ := hxt
  rw [← timeSpaceCons_spatialPart xt, timeSpaceCons_add_axialShift, pressure_timeSpaceCons,
    pressure_timeSpaceCons]
  exact P.normalizedPressure_add h0 h1 hx

/-- The initial velocity `u(0, ·)` with zero forcing, as Euler initial-value data. It is smooth
and divergence free on all of `ℝ³`. -/
def initialData : InitialValueData 3 where
  forcing := fun _ ↦ 0
  initialVelocity := fun x ↦ P.velocity (timeSpaceCons 0 x)
  initialVelocity_distributionallyDivergenceFree := by
    have hU := P.contDiff_profileSlice P.swirl_contDiffOn le_rfl P.time_pos
    have hΨ := P.contDiff_profileSlice P.streamFunction_contDiffOn le_rfl P.time_pos
    apply SpatialFieldDivergenceFree.distributionallyDivergenceFree
    · intro x
      exact spatialFieldDivergence_velocitySlice_eq_zero_of_contDiffOn P.isOpen_profileDomain
        (P.swirl_contDiffOn.of_le (by simp)) (P.streamFunction_contDiffOn.of_le (by simp)) 0 x
        (P.mem_profileDomain _ (by simp) (by simpa using P.time_pos))
    · rw [show (fun x ↦ P.velocity (timeSpaceCons 0 x)) =
          axisymmetricVelocity (profileSlice P.swirl 0) (profileSlice P.streamFunction 0) from
        funext (P.velocity_timeSpaceCons 0)]
      exact (contDiff_axisymmetricVelocity hU hΨ).of_le (by simp)

/-- The initial data have zero forcing. -/
@[simp]
theorem initialData_forcing (xt : ℝ^4) : P.initialData.forcing xt = 0 :=
  rfl

/-- The classical Euler solution in the periodic cylinder reconstructed from the profiles:
velocity `spacetimeAxisymmetricVelocity U Ψ`, pressure `ProfileSolution.pressure`, zero
forcing, on `[0, T)`. -/
def smoothSolution : SmoothSolution L P.initialData where
  u := P.velocity
  p := P.pressure
  T := ⟨T, P.time_pos⟩
  period_pos := P.period_pos
  momentum_at := fun xt hxt ↦ by
    change materialDerivative 3 P.velocity P.velocity xt + spatialGradient P.pressure xt = 0
    exact P.momentum_eq hxt
  divergenceFreeOn := fun xt hxt ↦ P.divergenceFreeAt_velocity hxt.1.le hxt.2.1
  velocity_contDiffAt := fun xt hxt ↦ P.contDiffAt_velocity hxt.1.le hxt.2.1
  pressure_contDiffAt := fun xt hxt ↦ P.contDiffAt_pressure hxt.1 hxt.2.1
  velocity_contDiffOn := fun xt hxt ↦
    ((P.contDiffAt_velocity hxt.1.le hxt.2.1).of_le (by simp)).contDiffWithinAt
  wallNormalVelocity_eq_zero := fun xt hxt ↦ P.wallNormalVelocity_velocity hxt
  velocity_periodic := fun xt _ ↦ P.velocity_add_axialShift xt
  pressure_periodic := fun xt hxt ↦ P.pressure_add_axialShift hxt
  continuousWithinAt_initial := fun x _ ↦
    (P.contDiffAt_velocity (xt := timeSpaceCons 0 x) (by simp)
      (by simpa using P.time_pos)).continuousAt.continuousWithinAt
  initial_eq := fun _ _ ↦ rfl

/-- The reconstructed solution has the reconstructed velocity. -/
@[simp]
theorem smoothSolution_u : P.smoothSolution.u = spacetimeAxisymmetricVelocity P.swirl
    P.streamFunction :=
  rfl

/-- The reconstructed solution lives on `[0, T)`. -/
@[simp]
theorem smoothSolution_T : (P.smoothSolution.T : ℝ) = T :=
  rfl

/-- The azimuthal vorticity is bounded by the Cartesian vorticity: off the axis in the open
cylinder, `r |Ω| = |ω^θ| ≤ |curl u|`, with `r` the cylindrical radius and `Ω = ω^θ / r` the
vorticity profile at `(t, r², z)`. -/
theorem mul_abs_vorticity_le_norm_curl {xt : ℝ^4} (hxt : xt ∈ offAxisDomain T) :
    Real.sqrt (cylindricalRadiusSq (spatialPart xt)) *
        |P.vorticity (spacetimeSquaredCylindricalMap xt)| ≤
      ‖spacetimeSpatialCurl P.velocity xt‖ := by
  rw [P.curl_eq_vorticityFromCoefficients hxt]
  set x := spatialPart xt
  set c := spacetimeAxisymmetricVorticityFromCoefficients P.swirl P.vorticity xt
  set Ω₀ := P.vorticity (spacetimeSquaredCylindricalMap xt)
  set r := Real.sqrt (cylindricalRadiusSq x)
  have hs : 0 < cylindricalRadiusSq x := hxt.2
  have hr : 0 < r := Real.sqrt_pos.2 hs
  have hr2 : r ^ 2 = cylindricalRadiusSq x := Real.sq_sqrt hs.le
  set w : ℝ^3 := cartesianVector (-x 1) (x 0) 0
  have hw : ‖w‖ = r := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp [w, r, cylindricalRadiusSq, add_comm]
  have hinner : inner ℝ c w = cylindricalRadiusSq x * Ω₀ := by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp only [c, w, spacetimeAxisymmetricVorticityFromCoefficients, cartesianVector_apply_zero,
      cartesianVector_apply_one, cartesianVector_apply_two, spacetimeSquaredCylindricalLift,
      RCLike.inner_apply, conj_trivial, Ω₀, cylindricalRadiusSq]
    ring
  have hcs := abs_real_inner_le_norm c w
  rw [hinner, hw, abs_mul, abs_of_pos hs, ← hr2] at hcs
  nlinarith [abs_nonneg Ω₀, norm_nonneg c]

end ProfileSolution

/-- The reduction of (6.2)-(6.4) to Cartesian Euler flow: axis-regular meridian fields
`(r U, r Ω, r Ψ)` with profiles smooth on an open set containing `[0, T) × ℝ²`, solving the
meridian system on `(0, T)`, `L`-periodic in `z` and with `U` even and `Ψ` odd in `z`, give a
classical Euler solution in the periodic cylinder on `[0, T)` with zero forcing and velocity
`spacetimeAxisymmetricVelocity U Ψ`. -/
theorem exists_smoothSolution_of_satisfiesMeridianSystemOn {L T : ℝ} (hL : 0 < L) (hT : 0 < T)
    {U Ω Ψ : ℝ^3 → ℝ} {D : Set (ℝ^3)} (hD : IsOpen D)
    (hDT : ∀ q : ℝ^3, 0 ≤ q 0 → q 0 < T → q ∈ D)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U D) (hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω D)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ D)
    (hsystem : SatisfiesMeridianSystemOn (ofProfiles U Ω Ψ) (Set.Ioo 0 T))
    (hUper : ∀ q, U (q + EuclideanSpace.single (2 : Fin 3) L) = U q)
    (hΨper : ∀ q, Ψ (q + EuclideanSpace.single (2 : Fin 3) L) = Ψ q)
    (hUeven : IsEvenUnderCoordinateReflection (2 : Fin 3) U)
    (hΨodd : IsOddUnderCoordinateReflection (2 : Fin 3) Ψ) :
    ∃ data : InitialValueData 3, data.forcing = 0 ∧
      (∀ x, data.initialVelocity x = spacetimeAxisymmetricVelocity U Ψ (timeSpaceCons 0 x)) ∧
      ∃ sol : SmoothSolution L data,
        sol.u = spacetimeAxisymmetricVelocity U Ψ ∧ (sol.T : ℝ) = T := by
  have hmem {q : ℝ^3} (hq : q ∈ profileStrip (Set.Ioo 0 T)) : D ∈ 𝓝 q :=
    hD.mem_nhds (hDT q hq.1.1.le hq.1.2)
  have hreg : HasProfileRegularityOn U Ω Ψ (Set.Ioo 0 T) :=
    ⟨fun q hq ↦ ((hU.contDiffAt (hmem hq)).of_le (by simp)),
      fun q hq ↦ ((hΩ.contDiffAt (hmem hq)).of_le (by simp)),
      fun q hq ↦ ((hΨ.contDiffAt (hmem hq)).of_le (by simp))⟩
  let P : ProfileSolution L T :=
    { swirl := U
      vorticity := Ω
      streamFunction := Ψ
      profileDomain := D
      isOpen_profileDomain := hD
      mem_profileDomain := hDT
      swirl_contDiffOn := hU
      vorticity_contDiffOn := hΩ
      streamFunction_contDiffOn := hΨ
      equations := (satisfiesMeridianSystemOn_ofProfiles_iff hreg).1 hsystem
      period_pos := hL
      time_pos := hT
      swirl_periodic := hUper
      streamFunction_periodic := hΨper
      swirl_even := hUeven
      streamFunction_odd := hΨodd }
  exact ⟨P.initialData, rfl, fun _ ↦ rfl, P.smoothSolution, rfl, rfl⟩

/-- Rigid rotation `u = ω₀ e_z × x` with angular velocity `ω₀`: the profiles `U = ω₀`, `Ω = 0`,
`Ψ = 0`. It is a steady solution in the reflection class, with the centrifugal pressure. -/
def ProfileSolution.rigidRotation {L T : ℝ} (hL : 0 < L) (hT : 0 < T) (ω₀ : ℝ) :
    ProfileSolution L T where
  swirl := fun _ ↦ ω₀
  vorticity := fun _ ↦ 0
  streamFunction := fun _ ↦ 0
  profileDomain := Set.univ
  isOpen_profileDomain := isOpen_univ
  mem_profileDomain := fun _ _ _ ↦ Set.mem_univ _
  swirl_contDiffOn := contDiffOn_const
  vorticity_contDiffOn := contDiffOn_const
  streamFunction_contDiffOn := contDiffOn_const
  equations :=
    { swirl_equation := fun q _ ↦ by
        simp [squaredRadiusEulerSwirlResidual, squaredRadiusMaterialDerivative]
      vorticity_equation := fun q _ ↦ by
        simp [squaredRadiusEulerVorticityResidual, squaredRadiusMaterialDerivative]
      streamFunction_equation := fun q _ ↦ by
        have h0 (i : Fin 3) : (∂[i] (fun _ : ℝ^3 ↦ (0 : ℝ))) = fun _ ↦ 0 :=
          funext fun _ ↦ PDE.partialDeriv_const 0
        simp [spacetimeSquaredRadiusDiffusion, h0]
      wall := fun _ _ _ ↦ rfl }
  period_pos := hL
  time_pos := hT
  swirl_periodic := fun _ ↦ rfl
  streamFunction_periodic := fun _ ↦ rfl
  swirl_even := fun _ ↦ rfl
  streamFunction_odd := fun _ ↦ by simp

/-- The rigid rotation has velocity `ω₀ (-x₁, x₀, 0)`. -/
theorem ProfileSolution.rigidRotation_velocity {L T : ℝ} (hL : 0 < L) (hT : 0 < T) (ω₀ t : ℝ)
    (x : ℝ^3) :
    (ProfileSolution.rigidRotation hL hT ω₀).velocity (timeSpaceCons t x) =
      cartesianVector (-ω₀ * x 1) (ω₀ * x 0) 0 := by
  rw [ProfileSolution.velocity_timeSpaceCons]
  have hslice : profileSlice (fun _ : ℝ^3 ↦ (0 : ℝ)) t = fun _ ↦ 0 := rfl
  ext i
  fin_cases i <;>
    simp [ProfileSolution.rigidRotation, hslice, axisymmetricVelocity_apply_zero,
      axisymmetricVelocity_apply_one, axisymmetricVelocity_apply_two, squaredCylindricalLift,
      profileSlice, mul_comm]

end

end Euler.Cylinder
