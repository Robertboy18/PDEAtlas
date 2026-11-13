/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Axisymmetric
public import PDE.Fluid.Incompressible.Vorticity
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Cartesian reconstruction of axis-regular velocity fields

Axisymmetric vector fields on `ℝ^3` are reconstructed from scalar profiles in
squared-radius coordinates `(s, z)`, where `s = x₁² + x₂²`. Writing the profiles
in `s` rather than in the cylindrical radius avoids every division by the radius
and gives formulas that remain smooth on the symmetry axis.

For a normalized streamfunction profile `Ψ(s,z)`, the meridional velocity is

```text
(-x₁ Ψ_z, -x₂ Ψ_z, 2 Ψ + 2 (x₁² + x₂²) Ψ_s).
```

For a swirl profile `U(s,z)`, the azimuthal velocity is

```text
(-x₂ U, x₁ U, 0).
```

Both fields are divergence free, so for smooth profiles their sum is a smooth,
divergence-free axisymmetric velocity on all of `ℝ^3`, including the axis.

## Main results

* `contDiff_axisymmetricVelocity`: smooth profiles give a globally smooth velocity;
  `contDiff_meridionalVelocity_of_succ` and `contDiff_swirlVelocity` track finite regularity
  (a `C^(n+1)` streamfunction gives a `C^n` meridional field, swirl loses nothing).
* `spatialFieldDivergenceFree_axisymmetricVelocity`: the reconstruction is divergence free on
  all of `ℝ^3` for a `C¹` swirl profile and a `C²` streamfunction profile.
* `isEquivariantUnderAxisRotation_axisymmetricVelocity`: the reconstructed field is equivariant
  under rotations about the `x₃` axis (`IsEquivariantUnderAxisRotation`), that is, axisymmetric.
* `axisymmetricVelocity_transverse_eq_zero_of_mem_symmetryAxis`,
  `axisymmetricVelocity_apply_two_of_mem_symmetryAxis`: on the axis the velocity is purely
  axial with value `2 Ψ(0, z)`.
* `meridionalVelocityOfScalar`, `meridionalVelocityOfScalar_squaredCylindricalLift`,
  `meridionalVelocityOfScalar_meridianLift_off_axis`: the same meridional formula written for a
  Cartesian scalar `q`, with the cylindrical components `u_r = -r ψ_z`, `u_z = 2ψ + r ψ_r` off
  the axis; `spatialCurl_azimuthalScalar_eq_meridionalVelocityOfScalar` shows it is the curl of
  `(-y q, x q, 0)`.

## How it works

The lift `squaredCylindricalLift Φ` is `Φ` composed with the polynomial map `squaredCylindricalMap`,
`x ↦ (x₁² + x₂², x₃)`, so it is as smooth as `Φ` (`contDiff_squaredCylindricalLift`). By the chain
rule its derivative is `2 xᵢ ∂_s Φ` in the two transverse directions and `∂_z Φ` in the axial one
(`partialDeriv_zero_squaredCylindricalLift`, `partialDeriv_one_squaredCylindricalLift`,
`partialDeriv_two_squaredCylindricalLift`), with no division by the radius. Each velocity component
is a polynomial in `x` times lifts of `U`, `Ψ` and the first derivatives of `Ψ`. The regularity
statements follow, and the divergence of the meridional field cancels after one exchange of `∂_s`
and `∂_z` (`spatialFieldDivergence_meridionalVelocity_eq_zero`). The lifts are invariant under
rotations about the axis (`squaredCylindricalLift_axisRotation`), while the coordinate factors
rotate as a vector, which gives equivariance. The cylindrical components need the radius
`r = √(x₁² + x₂²)`, which is differentiable only off the axis, so
`meridionalVelocityOfScalar_meridianLift_off_axis` is proved at positive radius by the ordinary
chain rule.

## Implementation notes

The normalisation behind these formulas is the classical one for axisymmetric flow with swirl in
cylindrical coordinates `(r, θ, z)`: the Stokes streamfunction is `ψ(r, z) = r² Ψ(r², z)`, the
meridional velocity is `u_r = -ψ_z / r`, `u_z = ψ_r / r`, and the swirl is `u_θ = r U(r², z)`.
Substituting gives `u_r = -r Ψ_z` and `u_z = 2Ψ + 2r² Ψ_s`, which in Cartesian components are the
expressions displayed above; equivalently, with `ψ₁(r, z) = Ψ(r², z)` this is the axial velocity
`u_z = 2ψ₁ + r ∂_r ψ₁` of the reduced Navier–Stokes equations. The reduced swirl `U = u_θ / r` is
the nonsingular variable of Hou and Li.

Many of the coordinate computations in the proofs (partial derivatives, smoothness, divergences
and curls) are closed by the `cas` tactic of SymLean, our computer algebra system for Lean.

## References

* T. Y. Hou and C. Li, "Dynamic stability of the three-dimensional axisymmetric Navier-Stokes
  equations with swirl", Comm. Pure Appl. Math. 61 (2008), no. 5, 661-697, for the reduced swirl
  `u_θ / r`.
  <https://doi.org/10.1002/cpa.20212>
* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 2, for the cylindrical form of
  axisymmetric flows with swirl.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

open PDE (partialDeriv divergence)

namespace AxisymmetricFlow

open EuclideanSpace
open PDE.CoordinateSystems
open IncompressibleFlow

noncomputable section

/-- The smooth Cartesian map `(x₁,x₂,x₃) ↦ (x₁²+x₂²,x₃)`. -/
def squaredCylindricalMap (x : ℝ^3) : ℝ^2 :=
  WithLp.toLp 2 ![cylindricalRadiusSq x, axialCoordinate x]

/-- The first squared-cylindrical coordinate is `s = x₁² + x₂²`. -/
@[simp]
theorem squaredCylindricalMap_apply_zero (x : ℝ^3) :
    squaredCylindricalMap x 0 = cylindricalRadiusSq x := by
  simp [squaredCylindricalMap]

/-- The second squared-cylindrical coordinate is the axial coordinate `x₃`. -/
@[simp]
theorem squaredCylindricalMap_apply_one (x : ℝ^3) :
    squaredCylindricalMap x 1 = axialCoordinate x := by
  simp [squaredCylindricalMap]

/-- The squared-cylindrical map written through the cylindrical radius rather than
its square. -/
theorem squaredCylindricalMap_eq_toLp_cylindricalRadius_sq (x : ℝ^3) :
    squaredCylindricalMap x =
      WithLp.toLp 2 ![cylindricalRadius x ^ 2, axialCoordinate x] := by
  simp [squaredCylindricalMap, cylindricalRadius_sq]

/-- The squared cylindrical coordinate map is smooth across the symmetry
axis. -/
theorem contDiff_squaredCylindricalMap :
    ContDiff ℝ (⊤ : ℕ∞) squaredCylindricalMap := by
  apply (contDiff_piLp (2 : ENNReal)).2
  intro i
  fin_cases i
  · simpa [cylindricalRadiusSq] using
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ^3 ↦ x 0 ^ 2 + x 1 ^ 2))
  · simpa [axialCoordinate] using
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^3 ↦ x 2))

/-- Rotating about the symmetry axis preserves `s = x₁² + x₂²` and `x₃`, so the squared-cylindrical
coordinates are rotation invariant. -/
@[simp]
theorem squaredCylindricalMap_axisRotation (θ : ℝ) (x : ℝ^3) :
    squaredCylindricalMap (axisRotation θ x) = squaredCylindricalMap x := by
  ext i
  fin_cases i
  · simp
  · simp

/-- Lift a scalar profile in squared-radius coordinates to Cartesian space. -/
def squaredCylindricalLift (Φ : ℝ^2 → ℝ) (x : ℝ^3) : ℝ :=
  Φ (squaredCylindricalMap x)

/-- Squared-radius lifting preserves every finite or infinite degree of
smoothness. -/
theorem contDiff_squaredCylindricalLift {n : ℕ∞} {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ n Φ) :
    ContDiff ℝ n (squaredCylindricalLift Φ) := by
  exact hΦ.comp (contDiff_squaredCylindricalMap.of_le (by simp))

/-- A squared-radius lift is a scalar axisymmetric function: it is invariant under rotations about
the symmetry axis. -/
@[simp]
theorem squaredCylindricalLift_axisRotation
    (Φ : ℝ^2 → ℝ) (θ : ℝ) (x : ℝ^3) :
    squaredCylindricalLift Φ (axisRotation θ x) =
      squaredCylindricalLift Φ x := by
  simp [squaredCylindricalLift]

/-- The squared cylindrical radius `x₀² + x₁²` has coordinate derivative `2 x₀` in direction
`0`. -/
theorem partialDeriv_zero_cylindricalRadiusSq (x : ℝ^3) :
    (∂[(0 : Fin 3)] cylindricalRadiusSq) x = 2 * x 0 := by
  unfold cylindricalRadiusSq
  cas

/-- The squared cylindrical radius `x₀² + x₁²` has coordinate derivative `2 x₁` in direction
`1`. -/
theorem partialDeriv_one_cylindricalRadiusSq (x : ℝ^3) :
    (∂[(1 : Fin 3)] cylindricalRadiusSq) x = 2 * x 1 := by
  unfold cylindricalRadiusSq
  cas

/-- The squared cylindrical radius `x₀² + x₁²` does not depend on the axial coordinate `x₂`. -/
theorem partialDeriv_two_cylindricalRadiusSq (x : ℝ^3) :
    (∂[(2 : Fin 3)] cylindricalRadiusSq) x = 0 := by
  unfold cylindricalRadiusSq
  cas

private theorem partialDeriv_comp_euclidean {n m : ℕ}
    (i : Fin n) (u : ℝ^m → ℝ) (Φ : ℝ^n → ℝ^m) (x : ℝ^n)
    (hu : DifferentiableAt ℝ u (Φ x)) (hΦ : DifferentiableAt ℝ Φ x) :
    (∂[i] (fun y ↦ u (Φ y))) x =
      ∑ j : Fin m,
        (∂[j] u) (Φ x) * (∂[i] (fun y ↦ Φ y j)) x := by
  have hcomp := fderiv_comp x hu hΦ
  have happ := congrArg
    (fun L : ℝ^n →L[ℝ] ℝ ↦
      L (EuclideanSpace.single i (1 : ℝ))) hcomp
  change (∂[i] (fun y ↦ u (Φ y))) x =
    (fderiv ℝ u (Φ x))
      ((fderiv ℝ Φ x) (EuclideanSpace.single i (1 : ℝ))) at happ
  rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul] at happ
  apply happ.trans
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact PDE.partialDeriv_apply i j hΦ

/-- Derivative of a squared-radius lift in the first transverse direction. -/
theorem partialDeriv_zero_squaredCylindricalLift {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (x : ℝ^3) :
    (∂[(0 : Fin 3)] (squaredCylindricalLift Φ)) x =
      2 * x 0 * (∂[(0 : Fin 2)] Φ) (squaredCylindricalMap x) := by
  calc
    _ = ∑ j : Fin 2,
        (∂[j] Φ) (squaredCylindricalMap x) *
          (∂[(0 : Fin 3)]
            (fun y ↦ squaredCylindricalMap y j)) x :=
      partialDeriv_comp_euclidean 0 Φ squaredCylindricalMap x
        (hΦ.differentiable one_ne_zero).differentiableAt
        (contDiff_squaredCylindricalMap.differentiable (by simp)).differentiableAt
    _ = _ := by
      simp only [Fin.sum_univ_two, squaredCylindricalMap_apply_zero,
        squaredCylindricalMap_apply_one]
      rw [partialDeriv_zero_cylindricalRadiusSq]
      simp [axialCoordinate, PDE.partialDeriv_coord]
      ring

/-- Derivative of a squared-radius lift in the second transverse direction. -/
theorem partialDeriv_one_squaredCylindricalLift {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (x : ℝ^3) :
    (∂[(1 : Fin 3)] (squaredCylindricalLift Φ)) x =
      2 * x 1 * (∂[(0 : Fin 2)] Φ) (squaredCylindricalMap x) := by
  calc
    _ = ∑ j : Fin 2,
        (∂[j] Φ) (squaredCylindricalMap x) *
          (∂[(1 : Fin 3)]
            (fun y ↦ squaredCylindricalMap y j)) x :=
      partialDeriv_comp_euclidean 1 Φ squaredCylindricalMap x
        (hΦ.differentiable one_ne_zero).differentiableAt
        (contDiff_squaredCylindricalMap.differentiable (by simp)).differentiableAt
    _ = _ := by
      simp only [Fin.sum_univ_two, squaredCylindricalMap_apply_zero,
        squaredCylindricalMap_apply_one]
      rw [partialDeriv_one_cylindricalRadiusSq]
      simp [axialCoordinate, PDE.partialDeriv_coord]
      ring

/-- Derivative of a squared-radius lift in the axial direction. -/
theorem partialDeriv_two_squaredCylindricalLift {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (x : ℝ^3) :
    (∂[(2 : Fin 3)] (squaredCylindricalLift Φ)) x =
      (∂[(1 : Fin 2)] Φ) (squaredCylindricalMap x) := by
  calc
    _ = ∑ j : Fin 2,
        (∂[j] Φ) (squaredCylindricalMap x) *
          (∂[(2 : Fin 3)]
            (fun y ↦ squaredCylindricalMap y j)) x :=
      partialDeriv_comp_euclidean 2 Φ squaredCylindricalMap x
        (hΦ.differentiable one_ne_zero).differentiableAt
        (contDiff_squaredCylindricalMap.differentiable (by simp)).differentiableAt
    _ = _ := by
      simp only [Fin.sum_univ_two, squaredCylindricalMap_apply_zero,
        squaredCylindricalMap_apply_one]
      rw [partialDeriv_two_cylindricalRadiusSq]
      simp [axialCoordinate, PDE.partialDeriv_coord]

/-- Package three scalar components as a Cartesian vector. -/
def cartesianVector (a b c : ℝ) : ℝ^3 :=
  WithLp.toLp 2 ![a, b, c]

/-- First component of `cartesianVector a b c`. -/
@[simp]
theorem cartesianVector_apply_zero (a b c : ℝ) :
    cartesianVector a b c 0 = a := by
  simp [cartesianVector]

/-- Second component of `cartesianVector a b c`. -/
@[simp]
theorem cartesianVector_apply_one (a b c : ℝ) :
    cartesianVector a b c 1 = b := by
  simp [cartesianVector]

/-- Third component of `cartesianVector a b c`. -/
@[simp]
theorem cartesianVector_apply_two (a b c : ℝ) :
    cartesianVector a b c 2 = c := by
  simp [cartesianVector]

/-- The meridional velocity generated by a normalized squared-radius
streamfunction profile `Ψ`. -/
def meridionalVelocity (Ψ : ℝ^2 → ℝ) (x : ℝ^3) : ℝ^3 :=
  let ψ := squaredCylindricalLift Ψ x
  let ψS := squaredCylindricalLift (fun q ↦ (∂[(0 : Fin 2)] Ψ) q) x
  let ψZ := squaredCylindricalLift (fun q ↦ (∂[(1 : Fin 2)] Ψ) q) x
  cartesianVector
    (-x 0 * ψZ)
    (-x 1 * ψZ)
    (2 * ψ + 2 * cylindricalRadiusSq x * ψS)

/-- The azimuthal velocity generated by a squared-radius swirl profile `U`. -/
def swirlVelocity (U : ℝ^2 → ℝ) (x : ℝ^3) : ℝ^3 :=
  let u := squaredCylindricalLift U x
  cartesianVector (-x 1 * u) (x 0 * u) 0

/-- The sum of meridional and swirl velocity reconstructed from squared-radius
profiles. -/
def axisymmetricVelocity (U Ψ : ℝ^2 → ℝ) (x : ℝ^3) : ℝ^3 :=
  meridionalVelocity Ψ x + swirlVelocity U x

/-- The `x₁` component of the meridional velocity is `-x₁ Ψ_z`, the Cartesian form of
`u_r = -r Ψ_z`. -/
@[simp]
theorem meridionalVelocity_apply_zero (Ψ : ℝ^2 → ℝ) (x : ℝ^3) :
    meridionalVelocity Ψ x 0 =
      -x 0 * squaredCylindricalLift
        (fun q ↦ (∂[(1 : Fin 2)] Ψ) q) x := by
  simp [meridionalVelocity]

/-- The `x₂` component of the meridional velocity is `-x₂ Ψ_z`. -/
@[simp]
theorem meridionalVelocity_apply_one (Ψ : ℝ^2 → ℝ) (x : ℝ^3) :
    meridionalVelocity Ψ x 1 =
      -x 1 * squaredCylindricalLift
        (fun q ↦ (∂[(1 : Fin 2)] Ψ) q) x := by
  simp [meridionalVelocity]

/-- The axial component of the meridional velocity is `2Ψ + 2s Ψ_s`, which is `u_z = ψ_r / r` for
the Stokes streamfunction `ψ = r² Ψ(r², z)`. -/
@[simp]
theorem meridionalVelocity_apply_two (Ψ : ℝ^2 → ℝ) (x : ℝ^3) :
    meridionalVelocity Ψ x 2 =
      2 * squaredCylindricalLift Ψ x +
        2 * cylindricalRadiusSq x *
          squaredCylindricalLift
            (fun q ↦ (∂[(0 : Fin 2)] Ψ) q) x := by
  simp [meridionalVelocity]

/-- The `x₁` component of the swirl velocity is `-x₂ U`, the Cartesian form of `u_θ = r U`. -/
@[simp]
theorem swirlVelocity_apply_zero (U : ℝ^2 → ℝ) (x : ℝ^3) :
    swirlVelocity U x 0 = -x 1 * squaredCylindricalLift U x := by
  simp [swirlVelocity]

/-- The `x₂` component of the swirl velocity is `x₁ U`. -/
@[simp]
theorem swirlVelocity_apply_one (U : ℝ^2 → ℝ) (x : ℝ^3) :
    swirlVelocity U x 1 = x 0 * squaredCylindricalLift U x := by
  simp [swirlVelocity]

/-- The swirl velocity has no axial component. -/
@[simp]
theorem swirlVelocity_apply_two (U : ℝ^2 → ℝ) (x : ℝ^3) :
    swirlVelocity U x 2 = 0 := by
  simp [swirlVelocity]

/-- The `x₁` component of the full velocity: `-x₁ Ψ_z` from the meridional part and `-x₂ U`
from the swirl. -/
@[simp]
theorem axisymmetricVelocity_apply_zero (U Ψ : ℝ^2 → ℝ) (x : ℝ^3) :
    axisymmetricVelocity U Ψ x 0 =
      -x 0 * squaredCylindricalLift
          (fun q ↦ (∂[(1 : Fin 2)] Ψ) q) x -
        x 1 * squaredCylindricalLift U x := by
  simp [axisymmetricVelocity]
  ring

/-- The `x₂` component of the full velocity: `-x₂ Ψ_z` from the meridional part and `x₁ U` from
the swirl. -/
@[simp]
theorem axisymmetricVelocity_apply_one (U Ψ : ℝ^2 → ℝ) (x : ℝ^3) :
    axisymmetricVelocity U Ψ x 1 =
      -x 1 * squaredCylindricalLift
          (fun q ↦ (∂[(1 : Fin 2)] Ψ) q) x +
        x 0 * squaredCylindricalLift U x := by
  simp [axisymmetricVelocity]

/-- The axial component of the full velocity comes from the streamfunction alone and equals
`2Ψ + 2s Ψ_s`. -/
@[simp]
theorem axisymmetricVelocity_apply_two (U Ψ : ℝ^2 → ℝ) (x : ℝ^3) :
    axisymmetricVelocity U Ψ x 2 =
      2 * squaredCylindricalLift Ψ x +
        2 * cylindricalRadiusSq x *
          squaredCylindricalLift
            (fun q ↦ (∂[(0 : Fin 2)] Ψ) q) x := by
  simp [axisymmetricVelocity]

/-- Setting the swirl profile to zero recovers the meridional
reconstruction. -/
@[simp]
theorem axisymmetricVelocity_zero_left (Ψ : ℝ^2 → ℝ) :
    axisymmetricVelocity (fun _ ↦ 0) Ψ = meridionalVelocity Ψ := by
  funext x
  ext i
  fin_cases i <;> simp [axisymmetricVelocity, swirlVelocity,
    squaredCylindricalLift]

/-- The meridional reconstruction is equivariant under rotations around the
symmetry axis. -/
theorem isEquivariantUnderAxisRotation_meridionalVelocity (Ψ : ℝ^2 → ℝ) :
    IsEquivariantUnderAxisRotation (meridionalVelocity Ψ) := by
  intro θ x
  ext i
  fin_cases i
  · change meridionalVelocity Ψ (axisRotation θ x) (0 : Fin 3) =
      axisRotation θ (meridionalVelocity Ψ x) (0 : Fin 3)
    simp only [meridionalVelocity_apply_zero, meridionalVelocity_apply_one,
      axisRotation_apply_zero, squaredCylindricalLift_axisRotation]
    ring
  · change meridionalVelocity Ψ (axisRotation θ x) (1 : Fin 3) =
      axisRotation θ (meridionalVelocity Ψ x) (1 : Fin 3)
    simp only [meridionalVelocity_apply_zero, meridionalVelocity_apply_one,
      axisRotation_apply_one, squaredCylindricalLift_axisRotation]
    ring
  · change meridionalVelocity Ψ (axisRotation θ x) (2 : Fin 3) =
      axisRotation θ (meridionalVelocity Ψ x) (2 : Fin 3)
    simp only [meridionalVelocity_apply_two, axisRotation_apply_two,
      squaredCylindricalLift_axisRotation, cylindricalRadiusSq_axisRotation]

/-- The swirl reconstruction is equivariant under rotations around the
symmetry axis. -/
theorem isEquivariantUnderAxisRotation_swirlVelocity (U : ℝ^2 → ℝ) :
    IsEquivariantUnderAxisRotation (swirlVelocity U) := by
  intro θ x
  ext i
  fin_cases i
  · change swirlVelocity U (axisRotation θ x) (0 : Fin 3) =
      axisRotation θ (swirlVelocity U x) (0 : Fin 3)
    simp only [swirlVelocity_apply_zero, swirlVelocity_apply_one,
      axisRotation_apply_zero, axisRotation_apply_one,
      squaredCylindricalLift_axisRotation]
    ring
  · change swirlVelocity U (axisRotation θ x) (1 : Fin 3) =
      axisRotation θ (swirlVelocity U x) (1 : Fin 3)
    simp only [swirlVelocity_apply_zero, swirlVelocity_apply_one,
      axisRotation_apply_zero, axisRotation_apply_one,
      squaredCylindricalLift_axisRotation]
    ring
  · change swirlVelocity U (axisRotation θ x) (2 : Fin 3) =
      axisRotation θ (swirlVelocity U x) (2 : Fin 3)
    simp

/-- The full reconstructed velocity is an axisymmetric Cartesian vector
field. -/
theorem isEquivariantUnderAxisRotation_axisymmetricVelocity
    (U Ψ : ℝ^2 → ℝ) :
    IsEquivariantUnderAxisRotation (axisymmetricVelocity U Ψ) := by
  intro θ x
  rw [axisymmetricVelocity]
  rw [isEquivariantUnderAxisRotation_meridionalVelocity Ψ θ x]
  rw [isEquivariantUnderAxisRotation_swirlVelocity U θ x]
  ext i
  fin_cases i <;> simp [axisRotation] <;> ring

/-- A Cartesian vector built from three `C^n` scalar components is `C^n`. -/
theorem contDiff_cartesianVector {E : Type*} {n : ℕ∞}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : E → ℝ} (ha : ContDiff ℝ n a)
    (hb : ContDiff ℝ n b)
    (hc : ContDiff ℝ n c) :
    ContDiff ℝ n (fun x ↦ cartesianVector (a x) (b x) (c x)) := by
  apply (contDiff_piLp (2 : ENNReal)).2
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa using hc

/-- A `C^(n+1)` normalized streamfunction reconstructs to a `C^n` meridional
velocity. In particular, a `C¹` profile gives a continuous velocity. -/
theorem contDiff_meridionalVelocity_of_succ {n : ℕ∞} {Ψ : ℝ^2 → ℝ}
    (hΨ : ContDiff ℝ (n + 1) Ψ) :
    ContDiff ℝ n (meridionalVelocity Ψ) := by
  have hΨDeriv : ContDiff ℝ n (fderiv ℝ Ψ) := hΨ.fderiv_right (by simp)
  have hΨS : ContDiff ℝ n
      (fun q ↦ (∂[(0 : Fin 2)] Ψ) q) :=
    hΨDeriv.clm_apply contDiff_const
  have hΨZ : ContDiff ℝ n
      (fun q ↦ (∂[(1 : Fin 2)] Ψ) q) :=
    hΨDeriv.clm_apply contDiff_const
  have hψ : ContDiff ℝ n (squaredCylindricalLift Ψ) :=
    contDiff_squaredCylindricalLift (hΨ.of_le (by simp))
  have hψS := contDiff_squaredCylindricalLift hΨS
  have hψZ := contDiff_squaredCylindricalLift hΨZ
  have hx0 : ContDiff ℝ n (fun x : ℝ^3 ↦ x 0) := by
    cas
  have hx1 : ContDiff ℝ n (fun x : ℝ^3 ↦ x 1) := by
    cas
  have hs : ContDiff ℝ n cylindricalRadiusSq := by
    change ContDiff ℝ n (fun x : ℝ^3 ↦ x 0 ^ 2 + x 1 ^ 2)
    fun_prop
  exact contDiff_cartesianVector
    (hx0.neg.mul hψZ)
    (hx1.neg.mul hψZ)
    ((contDiff_const.mul hψ).add ((contDiff_const.mul hs).mul hψS))

/-- A smooth normalized streamfunction profile reconstructs to a globally
smooth meridional velocity. -/
theorem contDiff_meridionalVelocity {Ψ : ℝ^2 → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (meridionalVelocity Ψ) :=
  contDiff_meridionalVelocity_of_succ hΨ

/-- Swirl reconstruction preserves every finite or infinite degree of
regularity, including continuity. -/
theorem contDiff_swirlVelocity {n : ℕ∞} {U : ℝ^2 → ℝ}
    (hU : ContDiff ℝ n U) :
    ContDiff ℝ n (swirlVelocity U) := by
  have hu := contDiff_squaredCylindricalLift hU
  have hx0 : ContDiff ℝ n (fun x : ℝ^3 ↦ x 0) := by
    cas
  have hx1 : ContDiff ℝ n (fun x : ℝ^3 ↦ x 1) := by
    cas
  exact contDiff_cartesianVector (hx1.neg.mul hu) (hx0.mul hu) contDiff_const

/-- A `C²` normalized streamfunction profile reconstructs to a `C¹`
meridional velocity. -/
theorem contDiff_one_meridionalVelocity {Ψ : ℝ^2 → ℝ}
    (hΨ : ContDiff ℝ 2 Ψ) :
    ContDiff ℝ 1 (meridionalVelocity Ψ) :=
  contDiff_meridionalVelocity_of_succ hΨ

/-- A `C¹` swirl profile reconstructs to a `C¹` azimuthal velocity. -/
theorem contDiff_one_swirlVelocity {U : ℝ^2 → ℝ}
    (hU : ContDiff ℝ 1 U) :
    ContDiff ℝ 1 (swirlVelocity U) :=
  contDiff_swirlVelocity hU

/-- Smooth squared-radius profiles reconstruct to a globally smooth velocity,
including on the symmetry axis. -/
theorem contDiff_axisymmetricVelocity {U Ψ : ℝ^2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (axisymmetricVelocity U Ψ) :=
  (contDiff_meridionalVelocity hΨ).add (contDiff_swirlVelocity hU)

/-- The meridional streamfunction reconstruction is divergence free. -/
theorem spatialFieldDivergence_meridionalVelocity_eq_zero
    {Ψ : ℝ^2 → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (x : ℝ^3) :
    ∇· (meridionalVelocity Ψ) x = 0 := by
  have hΨone : ContDiff ℝ 1 Ψ := hΨ.of_le (by norm_num)
  have hΨS : ContDiff ℝ 1 (fun q ↦ (∂[(0 : Fin 2)] Ψ) q) := PDE.contDiff_partialDeriv_of_succ hΨ
  have hΨZ : ContDiff ℝ 1 (fun q ↦ (∂[(1 : Fin 2)] Ψ) q) := PDE.contDiff_partialDeriv_of_succ hΨ
  have hψDiff : DifferentiableAt ℝ (squaredCylindricalLift Ψ) x :=
    (contDiff_squaredCylindricalLift hΨone).contDiffAt.differentiableAt_one
  have hψSDiff : DifferentiableAt ℝ (squaredCylindricalLift (fun q ↦ (∂[(0 : Fin 2)] Ψ) q)) x :=
    (contDiff_squaredCylindricalLift hΨS).contDiffAt.differentiableAt_one
  have hψZDiff : DifferentiableAt ℝ (squaredCylindricalLift (fun q ↦ (∂[(1 : Fin 2)] Ψ) q)) x :=
    (contDiff_squaredCylindricalLift hΨZ).contDiffAt.differentiableAt_one
  have hsDiff : DifferentiableAt ℝ cylindricalRadiusSq x := by
    change DifferentiableAt ℝ (fun y : ℝ^3 ↦ y 0 ^ 2 + y 1 ^ 2) x
    fun_prop
  have hnegCoordZero : (∂[(0 : Fin 3)] (fun y : ℝ^3 ↦ -y 0)) x = -1 := by cas
  have hnegCoordOne : (∂[(1 : Fin 3)] (fun y : ℝ^3 ↦ -y 1)) x = -1 := by cas
  have h₁ : DifferentiableAt ℝ (fun y ↦ 2 * squaredCylindricalLift Ψ y) x :=
    (differentiableAt_const (c := (2 : ℝ))).mul hψDiff
  have h₂ : DifferentiableAt ℝ (fun y ↦ 2 * cylindricalRadiusSq y *
      squaredCylindricalLift (fun q ↦ (∂[(0 : Fin 2)] Ψ) q) y) x :=
    ((differentiableAt_const (c := (2 : ℝ))).mul hsDiff).mul hψSDiff
  simp only [divergence, Fin.sum_univ_three,
    meridionalVelocity_apply_zero, meridionalVelocity_apply_one,
    meridionalVelocity_apply_two]
  rw [PDE.partialDeriv_mul (by fun_prop) hψZDiff, PDE.partialDeriv_mul (by fun_prop) hψZDiff,
    PDE.partialDeriv_add h₁ h₂,
    PDE.partialDeriv_mul (by fun_prop) hψDiff, PDE.partialDeriv_mul (by fun_prop) hψSDiff,
    PDE.partialDeriv_mul (differentiableAt_const (c := (2 : ℝ))) hsDiff,
    partialDeriv_zero_squaredCylindricalLift hΨZ, partialDeriv_one_squaredCylindricalLift hΨZ,
    partialDeriv_two_squaredCylindricalLift hΨone, partialDeriv_two_squaredCylindricalLift hΨS]
  simp only [hnegCoordZero, hnegCoordOne, PDE.partialDeriv_const,
    partialDeriv_two_cylindricalRadiusSq, zero_mul, neg_mul, one_mul,
    zero_add]
  rw [PDE.partialDeriv_partialDeriv_comm (0 : Fin 2) (1 : Fin 2) hΨ]
  simp only [squaredCylindricalLift]
  rw [show cylindricalRadiusSq x = x 0 ^ 2 + x 1 ^ 2 by rfl]
  ring

/-- The swirl field of a `C¹` squared-radius profile is divergence free. -/
theorem spatialFieldDivergence_swirlVelocity_eq_zero
    {U : ℝ^2 → ℝ} (hU : ContDiff ℝ 1 U) (x : ℝ^3) :
    ∇· (swirlVelocity U) x = 0 := by
  have huDiff : DifferentiableAt ℝ (squaredCylindricalLift U) x :=
    (contDiff_squaredCylindricalLift hU).contDiffAt.differentiableAt_one
  have hnegCoordOne :
      (∂[(0 : Fin 3)] (fun y : ℝ^3 ↦ -y 1)) x = 0 := by
    cas
  simp only [divergence, Fin.sum_univ_three,
    swirlVelocity_apply_zero, swirlVelocity_apply_one, swirlVelocity_apply_two]
  rw [PDE.partialDeriv_mul (by fun_prop) huDiff, PDE.partialDeriv_mul (by fun_prop) huDiff,
    partialDeriv_zero_squaredCylindricalLift hU, partialDeriv_one_squaredCylindricalLift hU,
    hnegCoordOne, PDE.partialDeriv_const]
  simp only [PDE.partialDeriv_coord]
  norm_num
  ring

/-- The velocity reconstructed from a `C¹` swirl profile and a `C²` streamfunction profile is
divergence free on all of Cartesian space. -/
theorem spatialFieldDivergence_axisymmetricVelocity_eq_zero
    {U Ψ : ℝ^2 → ℝ} (hU : ContDiff ℝ 1 U)
    (hΨ : ContDiff ℝ 2 Ψ) (x : ℝ^3) :
    ∇· (axisymmetricVelocity U Ψ) x = 0 := by
  have hmeridional : DifferentiableAt ℝ (meridionalVelocity Ψ) x :=
    (contDiff_one_meridionalVelocity hΨ).contDiffAt.differentiableAt_one
  have hswirl : DifferentiableAt ℝ (swirlVelocity U) x :=
    (contDiff_one_swirlVelocity hU).contDiffAt.differentiableAt_one
  have hmeridionalComponent (i : Fin 3) :
      DifferentiableAt ℝ (fun y ↦ meridionalVelocity Ψ y i) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).differentiableAt.comp
      x hmeridional
  have hswirlComponent (i : Fin 3) :
      DifferentiableAt ℝ (fun y ↦ swirlVelocity U y i) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).differentiableAt.comp
      x hswirl
  calc
    ∇· (axisymmetricVelocity U Ψ) x =
        ∇· (meridionalVelocity Ψ) x + ∇· (swirlVelocity U) x := by
      simp only [divergence, axisymmetricVelocity]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change (∂[i]
          (fun y ↦ meridionalVelocity Ψ y i + swirlVelocity U y i)) x = _
      exact PDE.partialDeriv_add (hmeridionalComponent i) (hswirlComponent i)
    _ = 0 := by
      rw [spatialFieldDivergence_meridionalVelocity_eq_zero hΨ]
      rw [spatialFieldDivergence_swirlVelocity_eq_zero hU]
      simp

/-- A `C²` normalized streamfunction generates a globally divergence-free
meridional field. -/
theorem spatialFieldDivergenceFree_meridionalVelocity
    {Ψ : ℝ^2 → ℝ} (hΨ : ContDiff ℝ 2 Ψ) :
    SpatialFieldDivergenceFree (meridionalVelocity Ψ) :=
  fun x ↦ spatialFieldDivergence_meridionalVelocity_eq_zero hΨ x

/-- A `C¹` swirl profile generates a globally divergence-free azimuthal
field. -/
theorem spatialFieldDivergenceFree_swirlVelocity
    {U : ℝ^2 → ℝ} (hU : ContDiff ℝ 1 U) :
    SpatialFieldDivergenceFree (swirlVelocity U) :=
  fun x ↦ spatialFieldDivergence_swirlVelocity_eq_zero hU x

/-- A `C¹` swirl profile and `C²` normalized streamfunction generate a
globally divergence-free axisymmetric velocity. -/
theorem spatialFieldDivergenceFree_axisymmetricVelocity
    {U Ψ : ℝ^2 → ℝ} (hU : ContDiff ℝ 1 U)
    (hΨ : ContDiff ℝ 2 Ψ) :
    SpatialFieldDivergenceFree (axisymmetricVelocity U Ψ) :=
  fun x ↦ spatialFieldDivergence_axisymmetricVelocity_eq_zero hU hΨ x

/-- At an axis point, both transverse components of the reconstructed
velocity vanish. -/
theorem axisymmetricVelocity_transverse_eq_zero_of_mem_symmetryAxis
    (U Ψ : ℝ^2 → ℝ) {x : ℝ^3} (hx : x ∈ symmetryAxis) :
    axisymmetricVelocity U Ψ x 0 = 0 ∧
      axisymmetricVelocity U Ψ x 1 = 0 := by
  rw [mem_symmetryAxis_iff] at hx
  rcases hx with ⟨hx0, hx1⟩
  simp [axisymmetricVelocity, hx0, hx1]

/-- The axial value on the symmetry axis is the regular value `2 Ψ(0,z)`. -/
theorem axisymmetricVelocity_apply_two_of_mem_symmetryAxis
    (U Ψ : ℝ^2 → ℝ) {x : ℝ^3} (hx : x ∈ symmetryAxis) :
    axisymmetricVelocity U Ψ x 2 =
      2 * squaredCylindricalLift Ψ x := by
  rw [mem_symmetryAxis_iff] at hx
  rcases hx with ⟨hx0, hx1⟩
  simp [axisymmetricVelocity, cylindricalRadiusSq, hx0, hx1]

/-- The poloidal velocity written directly in terms of a Cartesian scalar.
For a rotationally invariant scalar `q(x,y,z) = ψ(r,z)`, its cylindrical
components are `-r ψ_z` and `2ψ + r ψ_r`. This formula has no division by the
radius and therefore defines the velocity on the axis as well. -/
def meridionalVelocityOfScalar (q : ℝ^3 → ℝ) (x : ℝ^3) : ℝ^3 :=
  cartesianVector (-x 0 * (∂[(2 : Fin 3)] q) x)
    (-x 1 * (∂[(2 : Fin 3)] q) x)
    (2 * q x + x 0 * (∂[(0 : Fin 3)] q) x +
      x 1 * (∂[(1 : Fin 3)] q) x)

/-- A Cartesian scalar with one more derivative gives a velocity with the
stated regularity, including at the symmetry axis. -/
theorem contDiff_meridionalVelocityOfScalar_of_succ {n : ℕ∞} {q : ℝ^3 → ℝ}
    (hq : ContDiff ℝ (n + 1) q) :
    ContDiff ℝ n (meridionalVelocityOfScalar q) := by
  have hqd : ContDiff ℝ n (fderiv ℝ q) := hq.fderiv_right (by simp)
  have hd (i : Fin 3) : ContDiff ℝ n (∂[i] q) :=
    hqd.clm_apply contDiff_const
  have hv (i : Fin 3) : ContDiff ℝ n (fun x : ℝ^3 ↦ x i) := by fun_prop
  exact contDiff_cartesianVector
    ((hv 0).neg.mul (hd 2)) ((hv 1).neg.mul (hd 2))
    (((contDiff_const.mul (hq.of_le (by simp))).add ((hv 0).mul (hd 0))).add
      ((hv 1).mul (hd 1)))

/-- The direct Cartesian formula agrees with the reconstruction
when the scalar is given in squared-radius coordinates. The factor `2` in the
radial chain rule is retained in the axial velocity. -/
theorem meridionalVelocityOfScalar_squaredCylindricalLift {Ψ : ℝ^2 → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) :
    meridionalVelocityOfScalar (squaredCylindricalLift Ψ) = meridionalVelocity Ψ := by
  funext x
  unfold meridionalVelocityOfScalar meridionalVelocity
  rw [partialDeriv_zero_squaredCylindricalLift hΨ,
    partialDeriv_one_squaredCylindricalLift hΨ,
    partialDeriv_two_squaredCylindricalLift hΨ]
  simp only [squaredCylindricalLift, cylindricalRadiusSq]
  congr 1
  cas

/-- Away from the axis the meridian coordinates `(r, z)` are differentiable. -/
private theorem differentiableAt_meridianCoordinates {x : ℝ^3} (hx : 0 < cylindricalRadius x) :
    DifferentiableAt ℝ meridianCoordinates x := by
  refine (differentiableAt_piLp (2 : ENNReal)).2 fun i ↦ ?_
  fin_cases i
  · exact (by unfold cylindricalRadiusSq; fun_prop : DifferentiableAt ℝ cylindricalRadiusSq x).sqrt
      (by rw [← cylindricalRadius_sq]; exact pow_ne_zero _ hx.ne')
  · change DifferentiableAt ℝ (fun y : ℝ^3 ↦ y 2) x
    fun_prop

/-- Away from the axis, the ordinary chain rule identifies the three
Cartesian derivatives of a meridian lift. Only the square root defining the
radius needs the positive-radius condition. -/
private theorem partialDeriv_meridianLift_off_axis {ψ : ℝ^2 → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (x : ℝ^3) (hx : 0 < cylindricalRadius x) :
    (∂[(0 : Fin 3)] (meridianLift ψ)) x =
        x 0 / cylindricalRadius x * (∂[(0 : Fin 2)] ψ) (meridianCoordinates x) ∧
      (∂[(1 : Fin 3)] (meridianLift ψ)) x =
        x 1 / cylindricalRadius x * (∂[(0 : Fin 2)] ψ) (meridianCoordinates x) ∧
      (∂[(2 : Fin 3)] (meridianLift ψ)) x =
        (∂[(1 : Fin 2)] ψ) (meridianCoordinates x) := by
  have hs : DifferentiableAt ℝ cylindricalRadiusSq x := by
    unfold cylindricalRadiusSq
    fun_prop
  have hsne : cylindricalRadiusSq x ≠ 0 := by
    rw [← cylindricalRadius_sq]
    exact pow_ne_zero _ (ne_of_gt hx)
  have hrderiv (i : Fin 3) :
      (∂[i] cylindricalRadius) x =
        (1 / (2 * cylindricalRadius x)) * (∂[i] cylindricalRadiusSq) x := by
    have hh := (hs.hasFDerivAt.sqrt hsne).fderiv
    change fderiv ℝ cylindricalRadius x =
      (1 / (2 * cylindricalRadius x)) • fderiv ℝ cylindricalRadiusSq x at hh
    unfold partialDeriv
    rw [hh]
    simp only [_root_.smul_apply, smul_eq_mul]
  have hc (i : Fin 3) :
      (∂[i] (meridianLift ψ)) x =
        (∂[(0 : Fin 2)] ψ) (meridianCoordinates x) *
          (∂[i] cylindricalRadius) x +
        (∂[(1 : Fin 2)] ψ) (meridianCoordinates x) *
          (∂[i] PDE.CoordinateSystems.axialCoordinate) x := by
    exact (partialDeriv_comp_euclidean i ψ meridianCoordinates x
      hψ.contDiffAt.differentiableAt_one (differentiableAt_meridianCoordinates hx)).trans (by
        simp only [Fin.sum_univ_two, meridianCoordinates_apply_zero,
          meridianCoordinates_apply_one])
  have haxial (i : Fin 3) :
      (∂[i] PDE.CoordinateSystems.axialCoordinate) x =
        if i = (2 : Fin 3) then 1 else 0 := by
    change (∂[i] (fun y : ℝ^3 ↦ y 2)) x = _
    exact PDE.partialDeriv_coord i 2 x
  have hn : cylindricalRadius x ≠ 0 := ne_of_gt hx
  refine ⟨?_, ?_, ?_⟩
  · rw [hc 0, hrderiv, partialDeriv_zero_cylindricalRadiusSq, haxial]
    cas
  · rw [hc 1, hrderiv, partialDeriv_one_cylindricalRadiusSq, haxial]
    cas
  · rw [hc 2, hrderiv, partialDeriv_two_cylindricalRadiusSq, haxial]
    norm_num

/-- At positive radius, the Cartesian reconstruction has exactly the physical
poloidal components `u_r = -r ψ_z` and `u_z = 2ψ + r ψ_r`. The radial chain rule
is derived here from the scalar lift. -/
theorem meridionalVelocityOfScalar_meridianLift_off_axis {ψ : ℝ^2 → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (x : ℝ^3) (hx : 0 < cylindricalRadius x) :
    meridionalVelocityOfScalar (meridianLift ψ) x =
      cartesianVector
        (-x 0 * (∂[(1 : Fin 2)] ψ) (meridianCoordinates x))
        (-x 1 * (∂[(1 : Fin 2)] ψ) (meridianCoordinates x))
        (2 * ψ (meridianCoordinates x) + cylindricalRadius x *
          (∂[(0 : Fin 2)] ψ) (meridianCoordinates x)) := by
  obtain ⟨h0, h1, h2⟩ := partialDeriv_meridianLift_off_axis hψ x hx
  unfold meridionalVelocityOfScalar
  rw [h0, h1, h2]
  simp only [meridianLift]
  congr 1
  have hs : x 0 ^ 2 + x 1 ^ 2 = cylindricalRadius x ^ 2 := by
    rw [cylindricalRadius_sq]
    rfl
  have hn : cylindricalRadius x ≠ 0 := ne_of_gt hx
  have he : x 0 * (x 0 / cylindricalRadius x *
        (∂[(0 : Fin 2)] ψ) (meridianCoordinates x)) +
      x 1 * (x 1 / cylindricalRadius x *
        (∂[(0 : Fin 2)] ψ) (meridianCoordinates x)) =
      cylindricalRadius x * (∂[(0 : Fin 2)] ψ) (meridianCoordinates x) := by
    cas using hs
  cas using he

/-- The squared speed of the direct Cartesian reconstruction is the
physical cylindrical energy density. At radius zero the transverse factors
vanish, so this identity does not differentiate the square root on the axis. -/
theorem norm_sq_meridionalVelocityOfScalar_meridianLift {ψ : ℝ^2 → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (x : ℝ^3) :
    ‖meridionalVelocityOfScalar (meridianLift ψ) x‖ ^ 2 =
      cylindricalRadius x ^ 2 *
          ((∂[(1 : Fin 2)] ψ) (meridianCoordinates x)) ^ 2 +
        (2 * ψ (meridianCoordinates x) + cylindricalRadius x *
          (∂[(0 : Fin 2)] ψ) (meridianCoordinates x)) ^ 2 := by
  have hs : x 0 ^ 2 + x 1 ^ 2 = cylindricalRadius x ^ 2 := by
    rw [cylindricalRadius_sq]
    rfl
  by_cases hz : cylindricalRadius x = 0
  · have h0 : x 0 = 0 := by cas using hs
    have h1 : x 1 = 0 := by cas using hs
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [meridionalVelocityOfScalar, Fin.sum_univ_three, h0, h1, hz, meridianLift]
  · have hp := lt_of_le_of_ne (cylindricalRadius_nonneg x) (Ne.symm hz)
    rw [meridionalVelocityOfScalar_meridianLift_off_axis hψ x hp,
      EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_three, cartesianVector_apply_zero,
      cartesianVector_apply_one, cartesianVector_apply_two]
    cas using hs

open Filter
open scoped Topology

/-- The direct scalar reconstruction is divergence free for every `C²` scalar.
The two mixed derivatives cancel, and differentiation of the transverse
coordinate factors cancels the derivative of `2q` in the axial component.
No rotational invariance is needed for this identity. -/
theorem spatialFieldDivergence_meridionalVelocityOfScalar_eq_zero
    {q : ℝ^3 → ℝ} (hq : ContDiff ℝ 2 q) (x : ℝ^3) :
    ∇· (meridionalVelocityOfScalar q) x = 0 := by
  have hd (i : Fin 3) : ContDiff ℝ 1 (∂[i] q) :=
    PDE.contDiff_partialDeriv_of_succ hq
  have hq' : DifferentiableAt ℝ q x := hq.contDiffAt.differentiableAt (by norm_num)
  have hd' (i : Fin 3) : DifferentiableAt ℝ (∂[i] q) x :=
    (hd i).contDiffAt.differentiableAt_one
  have hfirst : DifferentiableAt ℝ (fun y : ℝ^3 ↦ 2 * q y) x :=
    (differentiableAt_const (c := (2 : ℝ))).mul hq'
  have hxq (i : Fin 3) : DifferentiableAt ℝ
      (fun y : ℝ^3 ↦ y i * (∂[i] q) y) x :=
    (by fun_prop : DifferentiableAt ℝ (fun y : ℝ^3 ↦ y i) x).mul (hd' i)
  have hneg (i : Fin 3) :
      (∂[i] (fun y : ℝ^3 ↦ -y i)) x = -1 := by
    rw [show (fun y : ℝ^3 ↦ -y i) = -(fun y : ℝ^3 ↦ y i) by rfl,
      PDE.partialDeriv_neg, PDE.partialDeriv_coord]
    simp
  simp only [divergence, Fin.sum_univ_three,
    meridionalVelocityOfScalar, cartesianVector_apply_zero,
    cartesianVector_apply_one, cartesianVector_apply_two]
  rw [PDE.partialDeriv_mul (by fun_prop) (hd' 2),
    PDE.partialDeriv_mul (by fun_prop) (hd' 2),
    PDE.partialDeriv_add (f := fun y : ℝ^3 ↦ 2 * q y + y 0 * (∂[0] q) y)
      (g := fun y : ℝ^3 ↦ y 1 * (∂[1] q) y) (hfirst.add (hxq 0)) (hxq 1),
    PDE.partialDeriv_add (f := fun y : ℝ^3 ↦ 2 * q y)
      (g := fun y : ℝ^3 ↦ y 0 * (∂[0] q) y) hfirst (hxq 0),
    PDE.partialDeriv_mul (differentiableAt_const (c := (2 : ℝ))) hq',
    PDE.partialDeriv_mul (by fun_prop) (hd' 0),
    PDE.partialDeriv_mul (by fun_prop) (hd' 1)]
  simp only [hneg, PDE.partialDeriv_const, PDE.partialDeriv_coord]
  rw [PDE.partialDeriv_partialDeriv_comm (2 : Fin 3) 0 hq,
    PDE.partialDeriv_partialDeriv_comm (2 : Fin 3) 1 hq]
  cas

/-- The vector potential `(-yq, xq, 0)` has curl equal to the direct scalar
reconstruction. This includes its axial value `2q` on the axis and fixes the
right-handed orientation without a cylindrical division. -/
theorem spatialCurl_azimuthalScalar_eq_meridionalVelocityOfScalar
    {q : ℝ^3 → ℝ} (hq : ContDiff ℝ 1 q) (x : ℝ^3) :
    spatialCurl (fun y : ℝ^3 ↦ cartesianVector (-y 1 * q y) (y 0 * q y) 0) x =
      meridionalVelocityOfScalar q x := by
  have hq' : DifferentiableAt ℝ q x := hq.contDiffAt.differentiableAt_one
  have hneg (i j : Fin 3) :
      (∂[i] (fun y : ℝ^3 ↦ -y j)) x = -(if i = j then 1 else 0) := by
    rw [show (fun y : ℝ^3 ↦ -y j) = -(fun y : ℝ^3 ↦ y j) by rfl,
      PDE.partialDeriv_neg, PDE.partialDeriv_coord]
  ext i
  fin_cases i
  · change (∂[(1 : Fin 3)] (fun _ : ℝ^3 ↦ (0 : ℝ))) x -
      (∂[(2 : Fin 3)] (fun y : ℝ^3 ↦ y 0 * q y)) x =
        -x 0 * (∂[(2 : Fin 3)] q) x
    rw [PDE.partialDeriv_const, PDE.partialDeriv_mul (by fun_prop) hq', PDE.partialDeriv_coord]
    cas
  · change (∂[(2 : Fin 3)] (fun y : ℝ^3 ↦ -y 1 * q y)) x -
      (∂[(0 : Fin 3)] (fun _ : ℝ^3 ↦ (0 : ℝ))) x =
        -x 1 * (∂[(2 : Fin 3)] q) x
    rw [PDE.partialDeriv_const, PDE.partialDeriv_mul (by fun_prop) hq', hneg]
    cas
  · change (∂[(0 : Fin 3)] (fun y : ℝ^3 ↦ y 0 * q y)) x -
      (∂[(1 : Fin 3)] (fun y : ℝ^3 ↦ -y 1 * q y)) x =
        2 * q x + x 0 * (∂[(0 : Fin 3)] q) x +
          x 1 * (∂[(1 : Fin 3)] q) x
    rw [PDE.partialDeriv_mul (by fun_prop) hq', PDE.partialDeriv_mul (by fun_prop) hq',
      PDE.partialDeriv_coord, hneg]
    cas

/-- At positive radius the curl of the direct reconstruction is azimuthal.
Its coefficient is `ψrr + 3ψr/r + ψzz`, the five-dimensional Laplacian of
the radial lift. The standard Cartesian curl fixes its sign. Only `C²`
regularity of the meridian profile is used away from the axis. -/
theorem spatialCurl_meridionalVelocityOfScalar_meridianLift_off_axis
    {ψ : ℝ^2 → ℝ} (hψ : ContDiff ℝ 2 ψ) (x : ℝ^3)
    (hx : 0 < cylindricalRadius x) :
    spatialCurl (meridionalVelocityOfScalar (meridianLift ψ)) x =
      cartesianVector
        (x 1 * ((∂[(0 : Fin 2)] (∂[0] ψ)) (meridianCoordinates x) +
          3 * (cylindricalRadius x)⁻¹ * (∂[0] ψ) (meridianCoordinates x) +
          (∂[1] (∂[1] ψ)) (meridianCoordinates x)))
        (-x 0 * ((∂[(0 : Fin 2)] (∂[0] ψ)) (meridianCoordinates x) +
          3 * (cylindricalRadius x)⁻¹ * (∂[0] ψ) (meridianCoordinates x) +
          (∂[1] (∂[1] ψ)) (meridianCoordinates x))) 0 := by
  have hψone : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hψr : ContDiff ℝ 1 (∂[(0 : Fin 2)] ψ) :=
    PDE.contDiff_partialDeriv_of_succ hψ
  have hψz : ContDiff ℝ 1 (∂[(1 : Fin 2)] ψ) :=
    PDE.contDiff_partialDeriv_of_succ hψ
  let a : ℝ^2 → ℝ := fun p ↦ 2 * ψ p + p 0 * (∂[(0 : Fin 2)] ψ) p
  have ha : ContDiff ℝ 1 a :=
    (contDiff_const.mul hψone).add
      ((by fun_prop : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 0)).mul hψr)
  have hdz : DifferentiableAt ℝ (meridianLift (∂[(1 : Fin 2)] ψ)) x :=
    hψz.contDiffAt.differentiableAt_one.comp x (differentiableAt_meridianCoordinates hx)
  have hevent : ∀ᶠ y in nhds x, 0 < cylindricalRadius y := (isOpen_lt continuous_const
    (by unfold cylindricalRadius cylindricalRadiusSq; fun_prop)).mem_nhds hx
  have hc (i j : Fin 3) :
      (∂[i] (fun y ↦ meridionalVelocityOfScalar (meridianLift ψ) y j)) x =
        (∂[i] (fun y ↦ (cartesianVector
          (-y 0 * meridianLift (∂[(1 : Fin 2)] ψ) y)
          (-y 1 * meridianLift (∂[(1 : Fin 2)] ψ) y)
          (meridianLift a y)) j)) x := by
    apply PDE.partialDeriv_congr_nhds i
    filter_upwards [hevent] with y hy
    rw [meridionalVelocityOfScalar_meridianLift_off_axis hψone y hy]
    simp only [meridianLift, a, meridianCoordinates_apply_zero]
  obtain ⟨ha0, ha1, _⟩ := partialDeriv_meridianLift_off_axis ha x hx
  obtain ⟨hz0, hz1, hz2⟩ := partialDeriv_meridianLift_off_axis hψz x hx
  have har : (∂[(0 : Fin 2)] a) (meridianCoordinates x) =
      3 * (∂[(0 : Fin 2)] ψ) (meridianCoordinates x) +
        cylindricalRadius x * (∂[(0 : Fin 2)]
          (∂[(0 : Fin 2)] ψ)) (meridianCoordinates x) := by
    dsimp only [a]
    rw [PDE.partialDeriv_add (f := fun p : ℝ^2 ↦ 2 * ψ p)
      (g := fun p : ℝ^2 ↦ p 0 * (∂[(0 : Fin 2)] ψ) p)
      ((differentiableAt_const (c := (2 : ℝ))).mul
        hψone.contDiffAt.differentiableAt_one)
      ((by fun_prop : DifferentiableAt ℝ (fun p : ℝ^2 ↦ p 0)
        (meridianCoordinates x)).mul hψr.contDiffAt.differentiableAt_one),
      PDE.partialDeriv_mul (differentiableAt_const (c := (2 : ℝ)))
        hψone.contDiffAt.differentiableAt_one,
      PDE.partialDeriv_mul (by fun_prop) hψr.contDiffAt.differentiableAt_one]
    simp only [PDE.partialDeriv_const, PDE.partialDeriv_coord, meridianCoordinates_apply_zero,
      zero_mul, zero_add]
    cas
  have hneg (i j : Fin 3) :
      (∂[i] (fun y : ℝ^3 ↦ -y j)) x = -(if i = j then 1 else 0) := by
    rw [show (fun y : ℝ^3 ↦ -y j) = -(fun y : ℝ^3 ↦ y j) by rfl,
      PDE.partialDeriv_neg, PDE.partialDeriv_coord]
  have hn : cylindricalRadius x ≠ 0 := ne_of_gt hx
  ext i
  fin_cases i
  · change (∂[(1 : Fin 3)]
        (fun y ↦ meridionalVelocityOfScalar (meridianLift ψ) y 2)) x -
      (∂[(2 : Fin 3)]
        (fun y ↦ meridionalVelocityOfScalar (meridianLift ψ) y 1)) x =
      x 1 * ((∂[(0 : Fin 2)] (∂[0] ψ)) (meridianCoordinates x) +
        3 * (cylindricalRadius x)⁻¹ * (∂[0] ψ) (meridianCoordinates x) +
        (∂[1] (∂[1] ψ)) (meridianCoordinates x))
    rw [hc 1 2, hc 2 1]
    simp only [cartesianVector_apply_one, cartesianVector_apply_two]
    rw [ha1, har, PDE.partialDeriv_mul (by fun_prop) hdz, hneg, hz2]
    simp only [meridianLift]
    cas
  · change (∂[(2 : Fin 3)]
        (fun y ↦ meridionalVelocityOfScalar (meridianLift ψ) y 0)) x -
      (∂[(0 : Fin 3)]
        (fun y ↦ meridionalVelocityOfScalar (meridianLift ψ) y 2)) x =
      -x 0 * ((∂[(0 : Fin 2)] (∂[0] ψ)) (meridianCoordinates x) +
        3 * (cylindricalRadius x)⁻¹ * (∂[0] ψ) (meridianCoordinates x) +
        (∂[1] (∂[1] ψ)) (meridianCoordinates x))
    rw [hc 2 0, hc 0 2]
    simp only [cartesianVector_apply_zero, cartesianVector_apply_two]
    rw [ha0, har, PDE.partialDeriv_mul (by fun_prop) hdz, hneg, hz2]
    simp only [meridianLift]
    cas
  · change (∂[(0 : Fin 3)]
        (fun y ↦ meridionalVelocityOfScalar (meridianLift ψ) y 1)) x -
      (∂[(1 : Fin 3)]
        (fun y ↦ meridionalVelocityOfScalar (meridianLift ψ) y 0)) x = 0
    rw [hc 0 1, hc 1 0]
    simp only [cartesianVector_apply_zero, cartesianVector_apply_one]
    rw [PDE.partialDeriv_mul (by fun_prop) hdz, PDE.partialDeriv_mul (by fun_prop) hdz,
      hneg, hneg, hz0, hz1]
    cas

end

end AxisymmetricFlow
