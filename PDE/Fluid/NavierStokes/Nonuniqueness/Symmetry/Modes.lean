/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry
public import PDE.FDeriv.Axisymmetric.SphericalSymmetry

/-!
# Sectors of spherical meridional and azimuthal fields

A Cartesian meridional field `meridionalField F G S T` lies in the even sector when its polar
coefficient `S` is even and `T` is odd in the polar cosine, and in the odd sector for the opposite
parities. An azimuthal field `azimuthalField H A` lies in the even sector for even `A` and in the
odd sector for odd `A`. For Legendre-type modes of degree `l` the parities are `(-1)^l` for the
scalar coefficient and `(-1)^(l+1)` for its derivative, which places each mode in the sector of
its degree. The constant axis direction `e_z` is odd.

Fields that are equivariant under rotations about the axis in the sense of
`PDE.CoordinateSystems.IsEquivariantUnderAxisRotation`, such as the ball modes, lie in the even
sector when `u(σ x) = σ u(x)` and in the odd sector when `u(σ x) = -σ u(x)`
(`IsEvenAxisymmetric.of_isEquivariantUnderAxisRotation`,
`IsOddAxisymmetric.of_isEquivariantUnderAxisRotation`).
-/

@[expose] public noncomputable section

open PDE.CoordinateSystems (axialRotation equatorialReflection)
open PDE.FDeriv.Spherical

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-- A meridional field with even `S` and odd `T` is even axisymmetric. -/
theorem isEvenAxisymmetric_meridionalField {F G S T : ℝ → ℝ} (hS : ∀ c, S (-c) = S c)
    (hT : ∀ c, T (-c) = -T c) : IsEvenAxisymmetric (meridionalField F G S T) :=
  IsEvenAxisymmetric.of_forall (meridionalField_axialRotation F G S T)
    (meridionalField_equatorialReflection hS hT)

/-- A meridional field with odd `S` and even `T` is odd axisymmetric. -/
theorem isOddAxisymmetric_meridionalField {F G S T : ℝ → ℝ} (hS : ∀ c, S (-c) = -S c)
    (hT : ∀ c, T (-c) = T c) : IsOddAxisymmetric (meridionalField F G S T) :=
  IsOddAxisymmetric.of_forall (meridionalField_axialRotation F G S T)
    (meridionalField_equatorialReflection_of_odd hS hT)

/-- An azimuthal field with even polar coefficient is even axisymmetric. -/
theorem isEvenAxisymmetric_azimuthalField {H A : ℝ → ℝ} (hA : ∀ c, A (-c) = A c) :
    IsEvenAxisymmetric (azimuthalField H A) :=
  IsEvenAxisymmetric.of_forall (azimuthalField_axialRotation H A)
    (azimuthalField_equatorialReflection hA)

/-- An azimuthal field with odd polar coefficient is odd axisymmetric. -/
theorem isOddAxisymmetric_azimuthalField {H A : ℝ → ℝ} (hA : ∀ c, A (-c) = -A c) :
    IsOddAxisymmetric (azimuthalField H A) :=
  IsOddAxisymmetric.of_forall (azimuthalField_axialRotation H A)
    (azimuthalField_equatorialReflection_of_odd hA)

/-- The constant axis direction `e_z` is odd axisymmetric. -/
theorem isOddAxisymmetric_axisDirection :
    IsOddAxisymmetric (fun _ : ℝ^3 ↦ EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) :=
  IsOddAxisymmetric.of_forall (fun θ _ ↦ (PDE.CoordinateSystems.axialRotation_single_two θ).symm)
    (fun _ ↦ by rw [PDE.CoordinateSystems.equatorialReflection_single_two, neg_neg])

/-- A rotation-equivariant field that is equivariant under the equatorial reflection is even
axisymmetric. -/
theorem IsEvenAxisymmetric.of_isEquivariantUnderAxisRotation {u : ℝ^3 → ℝ^3}
    (hrot : PDE.CoordinateSystems.IsEquivariantUnderAxisRotation u)
    (hrefl : ∀ x, u (equatorialReflection x) = equatorialReflection (u x)) :
    IsEvenAxisymmetric u :=
  IsEvenAxisymmetric.of_forall (fun θ x ↦ by
    simpa only [PDE.CoordinateSystems.axialRotation_apply] using hrot θ x) hrefl

/-- A rotation-equivariant field that changes sign under the equatorial reflection,
`u(σ x) = -σ u(x)`, is odd axisymmetric. -/
theorem IsOddAxisymmetric.of_isEquivariantUnderAxisRotation {u : ℝ^3 → ℝ^3}
    (hrot : PDE.CoordinateSystems.IsEquivariantUnderAxisRotation u)
    (hrefl : ∀ x, u (equatorialReflection x) = -equatorialReflection (u x)) :
    IsOddAxisymmetric u :=
  IsOddAxisymmetric.of_forall (fun θ x ↦ by
    simpa only [PDE.CoordinateSystems.axialRotation_apply] using hrot θ x) hrefl

end NavierStokes.Nonuniqueness
