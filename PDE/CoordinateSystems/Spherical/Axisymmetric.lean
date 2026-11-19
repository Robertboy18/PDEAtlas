/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Axisymmetric.Isometry
public import PDE.CoordinateSystems.Spherical.Frame

/-!
# Spherical coordinates of axisymmetric fields

Rotation through angle `φ` about the symmetry axis preserves the Euclidean inner product and
carries the spherical frame and the spherical points at azimuth zero to those at azimuth `φ`.
An equivariant vector field is therefore the rotated copy of its values on the half plane of
azimuth zero, and its spherical components `⟪e_k (θ, φ), u (point r θ φ)⟫` do not depend on `φ`.

The reflection `σ (x, y, z) = (x, y, -z)` in the equatorial plane takes the polar angle `θ` to
`π - θ`: it carries the radial vector and the spherical point at `θ` to those at `π - θ`, the
polar vector to minus the polar vector, and it fixes the azimuthal vector. A field with
`u (σ x) = ε σ (u x)` therefore satisfies `u (point r (π - θ) φ) = ε σ (u (point r θ φ))`.
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace

namespace PDE.CoordinateSystems

/-- Rotation about the symmetry axis preserves the Euclidean inner product. -/
theorem inner_axisRotation_axisRotation (φ : ℝ) (x y : ℝ^3) :
    ⟪axisRotation φ x, axisRotation φ y⟫ = ⟪x, y⟫ :=
  (axialRotation φ).inner_map_map x y

/-- Rotation about the symmetry axis commutes with scalar multiplication. -/
theorem axisRotation_smul (φ a : ℝ) (x : ℝ^3) :
    axisRotation φ (a • x) = a • axisRotation φ x :=
  map_smul (axialRotation φ) a x

end PDE.CoordinateSystems

namespace PDE.CoordinateSystems.Spherical

open PDE.Common

/-- Rotating the spherical frame at azimuth zero through `φ` gives the frame at azimuth `φ`. -/
theorem axisRotation_frame (φ θ : ℝ) (k : Fin 3) :
    axisRotation φ (frame θ 0 k) = frame θ φ k := by
  ext i
  fin_cases k <;> fin_cases i <;>
    simp [frame, radialFrame, polarFrame, azimuthalFrame, axisRotation] <;> ring

/-- Rotating the spherical point at azimuth zero through `φ` gives the point at azimuth `φ`. -/
theorem axisRotation_point (r θ φ : ℝ) : axisRotation φ (point r θ 0) = point r θ φ := by
  rw [point, point, axisRotation_smul]
  exact congrArg (r • ·) (axisRotation_frame φ θ 0)

/-- An equivariant vector field is the rotated copy of its values on the half plane of azimuth
zero. -/
theorem eq_axisRotation_of_isEquivariantUnderAxisRotation {u : ℝ^3 → ℝ^3}
    (hu : IsEquivariantUnderAxisRotation u) (r θ φ : ℝ) :
    u (point r θ φ) = axisRotation φ (u (point r θ 0)) := by
  rw [← axisRotation_point, hu]

/-- The spherical components of an equivariant vector field do not depend on the azimuth. -/
theorem inner_frame_of_isEquivariantUnderAxisRotation {u : ℝ^3 → ℝ^3}
    (hu : IsEquivariantUnderAxisRotation u) (r θ φ : ℝ) (k : Fin 3) :
    ⟪frame θ φ k, u (point r θ φ)⟫ = ⟪frame θ 0 k, u (point r θ 0)⟫ := by
  rw [eq_axisRotation_of_isEquivariantUnderAxisRotation hu, ← axisRotation_frame,
    inner_axisRotation_axisRotation]

/-- The equatorial reflection carries the radial vector at polar angle `θ` to the radial vector
at `π - θ`. -/
theorem radialFrame_pi_sub (θ φ : ℝ) :
    radialFrame (Real.pi - θ) φ = coordinateReflection 2 (radialFrame θ φ) := by
  ext i
  fin_cases i <;>
    simp [radialFrame, coordinateReflection_apply_of_ne, Real.sin_pi_sub, Real.cos_pi_sub]

/-- The equatorial reflection carries the polar vector at polar angle `θ` to minus the polar
vector at `π - θ`. -/
theorem polarFrame_pi_sub (θ φ : ℝ) :
    polarFrame (Real.pi - θ) φ = -coordinateReflection 2 (polarFrame θ φ) := by
  ext i
  fin_cases i <;>
    simp [polarFrame, coordinateReflection_apply_of_ne, Real.sin_pi_sub, Real.cos_pi_sub]

/-- The equatorial reflection fixes the azimuthal vector. -/
theorem coordinateReflection_azimuthalFrame (φ : ℝ) :
    coordinateReflection 2 (azimuthalFrame φ) = azimuthalFrame φ := by
  ext i
  fin_cases i <;> simp [azimuthalFrame, coordinateReflection_apply_of_ne]

/-- The equatorial reflection carries the spherical point of polar angle `θ` to that of polar
angle `π - θ`. -/
theorem point_pi_sub (r θ φ : ℝ) :
    point r (Real.pi - θ) φ = coordinateReflection 2 (point r θ φ) := by
  rw [point, point, radialFrame_pi_sub]
  exact ((coordinateReflectionLinearIsometryEquiv 2).map_smul r (radialFrame θ φ)).symm

/-- If `u (σ x) = ε σ (u x)` for the equatorial reflection `σ`, then
`u (point r (π - θ) φ) = ε σ (u (point r θ φ))` on every meridian. -/
theorem meridian_pi_sub_of_reflection {u : ℝ^3 → ℝ^3} {ε : ℝ}
    (hu : ∀ x, u (coordinateReflection 2 x) = ε • coordinateReflection 2 (u x)) (r θ φ : ℝ) :
    u (point r (Real.pi - θ) φ) = ε • coordinateReflection 2 (u (point r θ φ)) := by
  rw [point_pi_sub, hu]

end PDE.CoordinateSystems.Spherical
