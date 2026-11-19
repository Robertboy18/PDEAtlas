/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.Axisymmetric
public import PDE.CoordinateSystems.Spherical.AxisymmetricField

/-!
# Symmetries of spherical angles, frames and frame matrices

Off the axis, a rotation about the axis shifts the azimuthal angle by the rotation angle modulo
`2π`, so it carries the spherical frame at a point to the frame at the rotated point
(`frame_azimuthalAngle_axialRotation`). The equatorial reflection keeps the azimuthal angle and
maps the frame at `θ` to the reflected frame at `π - θ` with the polar vector reversed
(`frame_pi_sub_eq`). A Cartesian operator given by a component matrix in the frame transforms
accordingly (`matrixInFrame_conj`). The polar angle itself is treated in
`AxisymmetricIntegration`.
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace Matrix

namespace PDE.CoordinateSystems.Spherical

open PDE.CoordinateSystems

set_option linter.missingDocs true

/-- Frame matrices transform under an isometry that carries one frame to another up to signs:
if `f'ₖ = sₖ L fₖ` and `A'ᵢⱼ = sᵢ sⱼ Aᵢⱼ`, then the Cartesian operator of `A'` in the frame `f'`
is `L` conjugating the operator of `A` in the frame `f`. Both frames are orthonormal, so
`sₖ² = 1`. -/
theorem matrixInFrame_conj {θ φ θ' φ' : ℝ} (L : ℝ^3 ≃ₗᵢ[ℝ] ℝ^3) (s : Fin 3 → ℝ)
    (hframe : ∀ k, frame θ' φ' k = s k • L (frame θ φ k))
    {A A' : Matrix (Fin 3) (Fin 3) ℝ} (hA : ∀ i j, A' i j = s i * s j * A i j) (v : ℝ^3) :
    matrixInFrame θ' φ' A' v = L (matrixInFrame θ φ A (L.symm v)) := by
  have hs (k : Fin 3) : s k * s k = 1 := by
    have h := (orthonormal_frame θ' φ').1 k
    rw [hframe k, norm_smul, LinearIsometryEquiv.norm_map, (orthonormal_frame θ φ).1 k, mul_one,
      Real.norm_eq_abs] at h
    rw [← abs_mul_abs_self, h, one_mul]
  refine ext_inner_right ℝ fun w ↦ ?_
  have hflip (a b : ℝ^3) : ⟪L a, b⟫ = ⟪a, L.symm b⟫ := L.inner_map_eq_flip a b
  rw [inner_matrixInFrame, hflip, inner_matrixInFrame]
  simp only [dotProduct, Matrix.mulVec, frameBasis_repr_apply, hframe, real_inner_smul_left,
    hflip, hA]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hi := hs i
  have hj := hs j
  linear_combination (A i j * ⟪frame θ φ j, L.symm v⟫ * ⟪frame θ φ i, L.symm w⟫) *
    (s j * s j * hi + hj)

/-- The azimuthal angle is unchanged by the equatorial reflection. -/
theorem azimuthalAngle_equatorialReflection (x : ℝ^3) :
    azimuthalAngle (equatorialReflection x) = azimuthalAngle x := by
  simp only [azimuthalAngle, equatorialReflection_apply_zero, equatorialReflection_apply_one]

/-- The frame at the supplementary polar angle is the reflected frame up to the sign of the
polar direction. -/
theorem frame_pi_sub_eq (θ φ : ℝ) (k : Fin 3) :
    frame (Real.pi - θ) φ k = (![1, -1, 1] : Fin 3 → ℝ) k • equatorialReflection (frame θ φ k) := by
  fin_cases k
  · simp [frame, radialFrame_pi_sub, coe_equatorialReflection]
  · simp [frame, polarFrame_pi_sub, coe_equatorialReflection]
  · simp [frame, coordinateReflection_azimuthalFrame, coe_equatorialReflection]

/-- Rotating the frame about the axis shifts the azimuthal angle. -/
theorem frame_add_azimuth (θ φ α : ℝ) (k : Fin 3) :
    frame θ (φ + α) k = axialRotation α (frame θ φ k) := by
  rw [axialRotation_apply, ← axisRotation_frame φ θ k, ← axisRotation_add, add_comm,
    axisRotation_frame]

/-- Off the axis, a rotation about the axis shifts the azimuthal frame by the rotation angle. -/
theorem frame_azimuthalAngle_axialRotation (θ α : ℝ) {x : ℝ^3} (hx : x ∉ symmetryAxis)
    (k : Fin 3) :
    frame θ (azimuthalAngle (axialRotation α x)) k =
      axialRotation α (frame θ (azimuthalAngle x) k) := by
  have hρ : cylindricalRadius (axialRotation α x) = cylindricalRadius x := by
    rw [axialRotation_apply, cylindricalRadius_axisRotation]
  have hRx : axialRotation α x ∉ symmetryAxis := fun h ↦ hx (by
    change cylindricalRadius x = 0
    rw [← hρ]
    exact h)
  have hne := (cylindricalRadius_pos hx).ne'
  rw [← frame_add_azimuth]
  refine congrFun (frame_congr_azimuth ?_ ?_ θ) k
  · rw [cos_azimuthalAngle hRx, Real.cos_add, cos_azimuthalAngle hx, sin_azimuthalAngle, hρ,
      axialRotation_apply_zero]
    field_simp
  · rw [sin_azimuthalAngle, Real.sin_add, cos_azimuthalAngle hx, sin_azimuthalAngle, hρ,
      axialRotation_apply_one]
    field_simp
    ring

end PDE.CoordinateSystems.Spherical
