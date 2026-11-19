/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical

/-!
# The spherical orthonormal frame

Radial, polar, and azimuthal vectors form an orthonormal basis for every
pair of angles, including the polar axis. The frame coordinate map is a
linear isometry, so quadratic-form bounds in spherical components use
the same Euclidean norm as their Cartesian counterparts.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open scoped RealInnerProductSpace BigOperators

/-- The ordered radial, polar, and azimuthal frame. -/
def frame (θ φ : ℝ) : Fin 3 → ℝ^3 := ![radialFrame θ φ, polarFrame θ φ, azimuthalFrame φ]

/-- The spherical frame is orthonormal at every pair of angles. -/
theorem orthonormal_frame (θ φ : ℝ) : Orthonormal ℝ (frame θ φ) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  have hφ := Real.sin_sq_add_cos_sq φ
  have hθ := Real.sin_sq_add_cos_sq θ
  have h₁ := congrArg (fun t : ℝ ↦ Real.sin θ ^ 2 * t) hφ
  have h₂ := congrArg (fun t : ℝ ↦ Real.cos θ ^ 2 * t) hφ
  have h₃ := congrArg (fun t : ℝ ↦ Real.sin θ * Real.cos θ * t) hφ
  fin_cases i <;> fin_cases j <;>
    simp only [frame, radialFrame, polarFrame, azimuthalFrame, PiLp.inner_apply,
      Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  all_goals dsimp
  all_goals nlinarith only [hφ, hθ, h₁, h₂, h₃]

/-- The spherical frame spans the whole three-dimensional Euclidean space. -/
theorem span_frame_eq_top (θ φ : ℝ) : Submodule.span ℝ (Set.range (frame θ φ)) = ⊤ := by
  apply (orthonormal_frame θ φ).linearIndependent.span_eq_top_of_card_eq_finrank'
  simp only [Fintype.card_fin, finrank_euclideanSpace_fin]

/-- The spherical frame bundled as an orthonormal basis. -/
def frameBasis (θ φ : ℝ) : OrthonormalBasis (Fin 3) ℝ (ℝ^3) :=
  OrthonormalBasis.mk (orthonormal_frame θ φ) (span_frame_eq_top θ φ).ge

/-- The bundled frame basis has precisely the source's three frame vectors. -/
@[simp]
theorem frameBasis_apply (θ φ : ℝ) (i : Fin 3) : frameBasis θ φ i = frame θ φ i := by
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

/-- Frame coordinates are Euclidean inner products with the frame vectors. -/
theorem frameBasis_repr_apply (θ φ : ℝ) (v : ℝ^3) (i : Fin 3) :
    (frameBasis θ φ).repr v i = ⟪frame θ φ i, v⟫ := by
  rw [OrthonormalBasis.repr_apply_apply, frameBasis_apply]

/-- The frame coordinate map preserves the Euclidean norm. -/
theorem norm_frameBasis_repr (θ φ : ℝ) (v : ℝ^3) :
    ‖(frameBasis θ φ).repr v‖ = ‖v‖ := (frameBasis θ φ).repr.norm_map v

end PDE.CoordinateSystems.Spherical
