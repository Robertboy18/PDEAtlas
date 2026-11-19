/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.Frame
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Differentiation along spherical coordinate lines

The spherical frame turns under a change of the angles: `∂_θ e_r = e_θ`, `∂_θ e_θ = -e_r`,
`∂_φ e_r = sin θ e_φ`, `∂_φ e_θ = cos θ e_φ` and `∂_φ e_φ = -(sin θ e_r + cos θ e_θ)`. A vector
`frameVector θ φ c = ∑ₖ cₖ eₖ` with components `c` therefore has the angular derivatives
`frameVector θ φ (c' + polarConnection c)` and `frameVector θ φ (azimuthalConnection θ c)`.

The coordinate lines through `point r θ φ` have velocities `e_r`, `r e_θ` and `r sin θ e_φ`.
At a point where a map is differentiable, its derivative in a frame direction is therefore
the derivative along the corresponding coordinate line, divided by the scale factor `1`, `r`
or `r sin θ`.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open scoped RealInnerProductSpace

/-! ### Derivatives of the frame -/

private theorem hasDerivAt_toLp_three {a b c : ℝ → ℝ} {a' b' c' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (hc : HasDerivAt c c' t) :
    HasDerivAt (fun s ↦ (WithLp.toLp 2 ![a s, b s, c s] : ℝ^3))
      (WithLp.toLp 2 ![a', b', c']) t := by
  have h : HasDerivAt (fun s ↦ ![a s, b s, c s]) ![a', b', c'] t := by
    refine hasDerivAt_pi.mpr fun i ↦ ?_
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  exact (PiLp.hasFDerivAt_toLp 2 ![a t, b t, c t]).comp_hasDerivAt t h

/-- The radial vector turns into the polar vector as the polar angle increases. -/
theorem hasDerivAt_radialFrame_polar (θ φ : ℝ) :
    HasDerivAt (fun t ↦ radialFrame t φ) (polarFrame θ φ) θ := by
  unfold radialFrame polarFrame
  exact hasDerivAt_toLp_three ((Real.hasDerivAt_sin θ).mul_const (Real.cos φ))
    ((Real.hasDerivAt_sin θ).mul_const (Real.sin φ)) (Real.hasDerivAt_cos θ)

/-- The polar vector turns into minus the radial vector as the polar angle increases. -/
theorem hasDerivAt_polarFrame_polar (θ φ : ℝ) :
    HasDerivAt (fun t ↦ polarFrame t φ) (-radialFrame θ φ) θ := by
  unfold radialFrame polarFrame
  convert hasDerivAt_toLp_three ((Real.hasDerivAt_cos θ).mul_const (Real.cos φ))
    ((Real.hasDerivAt_cos θ).mul_const (Real.sin φ)) (Real.hasDerivAt_sin θ).neg using 1
  ext i
  fin_cases i <;> simp

/-- The radial vector turns into `sin θ` times the azimuthal vector as the azimuth increases. -/
theorem hasDerivAt_radialFrame_azimuthal (θ φ : ℝ) :
    HasDerivAt (fun t ↦ radialFrame θ t) (Real.sin θ • azimuthalFrame φ) φ := by
  unfold radialFrame azimuthalFrame
  convert hasDerivAt_toLp_three ((Real.hasDerivAt_cos φ).const_mul (Real.sin θ))
    ((Real.hasDerivAt_sin φ).const_mul (Real.sin θ)) (hasDerivAt_const φ (Real.cos θ)) using 1
  ext i
  fin_cases i <;> simp

/-- The polar vector turns into `cos θ` times the azimuthal vector as the azimuth increases. -/
theorem hasDerivAt_polarFrame_azimuthal (θ φ : ℝ) :
    HasDerivAt (fun t ↦ polarFrame θ t) (Real.cos θ • azimuthalFrame φ) φ := by
  unfold polarFrame azimuthalFrame
  convert hasDerivAt_toLp_three ((Real.hasDerivAt_cos φ).const_mul (Real.cos θ))
    ((Real.hasDerivAt_sin φ).const_mul (Real.cos θ)) (hasDerivAt_const φ (-Real.sin θ)) using 1
  ext i
  fin_cases i <;> simp

/-- The azimuthal vector turns into minus the horizontal radial direction
`sin θ e_r + cos θ e_θ` as the azimuth increases. -/
theorem hasDerivAt_azimuthalFrame (θ φ : ℝ) :
    HasDerivAt azimuthalFrame (-(Real.sin θ • radialFrame θ φ + Real.cos θ • polarFrame θ φ))
      φ := by
  have hθ := Real.sin_sq_add_cos_sq θ
  unfold radialFrame polarFrame azimuthalFrame
  convert hasDerivAt_toLp_three (Real.hasDerivAt_sin φ).neg (Real.hasDerivAt_cos φ)
    (hasDerivAt_const φ (0 : ℝ)) using 1
  ext i
  fin_cases i <;> simp
  · linear_combination (-Real.cos φ) * hθ
  · linear_combination (-Real.sin φ) * hθ
  · ring

/-! ### Vectors with components in the frame -/

/-- The vector `∑ₖ cₖ eₖ` with components `c` in the spherical frame at the angles `(θ, φ)`. -/
def frameVector (θ φ : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ^3 :=
  Fintype.linearCombination ℝ (frame θ φ)

/-- A frame vector is the combination of the radial, polar and azimuthal vectors. -/
theorem frameVector_apply (θ φ : ℝ) (c : Fin 3 → ℝ) :
    frameVector θ φ c = c 0 • radialFrame θ φ + c 1 • polarFrame θ φ + c 2 • azimuthalFrame φ := by
  simp [frameVector, Fintype.linearCombination_apply, Fin.sum_univ_three, frame]

/-- The frame components of `frameVector θ φ c` are the entries of `c`. -/
@[simp]
theorem inner_frame_frameVector (θ φ : ℝ) (c : Fin 3 → ℝ) (i : Fin 3) :
    ⟪frame θ φ i, frameVector θ φ c⟫ = c i := by
  rw [frameVector, Fintype.linearCombination_apply]
  exact (orthonormal_frame θ φ).inner_right_fintype c i

/-- Every vector is the frame vector of its frame components. -/
theorem frameVector_inner_frame (θ φ : ℝ) (v : ℝ^3) :
    frameVector θ φ (fun k ↦ ⟪frame θ φ k, v⟫) = v := by
  rw [frameVector, Fintype.linearCombination_apply]
  simpa only [frameBasis_apply, frameBasis_repr_apply] using (frameBasis θ φ).sum_repr v

/-- Two vectors with the same components in one spherical frame are equal. -/
theorem ext_frame {θ φ : ℝ} {v w : ℝ^3} (h : ∀ k, ⟪frame θ φ k, v⟫ = ⟪frame θ φ k, w⟫) :
    v = w := by
  rw [← frameVector_inner_frame θ φ v, ← frameVector_inner_frame θ φ w]
  exact congrArg _ (funext h)

/-- The Euclidean norm of a frame vector is the Euclidean norm of its components. -/
theorem norm_sq_frameVector (θ φ : ℝ) (c : Fin 3 → ℝ) :
    ‖frameVector θ φ c‖ ^ 2 = ∑ k, c k ^ 2 := by
  rw [← (frameBasis θ φ).sum_sq_inner_left (frameVector θ φ c)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [frameBasis_apply, real_inner_comm, inner_frame_frameVector]

/-- The change of frame components under differentiation in the polar angle:
`∂_θ e_r = e_θ` and `∂_θ e_θ = -e_r`, while `e_φ` does not depend on `θ`. -/
def polarConnection : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ where
  toFun c := ![-c 1, c 0, 0]
  map_add' c d := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' a c := by
    ext i
    fin_cases i <;> simp

/-- The polar connection rotates the radial and polar components. -/
@[simp]
theorem polarConnection_apply (c : Fin 3 → ℝ) : polarConnection c = ![-c 1, c 0, 0] := rfl

/-- The change of frame components under differentiation in the azimuth at polar angle `θ`:
`∂_φ e_r = sin θ e_φ`, `∂_φ e_θ = cos θ e_φ` and `∂_φ e_φ = -(sin θ e_r + cos θ e_θ)`. -/
def azimuthalConnection (θ : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ where
  toFun c := ![-(Real.sin θ * c 2), -(Real.cos θ * c 2), Real.sin θ * c 0 + Real.cos θ * c 1]
  map_add' c d := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a c := by
    ext i
    fin_cases i <;> simp <;> ring

/-- The azimuthal connection exchanges the swirl with the horizontal radial direction. -/
@[simp]
theorem azimuthalConnection_apply (θ : ℝ) (c : Fin 3 → ℝ) :
    azimuthalConnection θ c =
      ![-(Real.sin θ * c 2), -(Real.cos θ * c 2), Real.sin θ * c 0 + Real.cos θ * c 1] := rfl

/-- A frame vector with fixed angles has the frame vector of the component derivative as
its radial derivative. -/
theorem hasDerivAt_frameVector_radial {c : ℝ → Fin 3 → ℝ} {c' : Fin 3 → ℝ} {r : ℝ}
    (θ φ : ℝ) (hc : HasDerivAt c c' r) :
    HasDerivAt (fun s ↦ frameVector θ φ (c s)) (frameVector θ φ c') r :=
  (frameVector θ φ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r hc

/-- The radial derivative of a frame vector with fixed angles is the frame vector of the
component derivative, with no differentiability assumption: both sides vanish together. -/
theorem deriv_frameVector_radial (θ φ : ℝ) (c : ℝ → Fin 3 → ℝ) (r : ℝ) :
    deriv (fun s ↦ frameVector θ φ (c s)) r = frameVector θ φ (deriv c r) := by
  by_cases hc : DifferentiableAt ℝ c r
  · exact (hasDerivAt_frameVector_radial θ φ hc.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hc, map_zero]
    refine deriv_zero_of_not_differentiableAt fun h ↦ hc ?_
    have heq : c = fun s k ↦ ⟪frame θ φ k, frameVector θ φ (c s)⟫ := by
      funext s k
      rw [inner_frame_frameVector]
    rw [heq]
    exact differentiableAt_pi.mpr fun k ↦ (differentiableAt_const (frame θ φ k)).inner ℝ h

/-- Differentiating a frame vector in the polar angle adds the polar connection to the
derivative of its components. -/
theorem hasDerivAt_frameVector_polar {c : ℝ → Fin 3 → ℝ} {c' : Fin 3 → ℝ} {θ : ℝ}
    (φ : ℝ) (hc : HasDerivAt c c' θ) :
    HasDerivAt (fun t ↦ frameVector t φ (c t)) (frameVector θ φ (c' + polarConnection (c θ)))
      θ := by
  have hk (k : Fin 3) : HasDerivAt (fun t ↦ c t k) (c' k) θ := hasDerivAt_pi.mp hc k
  have h := (((hk 0).smul (hasDerivAt_radialFrame_polar θ φ)).add
    ((hk 1).smul (hasDerivAt_polarFrame_polar θ φ))).add
      ((hk 2).smul (hasDerivAt_const θ (azimuthalFrame φ)))
  simp only [frameVector_apply]
  convert h using 1
  simp only [polarConnection_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  module

/-- Differentiating a frame vector with fixed components in the azimuth applies the
azimuthal connection to its components. -/
theorem hasDerivAt_frameVector_azimuthal (c : Fin 3 → ℝ) (θ φ : ℝ) :
    HasDerivAt (fun t ↦ frameVector θ t c) (frameVector θ φ (azimuthalConnection θ c)) φ := by
  have h := (((hasDerivAt_radialFrame_azimuthal θ φ).const_smul (c 0)).add
    ((hasDerivAt_polarFrame_azimuthal θ φ).const_smul (c 1))).add
      ((hasDerivAt_azimuthalFrame θ φ).const_smul (c 2))
  simp only [frameVector_apply]
  convert h using 1
  simp only [azimuthalConnection_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  module

/-! ### Coordinate lines -/

/-- The radial coordinate line has the radial vector as velocity. -/
theorem hasDerivAt_point_radial (r θ φ : ℝ) :
    HasDerivAt (fun s ↦ point s θ φ) (radialFrame θ φ) r := by
  have h := (hasDerivAt_id r).smul_const (radialFrame θ φ)
  rw [one_smul] at h
  exact h

/-- The polar coordinate line has velocity `r e_θ`. -/
theorem hasDerivAt_point_polar (r θ φ : ℝ) :
    HasDerivAt (fun t ↦ point r t φ) (r • polarFrame θ φ) θ :=
  (hasDerivAt_radialFrame_polar θ φ).const_smul r

/-- The azimuthal coordinate line has velocity `r sin θ e_φ`. -/
theorem hasDerivAt_point_azimuthal (r θ φ : ℝ) :
    HasDerivAt (fun t ↦ point r θ t) ((r * Real.sin θ) • azimuthalFrame φ) φ := by
  have h := (hasDerivAt_radialFrame_azimuthal θ φ).const_smul r
  rw [smul_smul] at h
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative in the radial direction is the derivative along the radial line. -/
theorem fderiv_apply_radialFrame {F : ℝ^3 → E} {r θ φ : ℝ}
    (hF : DifferentiableAt ℝ F (point r θ φ)) :
    fderiv ℝ F (point r θ φ) (radialFrame θ φ) = deriv (fun s ↦ F (point s θ φ)) r :=
  ((hF.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_point_radial r θ φ)).deriv).symm

/-- The derivative in the polar direction is the derivative along the polar line divided
by `r`. -/
theorem fderiv_apply_polarFrame {F : ℝ^3 → E} {r θ φ : ℝ} (hr : r ≠ 0)
    (hF : DifferentiableAt ℝ F (point r θ φ)) :
    fderiv ℝ F (point r θ φ) (polarFrame θ φ) = r⁻¹ • deriv (fun t ↦ F (point r t φ)) θ := by
  have h : HasDerivAt (fun t ↦ F (point r t φ))
      (fderiv ℝ F (point r θ φ) (r • polarFrame θ φ)) θ :=
    hF.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_point_polar r θ φ)
  rw [h.deriv, map_smul, smul_smul, inv_mul_cancel₀ hr, one_smul]

/-- The derivative in the azimuthal direction is the derivative along the azimuthal line
divided by `r sin θ`. -/
theorem fderiv_apply_azimuthalFrame {F : ℝ^3 → E} {r θ φ : ℝ} (hr : r ≠ 0)
    (hθ : Real.sin θ ≠ 0) (hF : DifferentiableAt ℝ F (point r θ φ)) :
    fderiv ℝ F (point r θ φ) (azimuthalFrame φ) =
      (r * Real.sin θ)⁻¹ • deriv (fun t ↦ F (point r θ t)) φ := by
  have h : HasDerivAt (fun t ↦ F (point r θ t))
      (fderiv ℝ F (point r θ φ) ((r * Real.sin θ) • azimuthalFrame φ)) φ :=
    hF.hasFDerivAt.comp_hasDerivAt φ (hasDerivAt_point_azimuthal r θ φ)
  rw [h.deriv, map_smul, smul_smul, inv_mul_cancel₀ (mul_ne_zero hr hθ), one_smul]

end PDE.CoordinateSystems.Spherical
