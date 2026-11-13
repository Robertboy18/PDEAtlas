/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Spherical coordinate points and frames

The polar angle is measured from the positive third coordinate axis. The
radial, polar, and azimuthal frame vectors are explicit functions of the two
angles, including the degenerate angular chart at the symmetry axis.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

/-- The radial unit vector for polar angle `θ` and azimuthal angle `φ`. -/
def radialFrame (θ φ : ℝ) : ℝ^3 :=
  WithLp.toLp 2 ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

/-- The unit vector in the direction of increasing polar angle. -/
def polarFrame (θ φ : ℝ) : ℝ^3 :=
  WithLp.toLp 2 ![Real.cos θ * Real.cos φ, Real.cos θ * Real.sin φ, -Real.sin θ]

/-- The unit vector in the direction of increasing azimuthal angle. -/
def azimuthalFrame (φ : ℝ) : ℝ^3 :=
  WithLp.toLp 2 ![-Real.sin φ, Real.cos φ, 0]

/-- The spherical point of radius `r`, polar angle `θ`, and azimuthal angle `φ`. -/
def point (r θ φ : ℝ) : ℝ^3 := r • radialFrame θ φ

/-- The radial frame has unit Euclidean norm. -/
theorem norm_radialFrame (θ φ : ℝ) : ‖radialFrame θ φ‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_three]
  change (Real.sin θ * Real.cos φ) ^ 2 + (Real.sin θ * Real.sin φ) ^ 2 +
    Real.cos θ ^ 2 = 1 ^ 2
  calc
    _ = Real.sin θ ^ 2 * (Real.sin φ ^ 2 + Real.cos φ ^ 2) + Real.cos θ ^ 2 := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one, Real.sin_sq_add_cos_sq, one_pow]

/-- A positive spherical radius is the Euclidean norm of its point. -/
theorem norm_point {r : ℝ} (hr : 0 < r) (θ φ : ℝ) : ‖point r θ φ‖ = r := by
  rw [point, norm_smul, norm_radialFrame, Real.norm_eq_abs, abs_of_pos hr, mul_one]

/-- The squared norm of the spherical point of radius `r` is `r²`, for every real `r`. -/
theorem norm_point_sq (r θ φ : ℝ) : ‖point r θ φ‖ ^ 2 = r ^ 2 := by
  rw [point, norm_smul, norm_radialFrame, mul_one, Real.norm_eq_abs, sq_abs]

/-- The radial unit vector depends continuously on the two angles. -/
theorem continuous_radialFrame : Continuous fun p : ℝ × ℝ ↦ radialFrame p.1 p.2 := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [radialFrame] <;> fun_prop

/-- A positive-radius spherical point is nonzero, including at the polar axis. -/
theorem point_ne_zero {r : ℝ} (hr : 0 < r) (θ φ : ℝ) : point r θ φ ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_point hr]
  exact hr.ne'

end PDE.CoordinateSystems.Spherical
