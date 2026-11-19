/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.Calculus
public import PDE.FDeriv.Operators
import PDE.Analysis.Calculus.SecondDerivativeComposition

/-!
# The Laplacian in spherical coordinates

At a point `point r θ φ` with `r ≠ 0` and `sin θ ≠ 0`, the coordinate Laplacian of a map that
is `C²` there is

`∂_r² F + (2/r) ∂_r F + r⁻² (∂_θ² F + cot θ ∂_θ F) + (r sin θ)⁻² ∂_φ² F`,

where the derivatives are taken along the coordinate lines through the point. The codomain
is any real normed space, so vector fields are covered without choosing components. The
proof sums the second derivatives along the three orthogonal frame directions, which give the
Laplacian, and cancels the first-order terms coming from the curvature of the coordinate
lines.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coordinate Laplacian in spherical coordinates, for any `C²` map into a real normed
space, away from the origin and the symmetry axis. -/
theorem laplacian_point {F : ℝ^3 → E} {r θ φ : ℝ} (hF : ContDiffAt ℝ 2 F (point r θ φ))
    (hr : r ≠ 0) (hθ : Real.sin θ ≠ 0) :
    PDE.laplacian F (point r θ φ) =
      deriv (deriv fun s ↦ F (point s θ φ)) r + (2 / r) • deriv (fun s ↦ F (point s θ φ)) r +
        (r ^ 2)⁻¹ • (deriv (deriv fun t ↦ F (point r t φ)) θ +
          (Real.cos θ / Real.sin θ) • deriv (fun t ↦ F (point r t φ)) θ) +
        (r ^ 2 * Real.sin θ ^ 2)⁻¹ • deriv (deriv fun t ↦ F (point r θ t)) φ := by
  have hd : DifferentiableAt ℝ F (point r θ φ) := hF.differentiableAt (by norm_num)
  have hrad := PDE.Calculus.hasDerivAt_deriv_comp_of_contDiffAt (c := fun s ↦ point s θ φ)
    (c' := fun _ ↦ radialFrame θ φ) (t₀ := r) hF
    (Filter.Eventually.of_forall fun s ↦ hasDerivAt_point_radial s θ φ)
    (hasDerivAt_const r (radialFrame θ φ))
  have hpol := PDE.Calculus.hasDerivAt_deriv_comp_of_contDiffAt (c := fun t ↦ point r t φ)
    (c' := fun t ↦ r • polarFrame t φ) (t₀ := θ) hF
    (Filter.Eventually.of_forall fun t ↦ hasDerivAt_point_polar r t φ)
    ((hasDerivAt_polarFrame_polar θ φ).const_smul r)
  have hazi := PDE.Calculus.hasDerivAt_deriv_comp_of_contDiffAt (c := fun t ↦ point r θ t)
    (c' := fun t ↦ (r * Real.sin θ) • azimuthalFrame t) (t₀ := φ) hF
    (Filter.Eventually.of_forall fun t ↦ hasDerivAt_point_azimuthal r θ t)
    ((hasDerivAt_azimuthalFrame θ φ).const_smul (r * Real.sin θ))
  have hrad1 : HasDerivAt (fun s ↦ F (point s θ φ)) (fderiv ℝ F (point r θ φ) (radialFrame θ φ))
      r := hd.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_point_radial r θ φ)
  have hpol1 : HasDerivAt (fun t ↦ F (point r t φ))
      (fderiv ℝ F (point r θ φ) (r • polarFrame θ φ)) θ :=
    hd.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_point_polar r θ φ)
  rw [hrad.deriv, hpol.deriv, hazi.deriv, hrad1.deriv, hpol1.deriv,
    hF.coordinate_laplacian_eq_laplacian,
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis F
      (frameBasis θ φ)) (point r θ φ)]
  simp only [iteratedFDeriv_two_apply, Fin.sum_univ_three, frameBasis_apply, frame,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, map_smul, map_add, map_neg, map_zero, _root_.smul_apply,
    add_zero, smul_add,
    smul_neg, smul_smul]
  match_scalars <;> field_simp <;> ring

end PDE.CoordinateSystems.Spherical
