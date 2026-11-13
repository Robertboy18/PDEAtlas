/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.AxisymmetricField
public import PDE.Analysis.Calculus.Radial.ArctanBounds
import PDE.CoordinateSystems.RadialCompactification

/-!
# Axisymmetric fields in the compactified radius

For a scale `s > 0` the compactified radius `β = arctan (r / s)` maps the positive half-line
onto `(0, π / 2)`, with inverse `r = s tan β`. A profile `g β θ` of the compactified radius and
the polar angle gives the physical profile `compactifiedProfile s g r θ = g (arctan (r / s)) θ`.
At `r = s tan β` the radial derivatives become

`∂_r = (cos² β / s) ∂_β`,  `∂_r² = (cos² β / s)² ∂_β² - (2 sin β cos³ β / s²) ∂_β`,

and `1 / r = cos β / (s sin β)`. Substituting these into the spherical-frame formulas gives the
derivative matrix, the convective term and the vector Laplacian of the axisymmetric field with
components `g` directly in the variables `(β, θ)`. Hou, Wang and Yang extend their numerical
profile to the whole space by the change of variables `r = tan β`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 5.5 and Appendix D.
  <https://arxiv.org/abs/2509.25116v2>
* T. Hou, Y. Wang and C. Yang, code for arXiv:2509.25116, file `src/NS_Terms.jl`, function
  `get_gradient`.
  <https://github.com/HouGroup2026/3d-navier-stokes-nonuniqueness>
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open scoped RealInnerProductSpace Topology
open Set PDE.Analysis.Radial

/-- The compactified radius `arctan (r / s)` inverts `r = s tan β` on `(-π/2, π/2)`. -/
theorem arctan_mul_tan_div {s β : ℝ} (hs : s ≠ 0) (hβ : β ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    Real.arctan (s * Real.tan β / s) = β := by
  rw [mul_div_cancel_left₀ _ hs, Real.arctan_tan hβ.1 hβ.2]

private theorem scale_div_sq_add_tan_sq {s β : ℝ} (hs : s ≠ 0) (hc : Real.cos β ≠ 0) :
    s / (s ^ 2 + (s * Real.tan β) ^ 2) = Real.cos β ^ 2 / s := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq β

/-- The profile `(r, θ) ↦ g (arctan (r / s)) θ` of the physical radius given by a profile `g` of
the compactified radius `β = arctan (r / s)`. -/
def compactifiedProfile {G : Type*} (s : ℝ) (g : ℝ → ℝ → G) (r θ : ℝ) : G :=
  g (Real.arctan (r / s)) θ

/-- At the physical radius `s tan β` the profile takes the compactified value `g β θ`. -/
theorem compactifiedProfile_mul_tan {G : Type*} {s β : ℝ} (g : ℝ → ℝ → G) (hs : s ≠ 0)
    (hβ : β ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (θ : ℝ) :
    compactifiedProfile s g (s * Real.tan β) θ = g β θ := by
  rw [compactifiedProfile, arctan_mul_tan_div hs hβ]

section Profile

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The physical profile is as regular as the compactified one. -/
theorem contDiffAt_compactifiedProfile {n : WithTop ℕ∞} {s r θ : ℝ} {g : ℝ → ℝ → G}
    (hg : ContDiffAt ℝ n (Function.uncurry g) (Real.arctan (r / s), θ)) :
    ContDiffAt ℝ n (Function.uncurry (compactifiedProfile s g)) (r, θ) := by
  have hmap : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ (Real.arctan (p.1 / s), p.2)) (r, θ) :=
    ((Real.contDiff_arctan.comp (contDiff_fst.div_const s)).prodMk contDiff_snd).contDiffAt
  have h := hg.comp (r, θ) hmap
  exact h

/-- The radial derivative in the compactified radius: `∂_r = (cos² β / s) ∂_β`. -/
theorem deriv_compactifiedProfile_radial {s β θ : ℝ} {g : ℝ → ℝ → G} (hs : s ≠ 0)
    (hβ : β ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hg : DifferentiableAt ℝ (fun b ↦ g b θ) β) :
    deriv (fun r ↦ compactifiedProfile s g r θ) (s * Real.tan β) =
      (Real.cos β ^ 2 / s) • deriv (fun b ↦ g b θ) β := by
  have hg' : DifferentiableAt ℝ (fun b ↦ g b θ) (Real.arctan (s * Real.tan β / s)) := by
    rwa [arctan_mul_tan_div hs hβ]
  have h := hg'.hasDerivAt.scomp (s * Real.tan β) (hasDerivAt_arctan_div hs (s * Real.tan β))
  simp only [Function.comp_def] at h
  rw [show (fun r ↦ compactifiedProfile s g r θ) = fun r ↦ g (Real.arctan (r / s)) θ from rfl,
    h.deriv, arctan_mul_tan_div hs hβ,
    scale_div_sq_add_tan_sq hs (Real.cos_pos_of_mem_Ioo hβ).ne']

/-- The second radial derivative in the compactified radius:
`∂_r² = (cos² β / s)² ∂_β² - (2 sin β cos³ β / s²) ∂_β`. -/
theorem deriv_deriv_compactifiedProfile_radial {s β θ : ℝ} {g : ℝ → ℝ → G} (hs : s ≠ 0)
    (hβ : β ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hg : ContDiffAt ℝ 2 (fun b ↦ g b θ) β) :
    deriv (deriv fun r ↦ compactifiedProfile s g r θ) (s * Real.tan β) =
      (Real.cos β ^ 2 / s) ^ 2 • deriv (deriv fun b ↦ g b θ) β -
        (2 * Real.sin β * Real.cos β ^ 3 / s ^ 2) • deriv (fun b ↦ g b θ) β := by
  have hc := (Real.cos_pos_of_mem_Ioo hβ).ne'
  have hβ₀ : Real.arctan (s * Real.tan β / s) = β := arctan_mul_tan_div hs hβ
  have hg' : ContDiffAt ℝ 2 (fun b ↦ g b θ) (Real.arctan (s * Real.tan β / s)) := by
    rwa [hβ₀]
  have h := hasDerivAt_deriv_comp_arctan_div_of_contDiffAt hs hg'
  have hsq : s ^ 2 + (s * Real.tan β) ^ 2 = s ^ 2 / Real.cos β ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq β
  have hcoef : -2 * (s * Real.tan β) * s / (s ^ 2 + (s * Real.tan β) ^ 2) ^ 2 =
      -(2 * Real.sin β * Real.cos β ^ 3 / s ^ 2) := by
    rw [hsq, Real.tan_eq_sin_div_cos]
    field_simp
  change deriv (deriv fun t ↦ g (Real.arctan (t / s)) θ) (s * Real.tan β) = _
  rw [h.deriv, hβ₀, scale_div_sq_add_tan_sq hs hc, hcoef, neg_smul, ← sub_eq_add_neg]

/-- The spherical Laplacian written in the compactified radius `β` and the polar angle `θ`:
`(cos β / s)² (cos² β ∂_β² g + (2 cos³ β / sin β) ∂_β g + (∂_θ² g + cot θ ∂_θ g) / sin² β)`. -/
def compactifiedSphericalLaplacian (s : ℝ) (g : ℝ → ℝ → G) (β θ : ℝ) : G :=
  (Real.cos β / s) ^ 2 • (Real.cos β ^ 2 • deriv (deriv fun b ↦ g b θ) β +
    (2 * Real.cos β ^ 3 / Real.sin β) • deriv (fun b ↦ g b θ) β +
    (Real.sin β ^ 2)⁻¹ • (deriv (deriv fun t ↦ g β t) θ +
      (Real.cos θ / Real.sin θ) • deriv (fun t ↦ g β t) θ))

/-- The spherical Laplacian of the physical profile at `r = s tan β` is the compactified
spherical Laplacian of `g` at `β`. -/
theorem sphericalLaplacian_compactifiedProfile {s β θ : ℝ} {g : ℝ → ℝ → G} (hs : 0 < s)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hg : ContDiffAt ℝ 2 (Function.uncurry g) (β, θ)) :
    sphericalLaplacian (compactifiedProfile s g) (s * Real.tan β) θ =
      compactifiedSphericalLaplacian s g β θ := by
  have hβ' : β ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hβ.1, Real.pi_pos], hβ.2⟩
  have hc := (Real.cos_pos_of_mem_Ioo hβ').ne'
  have hsb := (Real.sin_pos_of_pos_of_lt_pi hβ.1 (by linarith [hβ.2, Real.pi_pos])).ne'
  have hrad : ContDiffAt ℝ 2 (fun b ↦ g b θ) β := by
    have h := hg.comp β (contDiffAt_id.prodMk contDiffAt_const)
    exact h
  have hpol : (fun t ↦ compactifiedProfile s g (s * Real.tan β) t) = fun t ↦ g β t :=
    funext fun t ↦ compactifiedProfile_mul_tan g hs.ne' hβ' t
  rw [sphericalLaplacian, compactifiedSphericalLaplacian,
    deriv_deriv_compactifiedProfile_radial hs.ne' hβ' hrad,
    deriv_compactifiedProfile_radial hs.ne' hβ' (hrad.differentiableAt (by norm_num)), hpol,
    Real.tan_eq_sin_div_cos]
  match_scalars <;> field_simp
  linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq β

end Profile

/-! ### The axisymmetric field of a compactified profile -/

variable {g : ℝ → ℝ → Fin 3 → ℝ} {s β θ φ : ℝ}

private theorem mem_Ioo_of_mem_Ioo_zero {β : ℝ} (hβ : β ∈ Ioo 0 (Real.pi / 2)) :
    β ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨by linarith [hβ.1, Real.pi_pos], hβ.2⟩

private theorem contDiffAt_compactifiedProfile_mul_tan {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {q : ℝ → ℝ → G} {n : WithTop ℕ∞} (hs : 0 < s)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hg : ContDiffAt ℝ n (Function.uncurry q) (β, θ)) :
    ContDiffAt ℝ n (Function.uncurry (compactifiedProfile s q)) (s * Real.tan β, θ) := by
  apply contDiffAt_compactifiedProfile
  rwa [arctan_mul_tan_div hs.ne' (mem_Ioo_of_mem_Ioo_zero hβ)]

private theorem deriv_compactifiedProfile_radial_apply (hs : 0 < s)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hg : ContDiffAt ℝ 1 (Function.uncurry g) (β, θ))
    (k : Fin 3) :
    deriv (fun r ↦ compactifiedProfile s g r θ k) (s * Real.tan β) =
      Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ k) β := by
  have hk : DifferentiableAt ℝ (fun b ↦ g b θ k) β := by
    have h := hg.comp β (contDiffAt_id.prodMk contDiffAt_const)
    exact (contDiffAt_pi.mp h k).differentiableAt (by norm_num)
  exact deriv_compactifiedProfile_radial (g := fun b t ↦ g b t k) hs.ne'
    (mem_Ioo_of_mem_Ioo_zero hβ) hk

private theorem inv_mul_tan {s β : ℝ} :
    (s * Real.tan β)⁻¹ = Real.cos β / (s * Real.sin β) := by
  rw [Real.tan_eq_sin_div_cos, mul_div_assoc', inv_div]

/-- The frame matrix of the derivative of the axisymmetric field with compactified profile `g`,
in the variables `(β, θ)`; `cos β / (s sin β)` is the reciprocal physical radius. Its entry
`(i, j)` is the component `⟪e_i, (Du) e_j⟫`. The gradient blocks `A_ij` of the verification
code of Hou, Wang and Yang (`get_gradient` in `src/NS_Terms.jl` with `weight_flag = true`) are
the transpose scaled by `tan β`: `A_ij = tan β · compactifiedGradientMatrix s g β θ j i`. -/
def compactifiedGradientMatrix (s : ℝ) (g : ℝ → ℝ → Fin 3 → ℝ) (β θ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ 0) β,
      Real.cos β / (s * Real.sin β) * (deriv (fun t ↦ g β t 0) θ - g β θ 1),
      -(Real.cos β / (s * Real.sin β) * g β θ 2);
    Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ 1) β,
      Real.cos β / (s * Real.sin β) * (deriv (fun t ↦ g β t 1) θ + g β θ 0),
      -(Real.cos β / (s * Real.sin β) * (Real.cos θ / Real.sin θ * g β θ 2));
    Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ 2) β,
      Real.cos β / (s * Real.sin β) * deriv (fun t ↦ g β t 2) θ,
      Real.cos β / (s * Real.sin β) * (g β θ 0 + Real.cos θ / Real.sin θ * g β θ 1)]

/-- The physical frame matrix at `r = s tan β` is the compactified one. -/
theorem sphericalGradientMatrix_compactifiedProfile (hs : 0 < s) (hβ : β ∈ Ioo 0 (Real.pi / 2))
    (hg : ContDiffAt ℝ 1 (Function.uncurry g) (β, θ)) :
    sphericalGradientMatrix (compactifiedProfile s g) (s * Real.tan β) θ =
      compactifiedGradientMatrix s g β θ := by
  have hval (t : ℝ) : compactifiedProfile s g (s * Real.tan β) t = g β t :=
    compactifiedProfile_mul_tan g hs.ne' (mem_Ioo_of_mem_Ioo_zero hβ) t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [sphericalGradientMatrix, compactifiedGradientMatrix, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, hval,
      deriv_compactifiedProfile_radial_apply hs hβ hg, div_eq_mul_inv (b := s * Real.tan β),
      inv_mul_tan] <;>
    ring

/-- The frame components of the derivative of the axisymmetric field with compactified profile
`g`, at the physical radius `s tan β`. -/
theorem frame_fderiv_axisymmetricField_compactifiedProfile (hs : 0 < s)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Ioo 0 Real.pi)
    (hg : ContDiffAt ℝ 1 (Function.uncurry g) (β, θ)) (i j : Fin 3) :
    ⟪frame θ φ i, fderiv ℝ (axisymmetricField (compactifiedProfile s g))
        (point (s * Real.tan β) θ φ) (frame θ φ j)⟫ =
      compactifiedGradientMatrix s g β θ i j := by
  rw [frame_fderiv_axisymmetricField (mul_tan_pos hs hβ) hθ
    (contDiffAt_compactifiedProfile_mul_tan hs hβ hg),
    sphericalGradientMatrix_compactifiedProfile hs hβ hg]

/-- The convective term `(u·∇)u` of the axisymmetric field with compactified profile `g`, in
frame components at the physical radius `s tan β`. -/
theorem frame_advectiveDerivative_axisymmetricField_compactifiedProfile (hs : 0 < s)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Ioo 0 Real.pi)
    (hg : ContDiffAt ℝ 1 (Function.uncurry g) (β, θ)) :
    frameCoords (point (s * Real.tan β) θ φ)
        (PDE.advectiveDerivative (axisymmetricField (compactifiedProfile s g))
          (axisymmetricField (compactifiedProfile s g)) (point (s * Real.tan β) θ φ)) =
      ![g β θ 0 * (Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ 0) β) +
          Real.cos β / (s * Real.sin β) *
            (g β θ 1 * deriv (fun t ↦ g β t 0) θ - (g β θ 1 ^ 2 + g β θ 2 ^ 2)),
        g β θ 0 * (Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ 1) β) +
          Real.cos β / (s * Real.sin β) * (g β θ 1 * deriv (fun t ↦ g β t 1) θ +
            g β θ 0 * g β θ 1 - Real.cos θ / Real.sin θ * g β θ 2 ^ 2),
        g β θ 0 * (Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ 2) β) +
          Real.cos β / (s * Real.sin β) * (g β θ 1 * deriv (fun t ↦ g β t 2) θ +
            g β θ 0 * g β θ 2 + Real.cos θ / Real.sin θ * g β θ 1 * g β θ 2)] := by
  have hval (t : ℝ) : compactifiedProfile s g (s * Real.tan β) t = g β t :=
    compactifiedProfile_mul_tan g hs.ne' (mem_Ioo_of_mem_Ioo_zero hβ) t
  rw [frame_advectiveDerivative_axisymmetricField (mul_tan_pos hs hβ) hθ
    (contDiffAt_compactifiedProfile_mul_tan hs hβ hg)]
  ext k
  fin_cases k <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, hval,
      deriv_compactifiedProfile_radial_apply hs hβ hg, div_eq_mul_inv (b := s * Real.tan β),
      inv_mul_tan] <;>
    ring

/-- The transport term `(v·∇)u` of two axisymmetric fields with compactified profiles, `w` for
`v` and `g` for `u`, in frame components at the physical radius `s tan β`. -/
theorem frame_advectiveDerivative_axisymmetricField_axisymmetricField_compactifiedProfile
    {w : ℝ → ℝ → Fin 3 → ℝ} (hs : 0 < s) (hβ : β ∈ Ioo 0 (Real.pi / 2))
    (hθ : θ ∈ Ioo 0 Real.pi) (hg : ContDiffAt ℝ 1 (Function.uncurry g) (β, θ)) :
    frameCoords (point (s * Real.tan β) θ φ)
        (PDE.advectiveDerivative (axisymmetricField (compactifiedProfile s w))
          (axisymmetricField (compactifiedProfile s g)) (point (s * Real.tan β) θ φ)) =
      ![w β θ 0 * (Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ 0) β) +
          Real.cos β / (s * Real.sin β) *
            (w β θ 1 * deriv (fun t ↦ g β t 0) θ - (w β θ 1 * g β θ 1 + w β θ 2 * g β θ 2)),
        w β θ 0 * (Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ 1) β) +
          Real.cos β / (s * Real.sin β) * (w β θ 1 * deriv (fun t ↦ g β t 1) θ +
            w β θ 1 * g β θ 0 - Real.cos θ / Real.sin θ * w β θ 2 * g β θ 2),
        w β θ 0 * (Real.cos β ^ 2 / s * deriv (fun b ↦ g b θ 2) β) +
          Real.cos β / (s * Real.sin β) * (w β θ 1 * deriv (fun t ↦ g β t 2) θ +
            w β θ 2 * g β θ 0 + Real.cos θ / Real.sin θ * w β θ 2 * g β θ 1)] := by
  have hβ' := mem_Ioo_of_mem_Ioo_zero hβ
  have hvalg (t : ℝ) : compactifiedProfile s g (s * Real.tan β) t = g β t :=
    compactifiedProfile_mul_tan g hs.ne' hβ' t
  have hvalw (t : ℝ) : compactifiedProfile s w (s * Real.tan β) t = w β t :=
    compactifiedProfile_mul_tan w hs.ne' hβ' t
  rw [frame_advectiveDerivative_axisymmetricField_axisymmetricField (mul_tan_pos hs hβ) hθ
    (contDiffAt_compactifiedProfile_mul_tan hs hβ hg)]
  ext k
  fin_cases k <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, hvalg,
      hvalw, deriv_compactifiedProfile_radial_apply hs hβ hg,
      div_eq_mul_inv (b := s * Real.tan β), inv_mul_tan] <;>
    ring

/-- The linearized convection `(ū·∇)v + (v·∇)ū` about the axisymmetric field `ū` with
compactified profile `g`, for the axisymmetric field `v` with compactified profile `w`, in frame
components at the physical radius `s tan β`. -/
theorem frame_advectiveDerivative_add_advectiveDerivative_axisymmetricField_compactifiedProfile
    {w : ℝ → ℝ → Fin 3 → ℝ} (hs : 0 < s) (hβ : β ∈ Ioo 0 (Real.pi / 2))
    (hθ : θ ∈ Ioo 0 Real.pi) (hg : ContDiffAt ℝ 1 (Function.uncurry g) (β, θ))
    (hw : ContDiffAt ℝ 1 (Function.uncurry w) (β, θ)) :
    frameCoords (point (s * Real.tan β) θ φ)
        (PDE.advectiveDerivative (axisymmetricField (compactifiedProfile s g))
            (axisymmetricField (compactifiedProfile s w)) (point (s * Real.tan β) θ φ) +
          PDE.advectiveDerivative (axisymmetricField (compactifiedProfile s w))
            (axisymmetricField (compactifiedProfile s g)) (point (s * Real.tan β) θ φ)) =
      ![Real.cos β ^ 2 / s * (g β θ 0 * deriv (fun b ↦ w b θ 0) β +
            w β θ 0 * deriv (fun b ↦ g b θ 0) β) +
          Real.cos β / (s * Real.sin β) * (g β θ 1 * deriv (fun t ↦ w β t 0) θ +
            w β θ 1 * deriv (fun t ↦ g β t 0) θ - 2 * (g β θ 1 * w β θ 1 + g β θ 2 * w β θ 2)),
        Real.cos β ^ 2 / s * (g β θ 0 * deriv (fun b ↦ w b θ 1) β +
            w β θ 0 * deriv (fun b ↦ g b θ 1) β) +
          Real.cos β / (s * Real.sin β) * (g β θ 1 * deriv (fun t ↦ w β t 1) θ +
            w β θ 1 * deriv (fun t ↦ g β t 1) θ + g β θ 1 * w β θ 0 + w β θ 1 * g β θ 0 -
            2 * (Real.cos θ / Real.sin θ) * g β θ 2 * w β θ 2),
        Real.cos β ^ 2 / s * (g β θ 0 * deriv (fun b ↦ w b θ 2) β +
            w β θ 0 * deriv (fun b ↦ g b θ 2) β) +
          Real.cos β / (s * Real.sin β) * (g β θ 1 * deriv (fun t ↦ w β t 2) θ +
            w β θ 1 * deriv (fun t ↦ g β t 2) θ + g β θ 2 * w β θ 0 + w β θ 2 * g β θ 0 +
            Real.cos θ / Real.sin θ * (g β θ 2 * w β θ 1 + w β θ 2 * g β θ 1))] := by
  rw [frameCoords_add,
    frame_advectiveDerivative_axisymmetricField_axisymmetricField_compactifiedProfile hs hβ hθ hw,
    frame_advectiveDerivative_axisymmetricField_axisymmetricField_compactifiedProfile hs hβ hθ hg]
  ext k
  fin_cases k <;>
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    ring

/-- The vector Laplacian of the axisymmetric field with compactified profile `g`, in frame
components at the physical radius `s tan β`; `cos β / (s sin β)` is the reciprocal radius. -/
theorem frame_laplacian_axisymmetricField_compactifiedProfile (hs : 0 < s)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Ioo 0 Real.pi)
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (β, θ)) :
    frameCoords (point (s * Real.tan β) θ φ)
        (PDE.laplacian (axisymmetricField (compactifiedProfile s g))
          (point (s * Real.tan β) θ φ)) =
      ![compactifiedSphericalLaplacian s (fun b t ↦ g b t 0) β θ -
          (Real.cos β / (s * Real.sin β)) ^ 2 *
            (2 * g β θ 0 + 2 / Real.sin θ * deriv (fun t ↦ Real.sin t * g β t 1) θ),
        compactifiedSphericalLaplacian s (fun b t ↦ g b t 1) β θ +
          (Real.cos β / (s * Real.sin β)) ^ 2 *
            (2 * deriv (fun t ↦ g β t 0) θ - g β θ 1 / Real.sin θ ^ 2),
        compactifiedSphericalLaplacian s (fun b t ↦ g b t 2) β θ -
          (Real.cos β / (s * Real.sin β)) ^ 2 * (g β θ 2 / Real.sin θ ^ 2)] := by
  have hval (t : ℝ) : compactifiedProfile s g (s * Real.tan β) t = g β t :=
    compactifiedProfile_mul_tan g hs.ne' (mem_Ioo_of_mem_Ioo_zero hβ) t
  have hL (k : Fin 3) : sphericalLaplacian (fun r θ ↦ compactifiedProfile s g r θ k)
      (s * Real.tan β) θ = compactifiedSphericalLaplacian s (fun b t ↦ g b t k) β θ :=
    sphericalLaplacian_compactifiedProfile (g := fun b t ↦ g b t k) hs hβ
      (contDiffAt_pi.mp hg k)
  have hsθ := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hcb := (Real.cos_pos_of_mem_Ioo (mem_Ioo_of_mem_Ioo_zero hβ)).ne'
  have hsb := (Real.sin_pos_of_pos_of_lt_pi hβ.1 (by linarith [hβ.2, Real.pi_pos])).ne'
  rw [frame_laplacian_axisymmetricField (mul_tan_pos hs hβ) hθ
    (contDiffAt_compactifiedProfile_mul_tan hs hβ hg)]
  ext k
  fin_cases k <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, hval,
      hL] <;>
    rw [Real.tan_eq_sin_div_cos] <;> field_simp <;> ring

/-- At the physical radius `s tan β` the field has the frame components `g β θ`. -/
theorem axisymmetricField_compactifiedProfile_point (hs : 0 < s)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Ioo 0 Real.pi) (φ : ℝ) :
    axisymmetricField (compactifiedProfile s g) (point (s * Real.tan β) θ φ) =
      frameVector θ φ (g β θ) := by
  rw [axisymmetricField_point _ (mul_tan_pos hs hβ) hθ,
    compactifiedProfile_mul_tan g hs.ne' (mem_Ioo_of_mem_Ioo_zero hβ)]

/-- The derivative of the field in the direction of the position vector `s tan β e_r` is
`sin β cos β ∂_β g`. -/
theorem fderiv_axisymmetricField_compactifiedProfile_point_self (hs : 0 < s)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Ioo 0 Real.pi)
    (hg : ContDiffAt ℝ 1 (Function.uncurry g) (β, θ)) :
    fderiv ℝ (axisymmetricField (compactifiedProfile s g)) (point (s * Real.tan β) θ φ)
        (point (s * Real.tan β) θ φ) =
      frameVector θ φ ((Real.sin β * Real.cos β) • deriv (fun b ↦ g b θ) β) := by
  have hrad : DifferentiableAt ℝ (fun b ↦ g b θ) β := by
    have h := hg.comp β (contDiffAt_id.prodMk contDiffAt_const)
    exact h.differentiableAt (by norm_num)
  have hc := (Real.cos_pos_of_mem_Ioo (mem_Ioo_of_mem_Ioo_zero hβ)).ne'
  rw [fderiv_axisymmetricField_point_self (mul_tan_pos hs hβ) hθ
    (contDiffAt_compactifiedProfile_mul_tan hs hβ hg),
    deriv_compactifiedProfile_radial hs.ne' (mem_Ioo_of_mem_Ioo_zero hβ) hrad, smul_smul,
    Real.tan_eq_sin_div_cos]
  congr 2
  field_simp

/-- The gradient of the axisymmetric function with compactified profile `p`, in frame
components at the physical radius `s tan β`. -/
theorem frame_gradient_axisymmetricFunction_compactifiedProfile {p : ℝ → ℝ → ℝ} (hs : 0 < s)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Ioo 0 Real.pi)
    (hp : ContDiffAt ℝ 1 (Function.uncurry p) (β, θ)) :
    frameCoords (point (s * Real.tan β) θ φ)
        (gradient (axisymmetricFunction (compactifiedProfile s p))
          (point (s * Real.tan β) θ φ)) =
      ![Real.cos β ^ 2 / s * deriv (fun b ↦ p b θ) β,
        Real.cos β / (s * Real.sin β) * deriv (fun t ↦ p β t) θ, 0] := by
  have hrad : DifferentiableAt ℝ (fun b ↦ p b θ) β := by
    have h := hp.comp β (contDiffAt_id.prodMk contDiffAt_const)
    exact h.differentiableAt (by norm_num)
  have hval (t : ℝ) : compactifiedProfile s p (s * Real.tan β) t = p β t :=
    compactifiedProfile_mul_tan p hs.ne' (mem_Ioo_of_mem_Ioo_zero hβ) t
  rw [frame_gradient_axisymmetricFunction (mul_tan_pos hs hβ) hθ
    (contDiffAt_compactifiedProfile_mul_tan hs hβ hp),
    deriv_compactifiedProfile_radial hs.ne' (mem_Ioo_of_mem_Ioo_zero hβ) hrad]
  simp only [hval, smul_eq_mul, div_eq_mul_inv (b := s * Real.tan β), inv_mul_tan]
  ext k
  fin_cases k
  · simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  · simp

/-- The Laplacian of the axisymmetric function with compactified profile `p` at the physical
radius `s tan β` is its compactified spherical Laplacian. -/
theorem laplacian_axisymmetricFunction_compactifiedProfile {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {p : ℝ → ℝ → G} (hs : 0 < s) (hβ : β ∈ Ioo 0 (Real.pi / 2))
    (hθ : θ ∈ Ioo 0 Real.pi)
    (hp : ContDiffAt ℝ 2 (Function.uncurry p) (β, θ)) :
    PDE.laplacian (axisymmetricFunction (compactifiedProfile s p))
        (point (s * Real.tan β) θ φ) =
      compactifiedSphericalLaplacian s p β θ := by
  rw [laplacian_axisymmetricFunction_point (mul_tan_pos hs hβ) hθ
    (contDiffAt_compactifiedProfile_mul_tan hs hβ hp),
    sphericalLaplacian_compactifiedProfile hs hβ hp]

end PDE.CoordinateSystems.Spherical
