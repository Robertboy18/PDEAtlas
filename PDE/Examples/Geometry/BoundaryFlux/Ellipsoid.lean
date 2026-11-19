/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.Transport.Linear
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Closure
public import PDE.Spaces.Sobolev.Boundary.Flux.Rellich.Identity
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A nonorthogonal ellipsoid with nonzero boundary flux

The map `(x₀,x₁) ↦ (2x₀+x₁,x₁)` has nonorthogonal columns. Its pullback of the
unit ball has smooth graph boundary, so no atlas is assumed. The quadratic
defining function is zero on the boundary and its Rellich flux is strictly
positive, so the boundary term in the Rellich identity cannot be dropped.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Examples.BoundaryFlux.Ellipsoid

open Set Metric MeasureTheory SobolevSpace Boundary Boundary.Flux Trace.C1
open Geometry.SurfaceMeasure

/-- An invertible, nonorthogonal change of Euclidean coordinates. -/
def coordinates : ℝ^2 ≃L[ℝ] ℝ^2 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x ↦ WithLp.toLp 2 ![2 * x 0 + x 1, x 1]
      invFun := fun y ↦ WithLp.toLp 2 ![(y 0 - y 1) / 2, y 1]
      left_inv := by intro x; ext i; fin_cases i <;> simp
      right_inv := by
        intro x
        ext i
        fin_cases i <;>
          simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, Fin.zero_eta]
        cas
      map_add' := by
        intro x y
        ext i
        fin_cases i <;>
          simp only [Fin.isValue, Fin.mk_one, PiLp.add_apply, Fin.zero_eta, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_fin_one]
        cas
      map_smul' := by
        intro a x
        ext i
        fin_cases i <;>
          simp only [Fin.isValue, Fin.mk_one, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, RingHom.id_apply]
        cas }

/-- The coordinate columns have inner product two, and hence are not orthogonal. -/
theorem coordinates_columns_inner :
    inner ℝ (coordinates (EuclideanSpace.single 0 1))
      (coordinates (EuclideanSpace.single 1 1)) = 2 := by
  simp [coordinates, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]

/-- The curved ellipsoid cut out by the coordinate map. -/
def domain : Set (ℝ^2) := coordinates ⁻¹' ball 0 1

/-- The ellipsoid is open, as a preimage under the coordinate map. -/
theorem isOpen_domain : IsOpen domain := isOpen_ball.preimage coordinates.continuous

/-- Invertibility gives boundedness of the ellipsoid. -/
theorem isBounded_domain : Bornology.IsBounded domain := by
  have heq : coordinates.symm '' ball (0 : ℝ^2) 1 = domain := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [domain, mem_preimage, coordinates.apply_symm_apply] using hy
    · intro hx
      exact ⟨coordinates x, hx, coordinates.symm_apply_apply x⟩
  rw [← heq]
  exact coordinates.symm.toContinuousLinearMap.lipschitzWith.isBounded_image isBounded_ball

/-- Smooth graph boundary, transported from the ball by the linear map. -/
theorem hasC1GraphBoundary_domain : HasC1GraphBoundary domain :=
  ((Atlas.UnitBall.hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl)
    |>.preimage_continuousLinearEquiv coordinates

/-- The quadratic defining function. -/
def definingFunction (x : ℝ^2) : ℝ := 1 - ‖coordinates x‖ ^ 2

/-- The defining function is globally C². -/
theorem contDiff_definingFunction : ContDiff ℝ 2 definingFunction :=
  contDiff_const.sub (coordinates.contDiff.norm_sq (𝕜 := ℝ))

/-- It vanishes on the boundary. -/
theorem definingFunction_eq_zero_on_frontier {x : ℝ^2} (hx : x ∈ frontier domain) :
    definingFunction x = 0 := by
  have hAx : coordinates x ∈ frontier (ball (0 : ℝ^2) 1) := by
    change x ∈ coordinates.toHomeomorph ⁻¹' frontier (ball (0 : ℝ^2) 1)
    rwa [coordinates.toHomeomorph.preimage_frontier]
  have hnorm : ‖coordinates x‖ = 1 := by
    simpa only [frontier_ball (0 : ℝ^2) one_ne_zero, mem_sphere, dist_zero_right] using hAx
  simp only [definingFunction, hnorm, one_pow, sub_self]

/-- The gradient of the defining polynomial. -/
theorem gradient_definingFunction (x : ℝ^2) :
    ∇ definingFunction x = WithLp.toLp 2 ![-8 * x 0 - 4 * x 1, -4 * x 0 - 4 * x 1] := by
  have hd : HasFDerivAt definingFunction
      (-(2 • (innerSL ℝ (coordinates x)).comp coordinates.toContinuousLinearMap)) x :=
    coordinates.hasFDerivAt.norm_sq.const_sub 1
  ext i
  rw [gradient_apply_eq_partialDeriv, partialDeriv, hd.fderiv]
  fin_cases i <;>
    simp [coordinates, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two] <;>
    ring

/-- Its Laplacian is the constant `-12`. -/
theorem laplacian_definingFunction (x : ℝ^2) :
    laplacian definingFunction x = -12 := by
  rw [laplacian_eq_divergence_gradient]
  have heq : ∇ definingFunction =
      fun y ↦ WithLp.toLp 2 ![-8 * y 0 - 4 * y 1, -4 * y 0 - 4 * y 1] :=
    funext gradient_definingFunction
  rw [heq]
  simp only [divergence, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  change (∂[0] (fun y : ℝ^2 ↦ -8 * y 0 - 4 * y 1)) x +
    (∂[1] (fun y : ℝ^2 ↦ -4 * y 0 - 4 * y 1)) x = -12
  have h₀ : (∂[0] (fun y : ℝ^2 ↦ -8 * y 0 - 4 * y 1)) x = -8 := by
    cas
  have h₁ : (∂[1] (fun y : ℝ^2 ↦ -4 * y 0 - 4 * y 1)) x = -4 := by
    cas
  rw [h₀, h₁]
  norm_num

/-- The radial derivative records the nonisotropic quadratic form. -/
theorem inner_gradient_definingFunction (x : ℝ^2) :
    inner ℝ x (∇ definingFunction x) = -2 * ‖coordinates x‖ ^ 2 := by
  rw [gradient_definingFunction, EuclideanSpace.real_norm_sq_eq]
  simp [coordinates, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- The quadratic form has strictly positive integral on the open ellipsoid. -/
theorem integral_coordinate_norm_sq_pos :
    0 < ∫ x in domain, ‖coordinates x‖ ^ 2 := by
  have hi : IntegrableOn (fun x ↦ ‖coordinates x‖ ^ 2) domain :=
    (coordinates.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) isBounded_domain.isCompact_closure |>.mono_set subset_closure
  have hnonneg : 0 ≤ ∫ x in domain, ‖coordinates x‖ ^ 2 :=
    integral_nonneg fun x ↦ sq_nonneg _
  apply lt_of_le_of_ne hnonneg
  intro heq
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg _) hi).mp heq.symm
  have hpoint := Measure.eqOn_open_of_ae_eq hae isOpen_domain
    (coordinates.continuous.norm.pow 2).continuousOn continuousOn_const
  let x : ℝ^2 := WithLp.toLp 2 ![1 / 4, 0]
  have hx : x ∈ domain := by
    simp only [domain, mem_preimage, mem_ball, dist_zero_right]
    rw [EuclideanSpace.norm_eq]
    norm_num [coordinates, x, Fin.sum_univ_two]
    have hs : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num [hs]
  have hzero := hpoint hx
  change ‖coordinates x‖ ^ 2 = 0 at hzero
  rw [EuclideanSpace.real_norm_sq_eq] at hzero
  norm_num [coordinates, x, Fin.sum_univ_two] at hzero

/-- The full Rellich flux is forty-eight times a strictly positive volume integral. -/
theorem rellich_flux_eq_pos :
    letI := hasC1GraphBoundary_domain.c1ExtensionAtlas isOpen_domain isBounded_domain
    let u := definingFunction
    let G := ∇ u
    Integrable (normalFlux (Ω := domain) (fun x ↦ ‖G x‖ ^ 2 • x))
        (surfaceMeasure domain) ∧
      (∫ x, normalFlux (Ω := domain) (fun y ↦ ‖G y‖ ^ 2 • y) x
        ∂surfaceMeasure domain) = 48 * ∫ x in domain, ‖coordinates x‖ ^ 2 ∧
      0 < ∫ x, normalFlux (Ω := domain) (fun y ↦ ‖G y‖ ^ 2 • y) x
        ∂surfaceMeasure domain := by
  let := hasC1GraphBoundary_domain.c1ExtensionAtlas isOpen_domain isBounded_domain
  have hu := ContDiffUpToBoundary.of_contDiff contDiff_definingFunction isBounded_domain
  have h := rellich_identity_of_contDiffUpToBoundary hasC1GraphBoundary_domain hu
    contDiff_definingFunction.continuous.continuousOn
    (fun x hx ↦ definingFunction_eq_zero_on_frontier hx) 0
  have hcompletion : EqOn (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
      (∇ definingFunction) (closure domain) :=
    (hu.of_le (show 1 ≤ 2 by omega)).completedGradient_eq_gradient_extension isOpen_domain
      (contDiff_definingFunction.of_le (by norm_num)) (fun _ _ ↦ rfl)
  have hflux :
      normalFlux (Ω := domain)
        (fun x ↦ ‖(hu.of_le (show 1 ≤ 2 by omega)).completedGradient x‖ ^ 2 • (x - 0)) =
        normalFlux (Ω := domain) (fun x ↦ ‖∇ definingFunction x‖ ^ 2 • x) := by
    funext x
    by_cases hx : x ∈ frontier domain
    · rw [normalFlux_eq_inner _ hx, normalFlux_eq_inner _ hx,
        hcompletion (frontier_subset_closure hx), sub_zero]
    · simp only [normalFlux, dite_eq_right hx]
  dsimp only at h
  rw [hflux] at h
  have hadv : (∫ x in domain,
      inner ℝ (x - 0) (∇ definingFunction x) * laplacian definingFunction x) =
      24 * ∫ x in domain, ‖coordinates x‖ ^ 2 := by
    simp only [sub_zero, inner_gradient_definingFunction, laplacian_definingFunction]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hid := h.2.2.2
  rw [hadv] at hid
  norm_num at hid
  have hvalue := integral_coordinate_norm_sq_pos
  exact ⟨h.2.2.1, by linarith, by linarith⟩

end PDE.Examples.BoundaryFlux.Ellipsoid
