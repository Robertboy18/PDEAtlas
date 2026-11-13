/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators
import PDE.FDeriv.SpaceTime

/-!
# Spatial slices and gradient fields for incompressible flow

Fixed-time velocity slices `velocitySlice`, the classical spatial velocity gradient
`spatialVelocityGradient`, the matrix divergence, and the fields `SpatialGradientField` that
represent weak spatial gradients. At a point where a field is differentiable its spatial
divergence is the divergence of the slice, and where a scalar field is `C²` its spatial
Laplacian is the Laplacian of the slice. These objects are shared by Euler and Navier–Stokes.

The velocity gradient is the matrix behind the local decomposition of an incompressible flow
into translation, rotation and deformation in Majda and Bertozzi, Section 1.4.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1, Section 1.4.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

namespace IncompressibleFlow

open EuclideanSpace

set_option linter.missingDocs true

/-- Euclidean space of real `n × n` spatial matrices, indexed by
component/derivative pairs `(i,j)`. -/
abbrev SpatialMatrix (n : ℕ) :=
  EuclideanSpace ℝ (Fin n × Fin n)

/-- Outer product `a ⊗ b`, represented as a spatial matrix with entry
`(i,j) = aᵢ bⱼ`. -/
noncomputable def spatialOuterProduct {n : ℕ}
    (a b : ℝ^n) : SpatialMatrix n :=
  WithLp.toLp 2 fun ij ↦ a ij.1 * b ij.2

/-- Coordinate formula for the spatial outer product. -/
@[simp]
theorem spatialOuterProduct_apply {n : ℕ}
    (a b : ℝ^n) (i j : Fin n) :
    spatialOuterProduct a b (i, j) = a i * b j := by
  simp [spatialOuterProduct, PiLp.toLp_apply]

/-- An outer product with zero in the first factor is zero. -/
@[simp]
theorem spatialOuterProduct_zero_left {n : ℕ} (b : ℝ^n) :
    spatialOuterProduct (0 : ℝ^n) b = 0 := by
  ext ⟨i, j⟩
  simp

/-- An outer product with zero in the second factor is zero. -/
@[simp]
theorem spatialOuterProduct_zero_right {n : ℕ} (a : ℝ^n) :
    spatialOuterProduct a (0 : ℝ^n) = 0 := by
  ext ⟨i, j⟩
  simp

/-- The norm of an outer product is the product of the norms of its factors. -/
theorem norm_spatialOuterProduct {n : ℕ} (a b : ℝ^n) :
    ‖spatialOuterProduct a b‖ = ‖a‖ * ‖b‖ := by
  have h : ‖spatialOuterProduct a b‖ ^ 2 = (‖a‖ * ‖b‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_mul_sum]
    simp [mul_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- The outer product of a vector with itself depends continuously on the vector. -/
theorem continuous_spatialOuterProduct_self {n : ℕ} :
    Continuous fun a : ℝ^n ↦ spatialOuterProduct a a :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun ij ↦
    (EuclideanSpace.proj ij.1).continuous.mul (EuclideanSpace.proj ij.2).continuous)

/-- Spatial velocity slice `x ↦ u(t,x)`. -/
def velocitySlice {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) : ℝ^n → ℝ^n :=
  fun x ↦ u (PDE.Common.timeSpaceCons t x)

/-- Divergence of a spatial slice agrees with spacetime spatial divergence when the field is
differentiable at the evaluation point. -/
theorem spatialFieldDivergence_velocitySlice {n : ℕ}
    {u : ℝ^(n + 1) → ℝ^n} (t : ℝ) (x : ℝ^n)
    (hu : DifferentiableAt ℝ u (PDE.Common.timeSpaceCons t x)) :
    spatialFieldDivergence (velocitySlice u t) x =
      spatialDivergence n u (PDE.Common.timeSpaceCons t x) := by
  unfold spatialFieldDivergence spatialDivergence velocitySlice
  apply Finset.sum_congr rfl
  intro i _hi
  exact PDE.partialDeriv_timeSpaceCons_spatial i (fun y ↦ u y i) t x
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hu)

/-- At a point where a scalar spacetime field is `C²`, its spatial Laplacian is the ordinary
Laplacian of the fixed-time slice. -/
theorem spatialLaplacian_timeSpaceCons_of_contDiffAt {n : ℕ} {f : ℝ^(n + 1) → ℝ} {t : ℝ}
    {x : ℝ^n} (hf : ContDiffAt ℝ 2 f (PDE.Common.timeSpaceCons t x)) :
    spatialLaplacian n f (PDE.Common.timeSpaceCons t x) =
      PDE.laplacian (fun y ↦ f (PDE.Common.timeSpaceCons t y)) x := by
  unfold spatialLaplacian PDE.laplacian
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hcont : Continuous (PDE.Common.timeSpaceCons (n := n) t) :=
    (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 0)).continuous
  have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f (PDE.Common.timeSpaceCons t y) :=
    hcont.continuousAt.eventually (hf.eventually (by simp))
  have hinner : (fun y ↦ PDE.partialDeriv i (fun w ↦ f (PDE.Common.timeSpaceCons t w)) y)
      =ᶠ[nhds x] fun y ↦ PDE.partialDeriv i.succ f (PDE.Common.timeSpaceCons t y) := by
    filter_upwards [hev] with y hy
    exact PDE.partialDeriv_timeSpaceCons_spatial i f t y (hy.differentiableAt (by simp))
  have hd : DifferentiableAt ℝ (PDE.partialDeriv i.succ f) (PDE.Common.timeSpaceCons t x) := by
    have h1 : ContDiffAt ℝ 1 (fun z ↦ fderiv ℝ f z (EuclideanSpace.single i.succ 1))
        (PDE.Common.timeSpaceCons t x) :=
      (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    exact h1.differentiableAt (by simp)
  change PDE.partialDeriv i.succ (PDE.partialDeriv i.succ f) (PDE.Common.timeSpaceCons t x) =
    PDE.partialDeriv i (fun y ↦ PDE.partialDeriv i (fun w ↦ f (PDE.Common.timeSpaceCons t w)) y) x
  rw [← PDE.partialDeriv_timeSpaceCons_spatial i (PDE.partialDeriv i.succ f) t x hd]
  change fderiv ℝ (fun y ↦ PDE.partialDeriv i.succ f (PDE.Common.timeSpaceCons t y)) x _ =
    fderiv ℝ (fun y ↦ PDE.partialDeriv i (fun w ↦ f (PDE.Common.timeSpaceCons t w)) y) x _
  rw [hinner.fderiv_eq]

/-- Classical spatial velocity gradient `∇u`, with entry `(i,j) = ∂ⱼuᵢ`. -/
noncomputable def spatialVelocityGradient (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    SpatialMatrix n :=
  WithLp.toLp 2 fun ij ↦
    (∂[ij.2.succ] (fun y ↦ u y ij.1)) x

/-- Coordinate formula for the classical spatial velocity gradient. -/
@[simp]
theorem spatialVelocityGradient_apply (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (i j : Fin n) :
    spatialVelocityGradient n u x (i, j) =
      (∂[j.succ] (fun y ↦ u y i)) x := by
  simp [spatialVelocityGradient, PiLp.toLp_apply]

/-- Spatial divergence of a spacetime matrix field, with
`(div A)ᵢ = ∑ⱼ ∂ⱼ Aᵢⱼ`. -/
noncomputable def spatialMatrixDivergence {n : ℕ}
    (A : ℝ^(n + 1) → SpatialMatrix n) (x : ℝ^(n + 1)) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    ∑ j : Fin n, (∂[j.succ] (fun y ↦ A y (i, j))) x

/-- Component formula for the spatial divergence of a matrix field. -/
@[simp]
theorem spatialMatrixDivergence_apply {n : ℕ}
    (A : ℝ^(n + 1) → SpatialMatrix n) (x : ℝ^(n + 1))
    (i : Fin n) :
    spatialMatrixDivergence A x i =
      ∑ j : Fin n, (∂[j.succ] (fun y ↦ A y (i, j))) x := by
  simp [spatialMatrixDivergence, PiLp.toLp_apply]

/-- Classical spatial gradient tensor at time `t`, indexed by component/derivative pairs
`(i,j)`. -/
noncomputable def classicalVelocityGradientSlice {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) :
    ℝ^n → SpatialMatrix n :=
  fun x ↦ spatialVelocityGradient n u (PDE.Common.timeSpaceCons t x)

/-- A spacetime field representing the distributional spatial gradient of velocity.
Component `(i,j)` represents `∂ⱼuᵢ`. -/
def SpatialGradientField (n : ℕ) :=
  ℝ^(n + 1) → SpatialMatrix n

/-- Spatial slice of a proposed weak-gradient field. -/
def spatialGradientSlice {n : ℕ}
    (Du : SpatialGradientField n) (t : ℝ) :
    ℝ^n → SpatialMatrix n :=
  fun x ↦ Du (PDE.Common.timeSpaceCons t x)

end IncompressibleFlow
