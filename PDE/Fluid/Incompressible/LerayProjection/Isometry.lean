/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Invariance of the whole-space Leray projection under linear isometries

A linear isometry `h` of `ℝ^n` acts on whole-space `L²` vector fields by `f ↦ h ∘ f ∘ h⁻¹`
(`l2Isometry h`), a linear isometry equivalence. It maps the gradient of a test function `φ` to the
gradient of `φ ∘ h⁻¹`, so it preserves the divergence-free subspace, and uniqueness of the
orthogonal projection shows that the Leray projection commutes with it
(`lerayProjection_l2Isometry`). Rotations and reflections are the cases used for symmetric flows.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped RealInnerProductSpace Distributions Sobolev

namespace IncompressibleFlow

set_option linter.missingDocs true

variable {n : ℕ}

local notation "μ₀" => domainMeasure n Set.univ

/-- Pull back along a measure-preserving map, then apply a linear map pointwise:
`f ↦ L ∘ f ∘ M`. -/
def l2Conj (L : ℝ^n →L[ℝ] ℝ^n) (M : ℝ^n → ℝ^n) (hM : MeasurePreserving M μ₀ μ₀) :
    WholeSpaceL2 n →L[ℝ] WholeSpaceL2 n :=
  (L.compLpL 2 μ₀).comp (Lp.compMeasurePreservingₗᵢ ℝ M hM).toContinuousLinearMap

/-- Evaluation of `l2Conj`. -/
theorem coeFn_l2Conj (L : ℝ^n →L[ℝ] ℝ^n) (M : ℝ^n → ℝ^n)
    (hM : MeasurePreserving M μ₀ μ₀) (f : WholeSpaceL2 n) :
    l2Conj L M hM f =ᵐ[volume] fun x ↦ L (f (M x)) := by
  have h1 := ContinuousLinearMap.coeFn_compLp' L (Lp.compMeasurePreserving M hM f)
  have h2 := Lp.coeFn_compMeasurePreserving f hM
  simp only [domainMeasure, Measure.restrict_univ] at h1 h2
  filter_upwards [h1, h2] with x hx1 hx2
  change (L.compLp (Lp.compMeasurePreserving M hM f)) x = _
  rw [hx1, hx2]
  rfl

/-- A linear isometry preserves the whole-space domain measure. -/
theorem measurePreserving_linearIsometryEquiv_domain (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) :
    MeasurePreserving h μ₀ μ₀ := by
  simpa only [domainMeasure, Measure.restrict_univ] using h.measurePreserving

/-- The action `f ↦ h ∘ f ∘ h⁻¹` of a linear isometry of `ℝ^n` on whole-space `L²` fields. -/
def l2IsometryMap (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) : WholeSpaceL2 n →L[ℝ] WholeSpaceL2 n :=
  l2Conj h.toContinuousLinearEquiv.toContinuousLinearMap h.symm
    (measurePreserving_linearIsometryEquiv_domain h.symm)

/-- Evaluation of `l2IsometryMap`. -/
theorem l2IsometryMap_ae (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (f : WholeSpaceL2 n) :
    l2IsometryMap h f =ᵐ[volume] fun x ↦ h (f (h.symm x)) :=
  coeFn_l2Conj _ _ _ f

/-- The action of the inverse isometry is a right inverse. -/
theorem l2IsometryMap_l2IsometryMap_symm (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (f : WholeSpaceL2 n) :
    l2IsometryMap h (l2IsometryMap h.symm f) = f := by
  refine Lp.ext ?_
  change _ =ᵐ[volume.restrict Set.univ] _
  rw [Measure.restrict_univ]
  have h1 := l2IsometryMap_ae h (l2IsometryMap h.symm f)
  have h2 := (h.symm.measurePreserving.quasiMeasurePreserving).ae
    (l2IsometryMap_ae h.symm f)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]
  simp

/-- The isometry action preserves `L²` norms. -/
theorem norm_l2IsometryMap (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (f : WholeSpaceL2 n) :
    ‖l2IsometryMap h f‖ = ‖f‖ := by
  change ‖(h.toContinuousLinearEquiv.toContinuousLinearMap).compLp
    (Lp.compMeasurePreserving h.symm (measurePreserving_linearIsometryEquiv_domain h.symm) f)‖ = ‖f‖
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine (eLpNorm_congr_ae (ContinuousLinearMap.coeFn_compLp' _ _)).trans ?_
  refine (eLpNorm_congr_norm_ae
    (h.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
    (Lp.aestronglyMeasurable _) (Filter.Eventually.of_forall fun x ↦ h.norm_map _)).trans ?_
  have hM := measurePreserving_linearIsometryEquiv_domain h.symm
  rw [eLpNorm_congr_ae (Lp.coeFn_compMeasurePreserving f hM)]
  exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) hM

/-- The action `f ↦ h ∘ f ∘ h⁻¹` of a linear isometry of `ℝ^n` on whole-space `L²` fields, as a
linear isometry equivalence. -/
def l2Isometry (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) : WholeSpaceL2 n ≃ₗᵢ[ℝ] WholeSpaceL2 n where
  toLinearEquiv := LinearEquiv.ofLinearMap (l2IsometryMap h).toLinearMap
    (l2IsometryMap h.symm).toLinearMap
    (LinearMap.ext fun f ↦ l2IsometryMap_l2IsometryMap_symm h f)
    (LinearMap.ext fun f ↦ by simpa using l2IsometryMap_l2IsometryMap_symm h.symm f)
  norm_map' := norm_l2IsometryMap h

/-- The isometry action is `h ∘ f ∘ h⁻¹` almost everywhere. -/
theorem l2Isometry_ae (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (f : WholeSpaceL2 n) :
    l2Isometry h f =ᵐ[volume] fun x ↦ h (f (h.symm x)) :=
  l2IsometryMap_ae h f

/-- The inverse of the isometry action is the action of the inverse isometry. -/
theorem l2Isometry_symm_apply (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (f : WholeSpaceL2 n) :
    (l2Isometry h).symm f = l2Isometry h.symm f :=
  rfl

/-- The pullback `φ ∘ h⁻¹` of a test function by a linear isometry. -/
def isometryTest (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (φ : TestFunctionOn n Set.univ) : TestFunctionOn n Set.univ :=
  ⟨TestFunction.mk (fun x ↦ φ.1.toFun (h.symm x)) (φ.1.contDiff.comp h.symm.contDiff)
    (φ.1.hasCompactSupport.comp_homeomorph h.symm.toHomeomorph) (Set.subset_univ _),
    Set.subset_univ _⟩

/-- The isometry action maps the gradient of a test function to the gradient of its pullback. -/
theorem l2Isometry_testGradient (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (φ : TestFunctionOn n Set.univ) :
    l2Isometry h (l2TestGradient φ) = l2TestGradient (isometryTest h φ) := by
  refine Lp.ext ?_
  change _ =ᵐ[volume.restrict Set.univ] _
  rw [Measure.restrict_univ]
  have hg := l2TestGradient_apply_ae φ
  have hg' := l2TestGradient_apply_ae (isometryTest h φ)
  simp only [domainMeasure, Measure.restrict_univ] at hg hg'
  filter_upwards [l2Isometry_ae h (l2TestGradient φ),
    h.symm.measurePreserving.quasiMeasurePreserving.ae hg, hg'] with x hx hy hz
  rw [hx]
  ext i
  rw [hz i]
  have hd : DifferentiableAt ℝ φ.1.toFun (h.symm x) :=
    (φ.1.contDiff.differentiable (by simp)) _
  have hcomp : HasFDerivAt (fun y ↦ φ.1.toFun (h.symm y))
      ((fderiv ℝ φ.1.toFun (h.symm x)).comp
        h.symm.toContinuousLinearEquiv.toContinuousLinearMap) x :=
    hd.hasFDerivAt.comp x h.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  change (h (l2TestGradient φ (h.symm x))) i =
    fderiv ℝ (fun y ↦ φ.1.toFun (h.symm y)) x (EuclideanSpace.single i 1)
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, PDE.fderiv_apply_eq_sum_smul_partialDeriv]
  have hcoord (w : ℝ^n) : (h w) i = ⟪h.symm (EuclideanSpace.single i 1), w⟫ := by
    rw [← h.inner_map_map, LinearIsometryEquiv.apply_symm_apply,
      EuclideanSpace.inner_single_left]
    simp
  rw [hcoord, PiLp.inner_apply]
  simp only [smul_eq_mul, hy, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm]
  rfl

/-- The isometry action preserves the divergence-free subspace. -/
theorem l2Isometry_mem_solenoidal (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) {v : WholeSpaceL2 n}
    (hv : v ∈ l2Solenoidal n) : l2Isometry h v ∈ l2Solenoidal n := by
  rw [mem_l2Solenoidal_iff_inner] at hv ⊢
  intro φ
  rw [LinearIsometryEquiv.inner_map_eq_flip, l2Isometry_symm_apply, l2Isometry_testGradient]
  exact hv _

/-- The Leray projection commutes with the action of linear isometries of `ℝ^n`. -/
theorem lerayProjection_l2Isometry (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (v : WholeSpaceL2 n) :
    lerayProjection n (l2Isometry h v) = l2Isometry h (lerayProjection n v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (l2Isometry_mem_solenoidal h (lerayProjection_mem n v)) fun w hw ↦ ?_
  rw [← map_sub, LinearIsometryEquiv.inner_map_eq_flip, l2Isometry_symm_apply]
  exact Submodule.starProjection_inner_eq_zero v _ (l2Isometry_mem_solenoidal h.symm hw)

end IncompressibleFlow
