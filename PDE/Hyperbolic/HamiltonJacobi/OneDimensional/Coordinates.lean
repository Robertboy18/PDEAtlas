/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.InitialValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Scalar coordinate transport for Hamilton–Jacobi comparison

The scalar library stores `(t, x)` in `ℝ^2`, with time at coordinate
zero. The general comparison theorem uses `(x, t) : E × ℝ`. A continuous
linear equivalence transports scalar solutions, slab regularity, and initial
traces to the general predicates with `E = ℝ`.

The scalar predicates test against every function differentiable at contact.
The general predicates require only locally `C¹` tests. A locally `C¹` test
remains differentiable under the coordinate change, so each scalar solution
satisfies the general predicate, and scalar comparison follows from the
general theorem.
-/

open scoped Gradient

@[expose] public section

open PDE (partialDeriv)

noncomputable section

namespace HamiltonJacobi1D

open PDE.Common Set
open scoped Topology

private theorem scalarSpaceTimeEquiv_time_direction :
    scalarSpaceTimeEquiv (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = (0, 1) := by
  simp

private theorem scalarSpaceTimeEquiv_space_direction :
    scalarSpaceTimeEquiv (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = (1, 0) := by
  simp

private theorem partialDeriv_time_comp_scalarSpaceTimeEquiv {φ : ℝ × ℝ → ℝ} {z : ℝ^2}
    (hφ : DifferentiableAt ℝ φ (scalarSpaceTimeEquiv z)) :
    (∂[0] (φ ∘ scalarSpaceTimeEquiv)) z = fderiv ℝ φ (scalarSpaceTimeEquiv z) (0, 1) := by
  rw [partialDeriv,
    (hφ.hasFDerivAt.comp z scalarSpaceTimeEquiv.toContinuousLinearMap.hasFDerivAt).fderiv]
  change fderiv ℝ φ (scalarSpaceTimeEquiv z)
    (scalarSpaceTimeEquiv (EuclideanSpace.single 0 (1 : ℝ))) = _
  rw [scalarSpaceTimeEquiv_time_direction]

private theorem partialDeriv_space_comp_scalarSpaceTimeEquiv {φ : ℝ × ℝ → ℝ} {z : ℝ^2}
    (hφ : DifferentiableAt ℝ φ (scalarSpaceTimeEquiv z)) :
    (∂[1] (φ ∘ scalarSpaceTimeEquiv)) z = ∇ (fun x ↦ φ (x, z 0)) (z 1) := by
  have hslice : HasDerivAt (fun x ↦ φ (x, z 0))
      (fderiv ℝ φ (scalarSpaceTimeEquiv z) (1, 0)) (z 1) := hφ.hasFDerivAt.comp_hasDerivAt (z 1)
      ((hasDerivAt_id (z 1)).prodMk (hasDerivAt_const (z 1) (z 0)))
  rw [gradient_eq_deriv', hslice.deriv, partialDeriv,
    (hφ.hasFDerivAt.comp z scalarSpaceTimeEquiv.toContinuousLinearMap.hasFDerivAt).fderiv]
  change fderiv ℝ φ (scalarSpaceTimeEquiv z)
    (scalarSpaceTimeEquiv (EuclideanSpace.single 1 (1 : ℝ))) = _
  rw [scalarSpaceTimeEquiv_space_direction]

/-- A scalar subsolution tested against all differentiable contacts
satisfies the local `C¹` test condition in product coordinates. -/
theorem IsSpatialDifferentiableTestSubsolution.to_product {H : ℝ → ℝ → ℝ} {U : Set ℝ^2}
    {u : ℝ^2 → ℝ} (hu : IsSpatialDifferentiableTestSubsolution H U u) :
    HamiltonJacobi.IsSpatialViscositySubsolution H
      (scalarSpaceTimeEquiv.symm ⁻¹' U) (u ∘ scalarSpaceTimeEquiv.symm) := by
  refine ⟨hu.1.preimage scalarSpaceTimeEquiv.symm.continuous, fun z hz φ hφ hmax ↦ ?_⟩
  have hz' : scalarSpaceTimeEquiv.symm z ∈ U := hz
  have hφ' : DifferentiableAt ℝ φ (scalarSpaceTimeEquiv (scalarSpaceTimeEquiv.symm z)) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hφ.differentiableAt_one
  have hmax' : IsLocalMaxOn (fun y ↦ (u ∘ scalarSpaceTimeEquiv.symm) y - φ y)
      (scalarSpaceTimeEquiv.symm ⁻¹' U) (scalarSpaceTimeEquiv (scalarSpaceTimeEquiv.symm z)) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hmax
  have h := hu.2 _ hz' _ (hφ'.comp _ scalarSpaceTimeEquiv.differentiableAt) (by
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      hmax'.comp_continuousOn (g := scalarSpaceTimeEquiv) (fun y hy ↦ by
        simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hy)
        scalarSpaceTimeEquiv.continuous.continuousOn hz')
  rw [partialDeriv_time_comp_scalarSpaceTimeEquiv hφ',
    partialDeriv_space_comp_scalarSpaceTimeEquiv hφ'] at h
  simpa using h

/-- A scalar supersolution tested against all differentiable contacts
satisfies the local `C¹` test condition in product coordinates. -/
theorem IsSpatialDifferentiableTestSupersolution.to_product {H : ℝ → ℝ → ℝ} {U : Set ℝ^2}
    {u : ℝ^2 → ℝ} (hu : IsSpatialDifferentiableTestSupersolution H U u) :
    HamiltonJacobi.IsSpatialViscositySupersolution H
      (scalarSpaceTimeEquiv.symm ⁻¹' U) (u ∘ scalarSpaceTimeEquiv.symm) := by
  refine ⟨hu.1.preimage scalarSpaceTimeEquiv.symm.continuous, fun z hz φ hφ hmin ↦ ?_⟩
  have hz' : scalarSpaceTimeEquiv.symm z ∈ U := hz
  have hφ' : DifferentiableAt ℝ φ (scalarSpaceTimeEquiv (scalarSpaceTimeEquiv.symm z)) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hφ.differentiableAt_one
  have hmin' : IsLocalMinOn (fun y ↦ (u ∘ scalarSpaceTimeEquiv.symm) y - φ y)
      (scalarSpaceTimeEquiv.symm ⁻¹' U) (scalarSpaceTimeEquiv (scalarSpaceTimeEquiv.symm z)) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hmin
  have h := hu.2 _ hz' _ (hφ'.comp _ scalarSpaceTimeEquiv.differentiableAt) (by
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      hmin'.comp_continuousOn (g := scalarSpaceTimeEquiv) (fun y hy ↦ by
        simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hy)
        scalarSpaceTimeEquiv.continuous.continuousOn hz')
  rw [partialDeriv_time_comp_scalarSpaceTimeEquiv hφ',
    partialDeriv_space_comp_scalarSpaceTimeEquiv hφ'] at h
  simpa using h

/-- Both scalar differentiable-contact inequalities imply the corresponding
local `C¹` inequalities in product coordinates. -/
theorem IsSpatialDifferentiableTestSolution.to_product {H : ℝ → ℝ → ℝ} {U : Set ℝ^2} {u : ℝ^2 → ℝ}
    (hu : IsSpatialDifferentiableTestSolution H U u) :
    HamiltonJacobi.IsSpatialViscositySolution H
      (scalarSpaceTimeEquiv.symm ⁻¹' U) (u ∘ scalarSpaceTimeEquiv.symm) :=
  ⟨hu.1.to_product, hu.2.to_product⟩

private theorem preimage_positiveTimeDomain :
    scalarSpaceTimeEquiv.symm ⁻¹' PDE.Common.positiveTimeDomain =
      HamiltonJacobi.positiveTimeDomain (E := ℝ) := by
  ext z
  simp [PDE.Common.positiveTimeDomain, HamiltonJacobi.positiveTimeDomain]

/-- Upper initial traces, slab regularity, and the scalar equation imply
the initial-value subsolution condition with local `C¹` tests. -/
theorem IsDifferentiableTestInitialSubsolution.to_product {H : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsDifferentiableTestInitialSubsolution H g u) :
    HamiltonJacobi.IsViscosityInitialSubsolution H g (u ∘ scalarSpaceTimeEquiv.symm) :=
  ⟨hu.1, by simpa only [preimage_positiveTimeDomain] using hu.2.1.to_product, fun x ↦ by
    simpa only [Function.comp_apply, scalarSpaceTimeEquiv_symm_apply] using hu.2.2 x⟩

/-- Lower initial traces, slab regularity, and the scalar equation imply
the initial-value supersolution condition with local `C¹` tests. -/
theorem IsDifferentiableTestInitialSupersolution.to_product {H : ℝ → ℝ → ℝ} {g : ℝ → ℝ}
    {u : ℝ^2 → ℝ} (hu : IsDifferentiableTestInitialSupersolution H g u) :
    HamiltonJacobi.IsViscosityInitialSupersolution H g (u ∘ scalarSpaceTimeEquiv.symm) :=
  ⟨hu.1, by simpa only [preimage_positiveTimeDomain] using hu.2.1.to_product, fun x ↦ by
    simpa only [Function.comp_apply, scalarSpaceTimeEquiv_symm_apply] using hu.2.2 x⟩

/-- A scalar initial-value solution with differentiable-contact tests gives
a solution with local `C¹` tests after the coordinate change. -/
theorem IsDifferentiableTestInitialSolution.to_product {H : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsDifferentiableTestInitialSolution H g u) :
    HamiltonJacobi.IsViscosityInitialSolution H g (u ∘ scalarSpaceTimeEquiv.symm) :=
  HamiltonJacobi.isViscosityInitialSolution_iff_sub_and_super.mpr
    ⟨hu.subsolution.to_product, hu.supersolution.to_product⟩

end HamiltonJacobi1D
