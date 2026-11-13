/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Determinant
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Local inversion from a coordinate Jacobian

A nonzero coordinate determinant identifies the derivative with a continuous
linear equivalence. Mathlib's inverse function theorem then gives a local
homeomorphism whose inverse has the same positive differentiability order.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

/-- A regular Euclidean map with nonzero Jacobian determinant is locally invertible,
with an inverse of the same differentiability order. -/
theorem exists_openPartialHomeomorph_of_det_jacobianMatrix_ne_zero
    {n : ℕ} {k : WithTop ℕ∞} {f : ℝ^n → ℝ^n} {x : ℝ^n}
    (hf : ContDiffAt ℝ k f x) (hk : k ≠ 0)
    (hdet : (jacobianMatrix f x).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℝ^n ℝ^n, (e : ℝ^n → ℝ^n) = f ∧
      x ∈ e.source ∧ ContDiffAt ℝ k e.symm (f x) := by
  have hd := hf.differentiableAt hk
  have hunit : IsUnit (LinearMap.det (fderiv ℝ f x).toLinearMap) := by
    apply isUnit_iff_ne_zero.mpr
    rwa [det_jacobianMatrix hd] at hdet
  let D : ℝ^n ≃L[ℝ] ℝ^n :=
    (LinearMap.equivOfIsUnitDet hunit).toContinuousLinearEquiv
  have hD : (D : ℝ^n →L[ℝ] ℝ^n) = fderiv ℝ f x := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : ℝ^n →ₗ[ℝ] ℝ^n ↦ L v) (LinearMap.coe_equivOfIsUnitDet hunit)
  have hfd : HasFDerivAt f (D : ℝ^n →L[ℝ] ℝ^n) x := hD.symm ▸ hd.hasFDerivAt
  exact ⟨hf.toOpenPartialHomeomorph f hfd hk, rfl,
    hf.mem_toOpenPartialHomeomorph_source hfd hk, hf.to_localInverse hfd hk⟩

end PDE.Analysis
