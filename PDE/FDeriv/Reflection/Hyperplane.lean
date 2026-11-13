/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Reflection.Hyperplane
public import PDE.FDeriv.Laplacian.Isometry

/-!
# Differential calculus for a translated hyperplane reflection

The derivative is the original linear orthogonal reflection. In particular,
the normal derivative changes sign and the Laplacian is unchanged.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reflection across a translated hyperplane is smooth. -/
theorem contDiff_reflectHyperplane (e : E) (a : ℝ) (k : ℕ∞ω) :
    ContDiff ℝ k (reflectHyperplane e a) :=
  (ℝ ∙ e)ᗮ.reflection.contDiff.add contDiff_const

/-- The derivative of the translated reflection is the original linear reflection. -/
theorem hasFDerivAt_reflectHyperplane (e : E) (a : ℝ) (x : E) :
    HasFDerivAt (reflectHyperplane e a)
      (ℝ ∙ e)ᗮ.reflection.toContinuousLinearEquiv.toContinuousLinearMap x := by
  exact (ℝ ∙ e)ᗮ.reflection.toContinuousLinearEquiv.hasFDerivAt.add_const _

/-- Pullback by a hyperplane reflection reverses the derivative in its normal direction. -/
theorem fderiv_comp_reflectHyperplane_normal {u : E → ℝ} (e : E) (a : ℝ) (x : E)
    (hu : DifferentiableAt ℝ u (reflectHyperplane e a x)) :
    fderiv ℝ (u ∘ reflectHyperplane e a) x e =
      -fderiv ℝ u (reflectHyperplane e a x) e := by
  rw [(hu.hasFDerivAt.comp x (hasFDerivAt_reflectHyperplane e a x)).fderiv]
  simp [Submodule.reflection_orthogonalComplement_singleton_eq_neg]

/-- Reflection preserves the native coordinate Laplacian at every `C²` point. -/
theorem laplacian_comp_reflectHyperplane_at {n : ℕ} {u : ℝ^n → ℝ}
    (e : ℝ^n) (a : ℝ) (x : ℝ^n) (hu : ContDiffAt ℝ 2 u (reflectHyperplane e a x)) :
    laplacian (u ∘ reflectHyperplane e a) x =
      laplacian u (reflectHyperplane e a x) :=
  laplacian_comp_isometry_add_at (ℝ ∙ e)ᗮ.reflection ((2 * a) • e) hu

end PDE.Analysis
