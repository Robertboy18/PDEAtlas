/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Calculus.Divergence

/-!
# Continuity of the classical divergence

A vector field `F` of class `C¹` on `ℝ^n` has a continuous divergence `∇· F`
(`ContDiff.continuous_divergence`): each term of the divergence is a coordinate of the continuous
derivative of `F`, applied to a vector of the standard basis.
-/

@[expose] public section

/-- A C¹ Euclidean vector field has continuous classical divergence. -/
theorem ContDiff.continuous_divergence {n : ℕ} {F : ℝ^n → ℝ^n}
    (hF : ContDiff ℝ 1 F) : Continuous (∇· F) := by
  apply continuous_finsetSum
  intro i _
  have hi := ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF).continuous_fderiv
    one_ne_zero
  exact hi.clm_apply (continuous_const (y := EuclideanSpace.single i 1))
