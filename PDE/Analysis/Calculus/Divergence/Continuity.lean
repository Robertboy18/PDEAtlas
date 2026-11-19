/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Divergence

/-!
# Continuity of the classical divergence
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
