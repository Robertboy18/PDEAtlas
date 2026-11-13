/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AffinePullback
public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixOperator

/-!
# Scaling the classical matrix operator

Translation and dilation preserve the principal matrix and scale the drift by
the radius and the potential by its square. The identities use the
coordinate operator and do not differentiate coefficients.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum

variable {n : ℕ}

/-- Pulling back by `x ↦ z + r • x` scales the operator residual by `r²`. -/
theorem matrixOperator_comp_const_add_smul
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (u : ℝ^n → ℝ) (z x : ℝ^n) (r : ℝ) :
    matrixOperator (fun y ↦ a (z + r • y)) (fun y ↦ r • b (z + r • y))
      (fun y ↦ r ^ 2 * c (z + r • y)) (fun y ↦ u (z + r • y)) x =
        r ^ 2 * matrixOperator a b c u (z + r • x) := by
  simp only [matrixOperator_apply, secondPartialDeriv_comp_const_add_smul,
    fderiv_comp_const_add_smul, smul_apply, map_smul, smul_eq_mul]
  simp only [mul_left_comm _ (r ^ 2), ← Finset.mul_sum]
  ring

end EllipticHarnack
