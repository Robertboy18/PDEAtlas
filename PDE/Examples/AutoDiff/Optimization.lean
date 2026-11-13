/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.AutoDiff.ResidualLoss
public import PDE.Elliptic.Classical.Laplace.Equation
public import CAS.ExactTactic

/-!
# Residual losses and gradient descent

The sampled residual loss of the Laplace equation on `ℝ^2`, built from the
Fréchet-derivative operators, vanishes for the zero field. For the
quadratic loss `(y - 3) ^ 2`, the gradient is `2 (y - 3)` (checked by `cas`), one
step of `gradientDescentStep` multiplies the displacement from `3` by `1 - 2 η`, and
`gradientDescent` after `k` steps multiplies it by `(1 - 2 η) ^ k`.
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace PDE.Examples.AutoDiff

/-- The sampled Laplace residual loss of the zero field at the points `(1, 2)` and
`(0, 1)`. -/
noncomputable def laplaceSampledLossExample : ℝ :=
  let u : ℝ^2 → ℝ := fun _ ↦ 0
  let x₁ : ℝ^2 :=
    WithLp.toLp 2 (fun i : Fin 2 ↦ if i = 0 then 1 else 2)
  let x₂ : ℝ^2 :=
    WithLp.toLp 2 (fun i : Fin 2 ↦ if i = 0 then 0 else 1)
  PDE.AutoDiff.ResidualLoss.sampledLoss (laplaceEquation 2) u [x₁, x₂]

/-- Every sampled term vanishes for the zero field. -/
theorem laplaceSampledLossExample_eq_zero :
    laplaceSampledLossExample = 0 := by
  apply (PDE.AutoDiff.ResidualLoss.sampledLoss_eq_zero_iff _ _ _).mpr
  intro x _
  simp [LinearPDE.residual, laplaceEquation, laplacian, partialDeriv]

/-- The gradient used by the optimizer is the classical derivative of this quadratic. -/
theorem gradient_quadratic (x : ℝ) :
    ∇ (fun y : ℝ ↦ (y - 3) ^ 2) x = 2 * (x - 3) := by
  have h : HasDerivAt (fun y : ℝ ↦ (y - 3) ^ 2) (2 * (x - 3)) x := by
    cas
  simpa using h.hasGradientAt.gradient

/-- One update contracts the displacement by the exact factor `1 - 2 * stepSize`. -/
theorem quadratic_step (x stepSize : ℝ) :
    PDE.AutoDiff.Optimization.gradientDescentStep
      (fun y : ℝ ↦ (y - 3) ^ 2) x stepSize - 3 =
      (1 - 2 * stepSize) * (x - 3) := by
  rw [PDE.AutoDiff.Optimization.gradientDescentStep, gradient_quadratic]
  simp only [smul_eq_mul]
  ring

/-- The implemented finite iteration has the expected closed form on a nonconstant loss. -/
theorem quadratic_iterations (initial stepSize : ℝ) (iterations : ℕ) :
    PDE.AutoDiff.ResidualLoss.gradientDescent
      (fun y : ℝ ↦ (y - 3) ^ 2) initial stepSize iterations - 3 =
      (1 - 2 * stepSize) ^ iterations * (initial - 3) := by
  induction iterations with
  | zero => simp [PDE.AutoDiff.ResidualLoss.gradientDescent]
  | succ iterations ih =>
      change PDE.AutoDiff.Optimization.gradientDescentStep _
        (PDE.AutoDiff.ResidualLoss.gradientDescent _ initial stepSize iterations) stepSize - 3 = _
      rw [quadratic_step, ih, pow_succ]
      ring

end PDE.Examples.AutoDiff
end
