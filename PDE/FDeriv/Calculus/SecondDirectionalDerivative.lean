/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SecondDirectionalDerivative
public import PDE.FDeriv.Calculus

/-!
# Directional curvature in coordinates

At a `C²` point, the second derivative along a line is the Hessian contracted against
the direction twice. Expanding that bilinear expression in the standard Euclidean basis
connects the factored maximum-principle operator to the usual matrix coefficients.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

variable {n : ℕ}

/-- Coordinate expansion of the second derivative in an arbitrary Euclidean direction.
The regularity is local to the evaluation point. -/
theorem secondDirectionalDerivative_eq_sum
    {f : ℝ^n → ℝ} {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x) (v : ℝ^n) :
    secondDirectionalDerivative f x v =
      ∑ i : Fin n, ∑ j : Fin n, v i * v j * (∂[i] (∂[j] f)) x := by
  have hv : v = ∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  rw [secondDirectionalDerivative_eq_fderiv hf]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← mul_assoc, ← secondPartialDeriv_eq_fderiv _ _ hd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Summing directional curvatures contracts the Hessian with the matrix
`aᵢⱼ = ∑ₖ σₖᵢ σₖⱼ`. This identity is pointwise and differentiates no coefficient. -/
theorem sum_secondDirectionalDerivative_eq_sum
    {ι : Type*} [Fintype ι] (σ : ι → ℝ^n)
    {f : ℝ^n → ℝ} {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x) :
    ∑ k, secondDirectionalDerivative f x (σ k) =
      ∑ i : Fin n, ∑ j : Fin n,
        (∑ k, σ k i * σ k j) * (∂[i] (∂[j] f)) x := by
  simp only [secondDirectionalDerivative_eq_sum hf, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

end PDE.Analysis
