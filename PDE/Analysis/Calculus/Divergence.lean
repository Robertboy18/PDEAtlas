/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus

/-!
# Product and chain rules for divergence

The conservative fluxes `a F` and `F ∘ u` have divergences
`Da(F) + a div F` and `Du(F'(u))`, respectively. These formulas connect the
coordinate definition of divergence with the Fréchet derivative of a scalar field.
Only differentiability at the evaluation point is needed.

The global notation `∇· F` is the function `divergence F`, with its scalar components
differentiated by the total Fréchet derivative. The hypotheses below give it its
classical meaning.

The chain rule takes an ordinary `HasDerivAt` hypothesis for the flux curve,
so its components can be computed separately, for instance with the checked CAS,
before the rule is applied to an abstract differentiable field.
-/

@[expose] public section

namespace PDE.Analysis

variable {n : ℕ}

/-- Multiplying a vector field by a scalar field adds the directional derivative
of the scalar to its weighted divergence. -/
theorem divergence_smul {a : ℝ^n → ℝ} {F : ℝ^n → ℝ^n} {x : ℝ^n}
    (ha : DifferentiableAt ℝ a x) (hF : DifferentiableAt ℝ F x) :
    ∇· (fun y ↦ a y • F y) x =
      fderiv ℝ a x (F x) + a x * ∇· F x := by
  have hFi (i : Fin n) : DifferentiableAt ℝ (fun y ↦ F y i) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).differentiableAt.comp x hF
  rw [fderiv_apply_eq_sum_partialDeriv_mul]
  simp only [divergence, PiLp.smul_apply, smul_eq_mul,
    partialDeriv_mul ha (hFi _), Finset.sum_add_distrib, Finset.mul_sum]

/-- The divergence of a flux depending on one scalar field is the derivative of
that field in the direction of the flux derivative. The flux derivative is given
by a `HasDerivAt` hypothesis at `u x` alone, so no regularity away from `u x` is
required. -/
theorem divergence_comp_of_hasDerivAt
    {u : ℝ^n → ℝ} {F : ℝ → ℝ^n} {F' : ℝ^n} {x : ℝ^n}
    (hF : HasDerivAt F F' (u x)) (hu : DifferentiableAt ℝ u x) :
    ∇· (fun y ↦ F (u y)) x = fderiv ℝ u x F' := by
  rw [divergence, fderiv_apply_eq_sum_partialDeriv_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hFi : HasDerivAt (fun s ↦ F s i) (F' i) (u x) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).hasFDerivAt.comp_hasDerivAt
      (u x) hF
  rw [partialDeriv_comp_real i hFi.differentiableAt hu, hFi.deriv]

end PDE.Analysis
