/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Coordinate derivatives under amplitudes and dilations

For `c, L ∈ ℝ` the function `y ↦ c f(L y)` has the coordinate derivatives `c L ∂ᵢf(L x)`, and it
is `C^n` when `f` is.

## Main results

* `partialDeriv_const_mul_comp_smul`: `∂ᵢ(c f(L ·))(x) = c L ∂ᵢf(L x)`.
* `contDiff_const_mul_comp_smul`: `y ↦ c f(L y)` is `C^n` when `f` is.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace PDE

/-- A coordinate derivative of `y ↦ c f(L y)` is `c L ∂ᵢf(L x)`. -/
theorem partialDeriv_const_mul_comp_smul {n : ℕ} (i : Fin n) {f : ℝ^n → ℝ} (c L : ℝ)
    {x : ℝ^n} (hf : DifferentiableAt ℝ f (L • x)) :
    (∂[i] (fun y ↦ c * f (L • y))) x = c * L * (∂[i] f) (L • x) := by
  have h1 : HasFDerivAt (fun y : ℝ^n ↦ L • y) (L • ContinuousLinearMap.id ℝ (ℝ^n)) x :=
    (hasFDerivAt_id x).const_smul L
  have h2 := (hf.hasFDerivAt.comp x h1).const_mul c
  simp only [PDE.partialDeriv]
  rw [show (fun y ↦ c * f (L • y)) = (fun y ↦ c * (f ∘ fun y : ℝ^n ↦ L • y) y) from rfl,
    h2.fderiv]
  simp [smul_eq_mul]
  ring

/-- Iterated coordinate derivatives of a dilation `z ↦ h (c • z)` acquire the factor
`c ^ α.length`. -/
theorem iteratedPartialDeriv_comp_const_smul {n : ℕ} (α : List (Fin n)) {h : ℝ^n → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (c : ℝ) (x : ℝ^n) :
    iteratedPartialDeriv α (fun z ↦ h (c • z)) x =
      c ^ α.length * iteratedPartialDeriv α h (c • x) := by
  induction α generalizing x with
  | nil => simp [iteratedPartialDeriv]
  | cons i rest ih =>
    have hfun : (fun y ↦ iteratedPartialDeriv rest (fun z ↦ h (c • z)) y) =
        fun y ↦ c ^ rest.length * iteratedPartialDeriv rest h (c • y) := funext ih
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ iteratedPartialDeriv rest h y) :=
      contDiff_top_iteratedPartialDeriv hh rest
    simp only [iteratedPartialDeriv]
    rw [hfun, partialDeriv_const_mul_comp_smul i _ c
      ((hg.differentiable (by simp)).differentiableAt), List.length_cons, pow_succ]

/-- Amplitudes and dilations preserve `C^n`. -/
theorem contDiff_const_mul_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) (c a : ℝ) :
    ContDiff ℝ n (fun y ↦ c * f (a • y)) :=
  contDiff_const.mul (hf.comp (contDiff_const_smul a))

end PDE
