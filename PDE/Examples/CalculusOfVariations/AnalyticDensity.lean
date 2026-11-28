/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A non-quadratic analytic density with two-sided Hessian bounds

## Motivation

Is there a real-analytic integrand on `ℝ^n`, other than a quadratic polynomial,
whose Hessian lies between two positive multiples of the identity?

## The idea

Start from the quadratic density `‖p‖² / 2` and add a bounded analytic term that
sees `p` through one linear functional: `F p = ‖p‖² / 2 + (1 - cos (ℓ p)) / 2` with `‖ℓ‖ ≤ 1`.
Its second derivative is `D²F(p)(ξ, η) = ⟪ξ, η⟫ + cos (ℓ p) * ℓ ξ * ℓ η / 2`. The second term is
at most `‖ξ‖ * ‖η‖ / 2` in absolute value, so `‖ξ‖² / 2 ≤ D²F(p)(ξ, ξ) ≤ 3 * ‖ξ‖² / 2`. The
cosine makes the Hessian depend on `p` as soon as `ℓ ≠ 0`. On `ℝ^n` the functional
`p ↦ ⟪e i, p⟫ = p i` of a basis vector has norm one, which gives an example in every dimension
`n ≥ 1`.

## Main results

* `cosineDensity` (construction, on every real inner product space and for every continuous
  linear functional `ℓ`): the density `‖p‖² / 2 + (1 - cos (ℓ p)) / 2`.
* `analyticOnNhd_cosineDensity` (all `ℓ`): the density is analytic on the whole space.
* `cosineDensity_hessian` (all `ℓ`): the formula for the second derivative.
* `cosineDensity_hessian_lower`, `cosineDensity_hessian_upper` (all `ℓ` with `‖ℓ‖ ≤ 1`):
  `‖ξ‖² / 2 ≤ D²F(p)(ξ, ξ)` and `‖D²F(p)‖ ≤ 3 / 2`.
* `cosineDensity_hessian_ne` (all `ℓ ≠ 0`): the Hessian is not constant.
* `exists_analytic_density` (one example on `ℝ^n` for every `n` and every coordinate `i`): the
  function `‖p‖² / 2 + (1 - cos (p i)) / 2` is analytic, satisfies both bounds, and has a
  Hessian that is not constant.

## Relations

* The two bounds have the form of the hypotheses `hbound` and `hpos` of the regularity
  theorems for gradient densities, for example
  `PDE.Elliptic.Regularity.Quasilinear.exists_smooth_solution_of_gradientDensity`, with
  `Λ = 3 / 2` and `θ = 1 / 2`.
* `PDE.Examples.GradientEnergy.signedDensity` is a density of the same kind on `ℝ^1`, with
  Hessian between `3 / 4` and `5 / 4`. The density here lives on every real inner product
  space.
* Smoothness of every order comes from Mathlib's `contDiff_norm_sq` and `Real.contDiff_cos`.
  Analyticity is `ContDiff.analyticOnNhd` at order `ω`.
* `PDE.Examples.CalculusOfVariations.exists_analytic_of_isLocalMinimizerOn_cosineDensity`
  applies the analyticity theorem for local minimizers to this density.

## What stays open

* The regularity theorems are applied to the density in
  `PDE.Examples.CalculusOfVariations.AnalyticMinimizer`, not in this file.
* The file proves that the Hessian is not constant. It does not prove that the density is not
  a polynomial of higher degree.

The computation is elementary and uses only Mathlib.
-/

@[expose] public noncomputable section

namespace PDE.Examples.CalculusOfVariations

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ℓ : E →L[ℝ] ℝ}

/-- The density `F p = ‖p‖² / 2 + (1 - cos (ℓ p)) / 2` on a real inner product space, for a
continuous linear functional `ℓ`. -/
def cosineDensity (ℓ : E →L[ℝ] ℝ) (p : E) : ℝ :=
  ‖p‖ ^ 2 / 2 + (1 - Real.cos (ℓ p)) / 2

/-- The density `cosineDensity ℓ` is continuously differentiable of every order `n`, the
analytic order `ω` included. -/
theorem contDiff_cosineDensity (ℓ : E →L[ℝ] ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (cosineDensity ℓ) :=
  ((contDiff_norm_sq ℝ).div_const 2).add ((contDiff_const.sub ℓ.contDiff.cos).div_const 2)

/-- The density `cosineDensity ℓ` is real-analytic on the whole space, for every continuous
linear functional `ℓ`. -/
theorem analyticOnNhd_cosineDensity (ℓ : E →L[ℝ] ℝ) : AnalyticOnNhd ℝ (cosineDensity ℓ) univ :=
  (contDiff_cosineDensity ℓ).analyticOnNhd

/-- The first derivative: `DF(p) ξ = ⟪p, ξ⟫ + sin (ℓ p) * ℓ ξ / 2`, written as the continuous
linear map `innerSL ℝ p + (sin (ℓ p) / 2) • ℓ`. -/
theorem hasFDerivAt_cosineDensity (ℓ : E →L[ℝ] ℝ) (p : E) :
    HasFDerivAt (cosineDensity ℓ) (innerSL ℝ p + (Real.sin (ℓ p) / 2) • ℓ) p := by
  have h1 : HasFDerivAt (fun q : E ↦ ‖q‖ ^ 2 / 2) (innerSL ℝ p) p := by
    simp only [div_eq_mul_inv]
    refine ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.mul_const (2⁻¹ : ℝ)).congr_fderiv ?_
    ext ξ
    simp
  have h2 : HasFDerivAt (fun q : E ↦ (1 - Real.cos (ℓ q)) / 2) ((Real.sin (ℓ p) / 2) • ℓ) p := by
    simp only [div_eq_mul_inv]
    refine (((ℓ.hasFDerivAt (x := p)).cos.const_sub 1).mul_const (2⁻¹ : ℝ)).congr_fderiv ?_
    ext ξ
    simp only [smul_neg, neg_apply, smul_apply, smul_eq_mul, neg_mul, mul_neg, neg_neg]
    ring
  exact h1.fun_add h2

/-- The second derivative: `D²F(p)(ξ, η) = ⟪ξ, η⟫ + cos (ℓ p) * ℓ ξ * ℓ η / 2` for all `p`, `ξ`
and `η`. The first term is the Hessian of `‖p‖² / 2` and the second comes from the cosine. -/
theorem cosineDensity_hessian (ℓ : E →L[ℝ] ℝ) (p ξ η : E) :
    fderiv ℝ (fderiv ℝ (cosineDensity ℓ)) p ξ η =
      ⟪ξ, η⟫ + Real.cos (ℓ p) * ℓ ξ * ℓ η / 2 := by
  have hfun : fderiv ℝ (cosineDensity ℓ) = fun q ↦ innerSL ℝ q + (Real.sin (ℓ q) / 2) • ℓ :=
    funext fun q ↦ (hasFDerivAt_cosineDensity ℓ q).fderiv
  have h1 : HasFDerivAt (fun q : E ↦ innerSL ℝ q) (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) p :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun q : E ↦ (Real.sin (ℓ q) / 2) • ℓ)
      ((Real.cos (ℓ p) / 2) • ℓ.smulRight ℓ) p := by
    simp only [div_eq_mul_inv]
    refine (((ℓ.hasFDerivAt (x := p)).sin.mul_const (2⁻¹ : ℝ)).smul_const ℓ).congr_fderiv ?_
    ext ξ η
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfun, (h1.fun_add h2).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change ⟪ξ, η⟫ + _ = _
  ring

/-- A functional of norm at most one is bounded by the norm of its argument. -/
private theorem abs_apply_le (hℓ : ‖ℓ‖ ≤ 1) (ξ : E) : |ℓ ξ| ≤ ‖ξ‖ :=
  (ℓ.le_opNorm ξ).trans (mul_le_of_le_one_left (norm_nonneg ξ) hℓ)

/-- Uniform convexity with constant `1 / 2`: if `‖ℓ‖ ≤ 1`, then
`‖ξ‖² / 2 ≤ D²F(p)(ξ, ξ)` for all `p` and `ξ`. The cosine term is at least `-‖ξ‖² / 2`. -/
theorem cosineDensity_hessian_lower (hℓ : ‖ℓ‖ ≤ 1) (p ξ : E) :
    (1 / 2 : ℝ) * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (cosineDensity ℓ)) p ξ ξ := by
  have hsq : ℓ ξ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_apply_le hℓ ξ) 2
  rw [cosineDensity_hessian, real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg (by linarith [Real.neg_one_le_cos (ℓ p)] : (0 : ℝ) ≤ 1 + Real.cos (ℓ p))
    (sq_nonneg (ℓ ξ))]

/-- The Hessian is bounded: if `‖ℓ‖ ≤ 1`, then the operator norm of `D²F(p)` is at most `3 / 2`
for all `p`. The inner product contributes `1` and the cosine term at most `1 / 2`. -/
theorem cosineDensity_hessian_upper (hℓ : ‖ℓ‖ ≤ 1) (p : E) :
    ‖fderiv ℝ (fderiv ℝ (cosineDensity ℓ)) p‖ ≤ (3 / 2 : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by norm_num) fun ξ η ↦ ?_
  have hcos : |Real.cos (ℓ p) * ℓ ξ * ℓ η / 2| ≤ ‖ξ‖ * ‖η‖ / 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_two]
    have h := mul_le_mul (mul_le_mul (Real.abs_cos_le_one (ℓ p)) (abs_apply_le hℓ ξ)
      (abs_nonneg _) zero_le_one) (abs_apply_le hℓ η) (abs_nonneg _)
      (mul_nonneg zero_le_one (norm_nonneg ξ))
    linarith
  rw [cosineDensity_hessian, Real.norm_eq_abs]
  calc |⟪ξ, η⟫ + Real.cos (ℓ p) * ℓ ξ * ℓ η / 2|
      ≤ |⟪ξ, η⟫| + |Real.cos (ℓ p) * ℓ ξ * ℓ η / 2| := abs_add_le _ _
    _ ≤ ‖ξ‖ * ‖η‖ + ‖ξ‖ * ‖η‖ / 2 := add_le_add (abs_real_inner_le_norm ξ η) hcos
    _ = 3 / 2 * ‖ξ‖ * ‖η‖ := by ring

/-- The upper bound as a quadratic form: if `‖ℓ‖ ≤ 1`, then `D²F(p)(ξ, ξ) ≤ 3 * ‖ξ‖² / 2` for
all `p` and `ξ`. This follows from `cosineDensity_hessian_upper`. -/
theorem cosineDensity_hessian_le (hℓ : ‖ℓ‖ ≤ 1) (p ξ : E) :
    fderiv ℝ (fderiv ℝ (cosineDensity ℓ)) p ξ ξ ≤ (3 / 2 : ℝ) * ‖ξ‖ ^ 2 :=
  calc fderiv ℝ (fderiv ℝ (cosineDensity ℓ)) p ξ ξ
      ≤ ‖fderiv ℝ (fderiv ℝ (cosineDensity ℓ)) p‖ * ‖ξ‖ * ‖ξ‖ :=
        (Real.le_norm_self _).trans (ContinuousLinearMap.le_opNorm₂ _ ξ ξ)
    _ ≤ (3 / 2 : ℝ) * ‖ξ‖ ^ 2 := by
        rw [mul_assoc, ← sq]
        exact mul_le_mul_of_nonneg_right (cosineDensity_hessian_upper hℓ p) (sq_nonneg _)

/-- If `ℓ ≠ 0`, the Hessian of `cosineDensity ℓ` is not constant: it differs at `0` and at a
point `p` with `ℓ p = π`. A quadratic polynomial has a constant Hessian, so the density is not
one. -/
theorem cosineDensity_hessian_ne (hℓ : ℓ ≠ 0) :
    ∃ p, fderiv ℝ (fderiv ℝ (cosineDensity ℓ)) p ≠ fderiv ℝ (fderiv ℝ (cosineDensity ℓ)) 0 := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ℓ ξ ≠ 0 := by
    by_contra h
    exact hℓ (ContinuousLinearMap.ext fun ξ ↦ by simpa using not_exists.1 h ξ)
  refine ⟨(Real.pi / ℓ ξ) • ξ, fun h ↦ hξ ?_⟩
  have h' := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ ↦ A ξ ξ) h
  simp only [cosineDensity_hessian, map_smul, smul_eq_mul, div_mul_cancel₀ _ hξ, Real.cos_pi,
    map_zero, Real.cos_zero] at h'
  exact mul_self_eq_zero.1 (by linarith)

/-- On `ℝ^n`, for every coordinate `i`, the function `F p = ‖p‖² / 2 + (1 - cos (p i)) / 2` is
real-analytic, satisfies `‖ξ‖² / 2 ≤ D²F(p)(ξ, ξ)` and `‖D²F(p)‖ ≤ 3 / 2` for all `p` and `ξ`,
and its Hessian is not constant. So the hypotheses of a regularity theorem for analytic
densities with bounded, uniformly positive Hessian hold for more than quadratic polynomials,
in every dimension `n ≥ 1`.

The function is `cosineDensity ℓ` for the functional `ℓ p = ⟪e i, p⟫` of the `i`-th basis
vector, which has norm one. -/
theorem exists_analytic_density {n : ℕ} (i : Fin n) :
    ∃ F : ℝ^n → ℝ, (∀ p, F p = ‖p‖ ^ 2 / 2 + (1 - Real.cos (p i)) / 2) ∧
      AnalyticOnNhd ℝ F univ ∧
      (∀ p ξ, (1 / 2 : ℝ) * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ) ∧
      (∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ (3 / 2 : ℝ)) ∧
      ∃ p, fderiv ℝ (fderiv ℝ F) p ≠ fderiv ℝ (fderiv ℝ F) 0 := by
  have hℓ : ‖innerSL ℝ (EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
  refine ⟨cosineDensity (innerSL ℝ (EuclideanSpace.single i 1)), fun p ↦ ?_,
    analyticOnNhd_cosineDensity _, cosineDensity_hessian_lower hℓ.le,
    cosineDensity_hessian_upper hℓ.le, cosineDensity_hessian_ne fun h ↦ ?_⟩
  · simp [cosineDensity, EuclideanSpace.inner_single_left]
  · simp [h] at hℓ

end PDE.Examples.CalculusOfVariations
