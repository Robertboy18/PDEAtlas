/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.FDeriv.Add
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Smooth
import PDE.FDeriv.PartialDeriv.Transforms

/-!
# Derivatives of a difference quotient of a smooth map

For a map `f` on `ℝⁿ`, a vector `a` and a scalar `c`, the map `y ↦ c (f(y + a) - f(y))` is a
difference quotient when `c = h⁻¹` and `a = h eₗ`. Every derivative commutes with it, because
translation commutes with the derivative (`hasFDerivAt_comp_add_right`,
`PDE.partialDeriv_comp_add_right`) and the derivative is linear. Regularity arguments by
difference quotients use this to move the operator of an equation onto the difference quotient
of its solution.

## Main results

All hold for every vector `a` and every scalar `c`.

* `PDE.hasFDerivAt_smul_comp_add_sub`: for a differentiable `f`, the derivative of
  `y ↦ c (f(y + a) - f(y))` at `x` is `c (Df(x + a) - Df(x))`.
* `PDE.partialDeriv_smul_comp_add_sub`, `PDE.divergence_smul_comp_add_sub`: the same for the
  coordinate derivatives and the divergence of a differentiable `f`.
* `PDE.laplacian_smul_comp_add_sub`: the same for the Laplacian of an `f` of class `C²`.
* `PDE.divergence_comp_add_right`: the divergence of a translate of any vector field is the
  translate of its divergence.
-/

@[expose] public section

namespace PDE

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of `y ↦ c (f(y + a) - f(y))` at `x` is `c (Df(x + a) - Df(x))`. -/
theorem hasFDerivAt_smul_comp_add_sub {f : ℝ^n → F} (hf : Differentiable ℝ f) (a : ℝ^n) (c : ℝ)
    (x : ℝ^n) :
    HasFDerivAt (fun y ↦ c • (f (y + a) - f y)) (c • (fderiv ℝ f (x + a) - fderiv ℝ f x)) x :=
  (((hasFDerivAt_comp_add_right a).mpr (hf (x + a)).hasFDerivAt).sub
    (hf x).hasFDerivAt).const_smul c

/-- The coordinate derivative of `y ↦ c (f(y + a) - f(y))` is `c (∂ᵢf(x + a) - ∂ᵢf(x))`. -/
theorem partialDeriv_smul_comp_add_sub {f : ℝ^n → F} (hf : Differentiable ℝ f) (a : ℝ^n)
    (c : ℝ) (i : Fin n) (x : ℝ^n) :
    ∂[i] (fun y ↦ c • (f (y + a) - f y)) x = c • (∂[i] f (x + a) - ∂[i] f x) := by
  change fderiv ℝ (fun y ↦ c • (f (y + a) - f y)) x (EuclideanSpace.single i 1) = _
  rw [(hasFDerivAt_smul_comp_add_sub hf a c x).fderiv]
  rfl

/-- The Laplacian of `y ↦ c (f(y + a) - f(y))` is `c (Δf(x + a) - Δf(x))`, for `f` of class
`C²`. -/
theorem laplacian_smul_comp_add_sub {f : ℝ^n → F} (hf : ContDiff ℝ 2 f) (a : ℝ^n) (c : ℝ)
    (x : ℝ^n) :
    laplacian (fun y ↦ c • (f (y + a) - f y)) x = c • (laplacian f (x + a) - laplacian f x) := by
  have h1 : ∀ i : Fin n, ∂[i] (fun y ↦ c • (f (y + a) - f y)) =
      fun y ↦ c • (∂[i] f (y + a) - ∂[i] f y) := fun i ↦
    funext fun y ↦ partialDeriv_smul_comp_add_sub (hf.differentiable (by norm_num)) a c i y
  unfold laplacian
  simp only [h1]
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ partialDeriv_smul_comp_add_sub
    ((ContDiff.partialDeriv (k := 1) hf i).differentiable one_ne_zero) a c i x

/-- The divergence of a translate is the translate of the divergence. -/
theorem divergence_comp_add_right (f : ℝ^n → ℝ^n) (a x : ℝ^n) :
    ∇· (fun y ↦ f (y + a)) x = ∇· f (x + a) := by
  rw [divergence_eq_sum, divergence_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    congrFun (partialDeriv_comp_add_right i (fun y ↦ f y i) a) x

/-- The divergence of `y ↦ c (f(y + a) - f(y))` is `c (div f(x + a) - div f(x))`. -/
theorem divergence_smul_comp_add_sub {f : ℝ^n → ℝ^n} (hf : Differentiable ℝ f) (a : ℝ^n)
    (c : ℝ) (x : ℝ^n) :
    ∇· (fun y ↦ c • (f (y + a) - f y)) x = c * (∇· f (x + a) - ∇· f x) := by
  have hi : ∀ i : Fin n, Differentiable ℝ (fun y ↦ f y i) := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable.comp hf
  rw [divergence_eq_sum, divergence_eq_sum, divergence_eq_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := partialDeriv_smul_comp_add_sub (hi i) a c i x
  rw [smul_eq_mul] at h
  exact h

end PDE
