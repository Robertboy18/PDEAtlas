/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators

/-!
# A pointwise bound on the coordinate Laplacian

At a point where `f : ℝⁿ → ℝ` is `C²`, each of the `n` terms `∂ᵢ∂ᵢf(x) = D²f(x)(eᵢ, eᵢ)` of the
Laplacian is bounded by the operator norm of the second derivative.

## Main results

* `ContDiffAt.abs_laplacian_le`: `|Δf(x)| ≤ n ‖D²f(x)‖` at a point where `f` is `C²`.
-/

@[expose] public section

open PDE

variable {n : ℕ} {f : ℝ^n → ℝ} {x : ℝ^n}

/-- At a point where `f` is `C²`, `|Δf(x)| ≤ n ‖D²f(x)‖`. -/
theorem ContDiffAt.abs_laplacian_le (hf : ContDiffAt ℝ 2 f x) :
    |laplacian f x| ≤ n * ‖iteratedFDeriv ℝ 2 f x‖ := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [hf.coordinate_laplacian_eq_laplacian,
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b) x]
  calc |∑ i, iteratedFDeriv ℝ 2 f x ![b i, b i]|
      ≤ ∑ i, |iteratedFDeriv ℝ 2 f x ![b i, b i]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖iteratedFDeriv ℝ 2 f x‖ := Finset.sum_le_sum fun i _ ↦ by
        have h := (iteratedFDeriv ℝ 2 f x).le_opNorm ![b i, b i]
        simpa [Fin.prod_univ_two, b] using h
    _ = n * ‖iteratedFDeriv ℝ 2 f x‖ := by simp
