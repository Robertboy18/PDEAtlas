/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import PDE.FDeriv.Calculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Coordinate derivatives through the squared norm

The `i`-th coordinate derivative of `‖x‖²` on `ℝ^n` is `2 xᵢ`, so a function of the squared norm
has `∂ᵢ F(‖x‖²) = 2 xᵢ F'(‖x‖²)`, and the product rule gives the derivative of a radial factor
times a function. These are the radial chain rules used by the radial Laplacian formulas and by
the radial weights of the certificate engines. Evans, §2.2.1(a), uses the same chain rule to
find `∂r/∂xᵢ = xᵢ/r` for `r = |x|`.

## Main results

* `partialDeriv_norm_sq`: `∂ᵢ ‖x‖² = 2 xᵢ`.
* `partialDeriv_comp_norm_sq`: `∂ᵢ F(‖x‖²) = 2 xᵢ F'(‖x‖²)`.
* `partialDeriv_comp_norm_sq_mul`: `∂ᵢ (F(‖x‖²) q) = 2 xᵢ F'(‖x‖²) q + F(‖x‖²) ∂ᵢ q`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(a), p. 21.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (partialDeriv)

namespace EuclideanLaplacian

variable {n : ℕ}

/-- The `i`th coordinate derivative of the squared Euclidean norm is
`2 * x i`. -/
@[simp]
theorem partialDeriv_norm_sq {n : ℕ} (i : Fin n) (x : ℝ^n) :
    (∂[i] (fun z : ℝ^n ↦ ‖z‖ ^ 2)) x = 2 * x i := by
  unfold partialDeriv
  have hInner : inner ℝ x (EuclideanSpace.single i (1 : ℝ)) = x i := by
    simpa using
      (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (v := x))
  rw [fderiv_norm_sq_apply]
  simp [innerSL_apply_apply, hInner]

/-- The coordinate derivative of a function of the squared norm:
`∂ᵢ (F(‖x‖²)) = 2 xᵢ F'(‖x‖²)`. -/
theorem partialDeriv_comp_norm_sq {F : ℝ → ℝ} (i : Fin n) {x : ℝ^n}
    (hF : DifferentiableAt ℝ F (‖x‖ ^ 2)) :
    ∂[i] (fun y : ℝ^n ↦ F (‖y‖ ^ 2)) x = 2 * x i * deriv F (‖x‖ ^ 2) := by
  rw [PDE.partialDeriv_comp_real i hF
      (((contDiff_norm_sq ℝ (n := 1))).differentiable one_ne_zero x),
    partialDeriv_norm_sq]

/-- Product rule for a radial factor: `∂ᵢ (F(‖x‖²) q) = 2 xᵢ F'(‖x‖²) q + F(‖x‖²) ∂ᵢ q`. -/
theorem partialDeriv_comp_norm_sq_mul {F : ℝ → ℝ} {q : ℝ^n → ℝ} (i : Fin n) {x : ℝ^n}
    (hF : DifferentiableAt ℝ F (‖x‖ ^ 2)) (hq : DifferentiableAt ℝ q x) :
    ∂[i] (fun y : ℝ^n ↦ F (‖y‖ ^ 2) * q y) x =
      2 * x i * deriv F (‖x‖ ^ 2) * q x + F (‖x‖ ^ 2) * ∂[i] q x := by
  have hFn : DifferentiableAt ℝ (fun y : ℝ^n ↦ F (‖y‖ ^ 2)) x :=
    hF.comp x (((contDiff_norm_sq ℝ (n := 1))).differentiable one_ne_zero x)
  rw [PDE.partialDeriv_mul hFn hq, partialDeriv_comp_norm_sq i hF]

end EuclideanLaplacian
