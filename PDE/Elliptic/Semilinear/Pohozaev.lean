/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.Rellich

/-!
# Pohozaev's identity for compactly supported classical solutions

For `-Δu = F'(u)` on `ℝ^n`, a compactly supported `C²` solution satisfies (`integral_pohozaev_eq`)

`(n - 2) ∫ |Du|² = 2n ∫ F(u)`.

The primitive is `C¹` and normalized by `F(0) = 0`. That normalization makes `F ∘ u` compactly
supported, so its integral is a finite integral. In positive dimension, the pointwise equation
outside the compact support implies `F'(0) = 0`. On a bounded domain the identity acquires a
boundary flux (`PDE.Elliptic.Semilinear.Pohozaev.Boundary`); zero Dirichlet data alone do not make
that flux vanish.

For `F(u) = |u|^{p+1}/(p+1)` this is the Derrick-Pohozaev identity (18) of Evans's §9.4.2 without
its boundary integral; Evans proves (18) on a bounded domain for solutions with zero boundary
values.

## How it works

Evans multiplies the equation by `x · Du` and integrates by parts, (14)-(18). We do the same on
`ℝ^n`, where compact support removes every boundary term. The Rellich identity
`integral_dilation_mul_laplacian_eq` gives `∫ (x · Du) Δu = ((n - 2)/2) ∫ |Du|²`, the boundary-free
form of Evans's (15)-(16). The chain rule turns `(x · Du) F'(u)` into `x · D(F ∘ u)`, and
`integral_dilation_eq` gives `∫ x · D(F ∘ u) = -n ∫ F(u)`, as in his step 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2 (Derrick-Pohozaev identity), proof of Theorem 3
  (Nonexistence of nontrivial solution), (14)-(18), pp. 552-553, and the remark naming (18), p. 554.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

open MeasureTheory PDE.DistributionTheory

namespace PDE.Elliptic.Semilinear

variable {n : ℕ}

/-- Pohozaev's identity for a compactly supported classical solution of `-Δu = F'(u)`.
The potential is `C¹` with `F(0) = 0`; no sign, growth or dimension restriction is needed.
All integrals use Euclidean volume. The sign corresponds to the positive operator `-Δ`. -/
theorem integral_pohozaev_eq {u : ℝ^n → ℝ} {F : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hcompact : HasCompactSupport u)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (heq : ∀ x, -laplacian u x = deriv F (u x)) :
    ((n : ℝ) - 2) * (∫ x, ‖∇ u x‖ ^ 2) =
      2 * (n : ℝ) * ∫ x, F (u x) := by
  have hcomp : ContDiff ℝ 1 (fun x ↦ F (u x)) := hF.comp (hu.of_le (by norm_num))
  have hcompactComp : HasCompactSupport (fun x ↦ F (u x)) := hcompact.comp_left hF0
  have hdilation := integral_dilation_eq hcomp hcompactComp
  have hrellich := integral_dilation_mul_laplacian_eq hu hcompact
  have hchain (x : ℝ^n) : advectiveDerivative id (fun y ↦ F (u y)) x =
      advectiveDerivative id u x * deriv F (u x) := by
    simp only [advectiveDerivative_eq_sum_mul_partialDeriv, id_eq]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [partialDeriv_comp_real i hF.differentiable_one.differentiableAt
      (hu.differentiable (by norm_num)).differentiableAt]
    ring
  have hnegative : (fun x ↦ advectiveDerivative id (fun y ↦ F (u y)) x) =
      fun x ↦ -(advectiveDerivative id u x * laplacian u x) := by
    funext x
    rw [hchain, ← heq x, mul_neg]
  rw [hnegative, integral_neg] at hdilation
  nlinarith

end PDE.Elliptic.Semilinear

end
