/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import PDE.Common.Euclidean
public import PDE.FDeriv.LinearPDE

/-!
# Gradient-based optimization

Optimization primitives for finite-dimensional PDE loss functions: weighted sums of gradients,
the gradient-descent step `x - η ∇f(x)`, an uncorrected Adam-style moment update, and the
gradient of a squared PDE residual. Gradients are Mathlib's `gradient` (the Riesz
representative of `fderiv`), not the output of a reverse-mode automatic differentiation.

## Main results

* `hasGradientAt_weightedSum`: the gradient of `∑ cⱼ fⱼ` is `∑ cⱼ ∇fⱼ` at points where every
  `fⱼ` is differentiable.
* `fderiv_gradientDescentStep_sub`: to first order a gradient step changes `f` by
  `-η ‖∇f(x)‖²`.
* `adamStep_secondMoment_nonneg`, `adamStep_denominator_pos`: for `0 ≤ β₂ ≤ 1` and `ε > 0`
  the Adam denominator stays positive.
* `pdeResidualGradient_eq`: `∇(r²) = 2 r ∇r` for a residual `r` differentiable at the point.

## References

* D. P. Kingma and J. Ba, "Adam: A Method for Stochastic Optimization", 3rd International
  Conference on Learning Representations (ICLR), San Diego, 2015, arXiv:1412.6980v9, Algorithm 1.
  <https://arxiv.org/abs/1412.6980v9>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace PDE.AutoDiff.Optimization

/-- Weighted sum of gradients of scalar functions. -/
def gradientSum {n : ℕ}
    (terms : List (ℝ × (ℝ^n → ℝ)))
    (x : ℝ^n) : ℝ^n :=
  (terms.map fun term ↦ term.1 • ∇ term.2 x).sum

/-- A weighted finite sum has the sum of the weighted gradients whenever its terms
are differentiable at the point. Repeated terms are counted with their multiplicity. -/
theorem hasGradientAt_weightedSum {n : ℕ}
    (terms : List (ℝ × (ℝ^n → ℝ))) (x : ℝ^n)
    (h : ∀ term ∈ terms, DifferentiableAt ℝ term.2 x) :
    HasGradientAt (fun y ↦ (terms.map fun term ↦ term.1 * term.2 y).sum)
      (gradientSum terms x) x := by
  induction terms with
  | nil => simpa [gradientSum] using hasGradientAt_const x (0 : ℝ)
  | cons term terms ih =>
      have head := h term (List.mem_cons_self ..)
      have tail := ih fun t ht ↦ h t (List.mem_cons_of_mem _ ht)
      rw [hasGradientAt_iff_hasFDerivAt] at tail ⊢
      convert (head.hasFDerivAt.const_mul term.1).add tail using 1 <;>
        simp [gradientSum, map_add, map_smul, toDual_gradient, Pi.add_def]

/-- One gradient-descent update. -/
def gradientDescentStep
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (f : E → ℝ) (x : E) (stepSize : ℝ) : E :=
  x - stepSize • ∇ f x

/-- The linearized change along a gradient step is the negative step size times
the squared gradient norm. For positive step size this is negative at noncritical points. -/
theorem fderiv_gradientDescentStep_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x : E) (stepSize : ℝ) :
    fderiv ℝ f x (gradientDescentStep f x stepSize - x) =
      -stepSize * ‖∇ f x‖ ^ 2 := by
  rw [← inner_gradient_left]
  simp [gradientDescentStep, inner_smul_right]

/-- A vanishing gradient is a fixed point of every gradient step. -/
theorem gradientDescentStep_eq_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x : E) (stepSize : ℝ) (h : ∇ f x = 0) :
    gradientDescentStep f x stepSize = x := by
  simp [gradientDescentStep, h]

/--
One uncorrected Adam-style exponential-moment update.

The operation is total. Analytic uses should separately require nonnegative second moments and a
positive denominator `Real.sqrt (newV i) + eps`. This primitive stores no time step and applies
no bias corrections `1 - beta1 ^ t` or `1 - beta2 ^ t`; the bias-corrected update of Kingma and
Ba, Algorithm 1, keeps those state components and applies those corrections.
-/
def adamStep {n : ℕ}
    (f : ℝ^n → ℝ)
    (x m v : ℝ^n)
    (stepSize beta1 beta2 eps : ℝ) :
    ℝ^n ×
      ℝ^n ×
      ℝ^n :=
  let g := ∇ f x
  let newM := beta1 • m + (1 - beta1) • g
  let gSq : ℝ^n :=
    WithLp.toLp 2 fun i ↦ g i * g i
  let newV := beta2 • v + (1 - beta2) • gSq
  let update : ℝ^n :=
    WithLp.toLp 2 fun i ↦
      stepSize * newM i / (Real.sqrt (newV i) + eps)
  (x - update, newM, newV)

/-- Convex exponential averaging preserves nonnegative second moments. -/
theorem adamStep_secondMoment_nonneg {n : ℕ}
    (f : ℝ^n → ℝ) (x m v : ℝ^n) (stepSize beta1 beta2 eps : ℝ)
    (hbeta : 0 ≤ beta2) (hbeta' : beta2 ≤ 1) (hv : ∀ i, 0 ≤ v i) (i : Fin n) :
    0 ≤ (adamStep f x m v stepSize beta1 beta2 eps).2.2 i := by
  change 0 ≤ beta2 * v i + (1 - beta2) * (∇ f x i * ∇ f x i)
  exact add_nonneg (mul_nonneg hbeta (hv i))
    (mul_nonneg (sub_nonneg.mpr hbeta') (mul_self_nonneg _))

/-- Positive regularization keeps the updated Adam denominator strictly positive. -/
theorem adamStep_denominator_pos {n : ℕ}
    (f : ℝ^n → ℝ) (x m v : ℝ^n) (stepSize beta1 beta2 eps : ℝ)
    (heps : 0 < eps) (i : Fin n) :
    0 < Real.sqrt ((adamStep f x m v stepSize beta1 beta2 eps).2.2 i) + eps :=
  add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) heps

/-- Totalized gradient in the spatial variable of a squared PDE-residual expression.

The definition is an objective-building primitive. Its interpretation as the classical gradient
of a PDE residual requires the corresponding regularity hypotheses. -/
def pdeResidualGradient {n k : ℕ}
    (pde : LinearPDE ℝ (ℝ^n) ℝ k)
    (u : ℝ^n → ℝ)
    (x : ℝ^n) : ℝ^n :=
  ∇ (fun y ↦ (pde.residual u y) ^ (2 : Nat)) x

/-- Differentiability of the residual itself suffices for the squared-residual
gradient formula; no stronger regularity of the candidate field is inferred. -/
theorem pdeResidualGradient_eq {n k : ℕ}
    (pde : LinearPDE ℝ (ℝ^n) ℝ k) (u : ℝ^n → ℝ) (x : ℝ^n)
    (h : DifferentiableAt ℝ (pde.residual u) x) :
    pdeResidualGradient pde u x =
      (2 * pde.residual u x) • ∇ (pde.residual u) x := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h.hasFDerivAt.pow 2 using 1
  simp [map_smul, toDual_gradient, two_smul, two_mul]

end PDE.AutoDiff.Optimization
