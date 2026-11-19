/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Gradient
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace
public import PDE.Analysis.Calculus.Semiconcavity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Positive Hessians and trace estimates

A positive operator weights an upper quadratic-form bound without changing its
direction: `tr (A B) ≤ C tr A` when `A` is positive and `B ≤ C I`.
Diagonalizing the positive operator proves this without an absolute bound on `B`.
This distinction is useful for semiconcave functions, whose Hessians need only
have an upper bound.
-/

@[expose] public section

open scoped Gradient

noncomputable section

namespace PDE.Analysis

open scoped ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A positive operator preserves an upper quadratic-form bound after taking
the trace. No lower bound or symmetry assumption on the second operator is needed. -/
theorem trace_comp_le_mul_trace
    {A B : E →ₗ[ℝ] E} (hA : A.IsPositive) {C : ℝ}
    (hB : ∀ v, ⟪v, B v⟫ ≤ C * ‖v‖ ^ 2) :
    LinearMap.trace ℝ E (A.comp B) ≤ C * LinearMap.trace ℝ E A := by
  classical
  let b := hA.isSymmetric.eigenvectorBasis rfl
  have htrace : LinearMap.trace ℝ E A = ∑ i, hA.isSymmetric.eigenvalues rfl i := by
    simpa using hA.isSymmetric.trace_eq_sum_eigenvalues rfl
  rw [LinearMap.trace_eq_sum_inner _ b, htrace, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change ⟪b i, A (B (b i))⟫ ≤ C * hA.isSymmetric.eigenvalues rfl i
  rw [← hA.isSymmetric, hA.isSymmetric.apply_eigenvectorBasis rfl,
    real_inner_smul_left]
  have h := hB (b i)
  simp only [b, OrthonormalBasis.norm_eq_one, one_pow, mul_one] at h
  exact (mul_le_mul_of_nonneg_left h (hA.nonneg_eigenvalues rfl i)).trans_eq (mul_comm _ _)

/-- A lower quadratic-form bound controls the weighted trace from below whenever
the weight is positive. The second operator need not be symmetric. -/
theorem mul_trace_le_trace_comp
    {A B : E →ₗ[ℝ] E} (hA : A.IsPositive) {c : ℝ}
    (hB : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪v, B v⟫) :
    c * LinearMap.trace ℝ E A ≤ LinearMap.trace ℝ E (B.comp A) := by
  have h := trace_comp_le_mul_trace hA (B := -B) (C := -c) (fun v ↦ by
    simpa only [LinearMap.neg_apply, inner_neg_right, neg_mul] using neg_le_neg (hB v))
  rw [LinearMap.comp_neg, map_neg, neg_mul] at h
  rw [LinearMap.trace_comp_comm']
  exact neg_le_neg_iff.mp h

omit [FiniteDimensional ℝ E] in
/-- Convexity forces the Hessian quadratic form of a `C²` function to be
nonnegative. This follows from its midpoint inequality and the second-derivative test. -/
theorem hessian_nonneg_of_convex
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f) (x v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hsemi (z : E) :
      -f (x + z) - 2 * -f x + -f (x - z) ≤ (0 : ℝ) * ‖z‖ ^ 2 := by
    have h := hconv.2 (Set.mem_univ (x + z)) (Set.mem_univ (x - z))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have heq : (1 / 2 : ℝ) • (x + z) + (1 / 2 : ℝ) • (x - z) = x := by
      rw [← smul_add]
      have : x + z + (x - z) = (2 : ℝ) • x := by rw [two_smul]; abel
      rw [this, smul_smul]
      norm_num
    rw [heq] at h
    simp only [smul_eq_mul] at h
    linarith
  have h := hessian_le_of_second_difference hf.neg hsemi v
  rw [show fderiv ℝ (fun y ↦ -f y) = fun y ↦ -fderiv ℝ f y from
    funext fun _ ↦ fderiv_fun_neg] at h
  simp only [fderiv_fun_neg, neg_apply, zero_mul] at h
  linarith

/-- Differentiating the Riesz representation identifies the derivative of the
gradient with the Hessian quadratic form. -/
theorem inner_fderiv_gradient
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    ⟪fderiv ℝ (∇ f) x v, w⟫ = fderiv ℝ (fderiv ℝ f) x v w :=
  inner_fderiv_gradient_at hf.contDiffAt v w

/-- Riesz representation preserves the smoothness of the derivative. -/
theorem contDiff_gradient {n : ℕ∞} {f : E → ℝ}
    (hf : ContDiff ℝ ((n : ℕ∞ω) + 1) f) :
    ContDiff ℝ n (∇ f) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ contDiffAt_gradient hf.contDiffAt

/-- The derivative of the gradient of a convex `C²` function is a positive
linear operator. Symmetry comes from equality of mixed derivatives. -/
theorem isPositive_fderiv_gradient {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f) (x : E) :
    (fderiv ℝ (∇ f) x).toLinearMap.IsPositive := by
  refine ⟨?_, ?_⟩
  · intro v w
    change ⟪fderiv ℝ (∇ f) x v, w⟫ = ⟪v, fderiv ℝ (∇ f) x w⟫
    rw [show ⟪v, fderiv ℝ (∇ f) x w⟫ =
      ⟪fderiv ℝ (∇ f) x w, v⟫ from real_inner_comm _ _,
      inner_fderiv_gradient hf, inner_fderiv_gradient hf]
    exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w
  · intro v
    simpa only [ContinuousLinearMap.coe_coe, RCLike.re_to_real,
      inner_fderiv_gradient hf] using hessian_nonneg_of_convex hf hconv x v

/-- The chain rule and positivity of the outer Hessian turn a one-sided
Jacobian bound into a divergence bound for a nonlinear gradient flux. -/
theorem trace_fderiv_gradient_comp_le
    {H : E → ℝ} (hH : ContDiff ℝ 2 H) (hconv : ConvexOn ℝ Set.univ H)
    {p : E → E} {x : E} (hp : DifferentiableAt ℝ p x) {C : ℝ}
    (hbound : ∀ v, ⟪v, fderiv ℝ p x v⟫ ≤ C * ‖v‖ ^ 2) :
    LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ ∇ H (p y)) x).toLinearMap ≤
      C * LinearMap.trace ℝ E (fderiv ℝ (∇ H) (p x)).toLinearMap := by
  have hgrad : DifferentiableAt ℝ (∇ H) (p x) :=
    (contDiff_gradient (n := 1) hH).differentiable one_ne_zero _
  rw [show (fun y ↦ ∇ H (p y)) = ∇ H ∘ p from rfl,
    fderiv_comp x hgrad hp]
  exact trace_comp_le_mul_trace (isPositive_fderiv_gradient hH hconv (p x)) hbound

end PDE.Analysis
