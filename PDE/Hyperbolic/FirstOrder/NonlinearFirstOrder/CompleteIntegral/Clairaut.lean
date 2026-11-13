/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.CompleteIntegral.Envelope
public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Clairaut
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Clairaut complete integrals and their stationary envelopes

For `x · Du + f(Du) = u`, the family `u(x; a) = a · x + f(a)` is a complete
integral wherever `f` is C². Its spatial gradient is exactly `a`, so the parameter derivative of the
first jet has an identity component and full rank. The family is the complete integral (5) of
Evans, §3.1.1, Example 1.

An invertible Hessian of `f` at `a₀` additionally produces a stationary
envelope near `x₀ = -∇f(a₀)`. The selector, its regularity, and the classical
PDE are obtained by the local envelope construction.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.1.1, Example 1, equations (4)-(5); §3.1.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter
open scoped Gradient Topology RealInnerProductSpace

namespace NonlinearFirstOrder

variable {n : ℕ}

/-- The spatial gradient of a Clairaut family member is its parameter. -/
theorem gradient_clairautSolution (f : ℝ^n → ℝ) (a x : ℝ^n) :
    ∇ (clairautSolution f a) x = a :=
  (show HasGradientAt (clairautSolution f a) a x from
    (innerSL ℝ a).hasFDerivAt.add_const (f a)).gradient

/-- The parameter derivative of the affine Clairaut family. -/
theorem hasFDerivAt_clairaut_parameter {f : ℝ^n → ℝ} {a : ℝ^n}
    (hf : DifferentiableAt ℝ f a) (x : ℝ^n) :
    HasFDerivAt (fun b ↦ clairautSolution f b x) (innerSL ℝ x + fderiv ℝ f a) a := by
  have heq : (fun b ↦ clairautSolution f b x) = (innerSL ℝ x : ℝ^n → ℝ) + f := by
    funext b
    simp only [clairautSolution, Pi.add_apply, innerSL_apply_apply, real_inner_comm]
  rw [heq]
  exact (innerSL ℝ x).hasFDerivAt.add hf.hasFDerivAt

/-- The augmented first-jet derivative has full parameter rank: its second
component is the identity. Smoothness of the scalar term is enough. -/
theorem clairaut_parameter_rank {f : ℝ^n → ℝ} {a : ℝ^n} (hf : DifferentiableAt ℝ f a) (x : ℝ^n) :
    Function.Injective
      (fderiv ℝ (fun b ↦ (clairautSolution f b x, ∇ (clairautSolution f b) x)) a) := by
  have hjet : HasFDerivAt (fun b ↦ (clairautSolution f b x, ∇ (clairautSolution f b) x))
      ((innerSL ℝ x + fderiv ℝ f a).prod (ContinuousLinearMap.id ℝ (ℝ^n))) a := by
    simpa only [gradient_clairautSolution, id_eq] using
      (hasFDerivAt_clairaut_parameter hf x).prodMk (hasFDerivAt_id a)
  rw [hjet.fderiv]
  exact fun v w hvw ↦ congrArg Prod.snd hvw

/-- Clairaut's affine family is a complete integral on every open parameter
set where the scalar function is C². -/
theorem clairautSolution_isCompleteIntegral [Fact (0 < n)] {f : ℝ^n → ℝ} {A : Set (ℝ^n)}
    (hA : IsOpen A) (hf : ContDiffOn ℝ 2 f A) :
    IsCompleteIntegral (clairautEquation f) A (fun x a ↦ clairautSolution f a x) := by
  refine ⟨isOpen_univ, hA, ?_, ?_, ?_⟩
  · exact ((contDiff_snd.inner ℝ contDiff_fst).contDiffOn).add
      (hf.comp contDiff_snd.contDiffOn (fun _ hq ↦ hq.2))
  · exact fun a _ ↦ clairautSolution_isClassicalSolution f a
  · exact fun x _ a ha ↦ clairaut_parameter_rank
      ((hf.contDiffAt (hA.mem_nhds ha)).differentiableAt (by norm_num)) x

/-- At `x = -∇f(a)` the parameter derivative vanishes. -/
theorem clairaut_parameter_stationary {f : ℝ^n → ℝ} {a : ℝ^n} (hf : DifferentiableAt ℝ f a) :
    fderiv ℝ (fun b ↦ clairautSolution f b (-∇ f a)) a = 0 := by
  rw [(hasFDerivAt_clairaut_parameter hf (-∇ f a)).fderiv]
  ext v
  simp only [add_apply, zero_apply, innerSL_apply_apply, inner_neg_left]
  rw [← toDual_gradient]
  simp

/-- Adding the affine spatial term does not change the parameter Hessian. -/
theorem clairaut_parameter_hessian {f : ℝ^n → ℝ} {a : ℝ^n} (hf : ContDiffAt ℝ 2 f a) (x : ℝ^n) :
    fderiv ℝ (fun b ↦ fderiv ℝ (fun c ↦ clairautSolution f c x) b) a = fderiv ℝ (fderiv ℝ f) a := by
  have heq : (fun b ↦ fderiv ℝ (fun c ↦ clairautSolution f c x) b) =ᶠ[𝓝 a]
      (fun b ↦ innerSL ℝ x + fderiv ℝ f b) := by
    filter_upwards [hf.eventually (by simp)] with b hb
    exact (hasFDerivAt_clairaut_parameter (hb.differentiableAt (by norm_num)) x).fderiv
  rw [heq.fderiv_eq]
  exact ((hf.fderiv_right (by norm_num)).differentiableAt_one.hasFDerivAt.const_add
    (innerSL ℝ x)).fderiv

/-- A nondegenerate Hessian of `f` constructs a local stationary envelope of
its complete integral near `-∇f(a₀)`, including the gradient identity
`Dv = φ` and the classical Clairaut equation. -/
theorem exists_clairaut_envelope [Fact (0 < n)] {f : ℝ^n → ℝ} {A : Set (ℝ^n)} {a₀ : ℝ^n}
    (hA : IsOpen A) (ha₀ : a₀ ∈ A) (hf : ContDiffOn ℝ 2 f A)
    (hessian : (fderiv ℝ (fderiv ℝ f) a₀).IsInvertible) :
    ∃ (V : Set (ℝ^n)) (φ : ℝ^n → ℝ^n),
      IsOpen V ∧ -∇ f a₀ ∈ V ∧ φ (-∇ f a₀) = a₀ ∧ MapsTo φ V A ∧
      ContDiffOn ℝ 1 φ V ∧
      (∀ x ∈ V, x + ∇ f (φ x) = 0) ∧
      ContDiffOn ℝ 2 (fun x ↦ clairautSolution f (φ x) x) V ∧
      (∀ x ∈ V, ∇ (fun y ↦ clairautSolution f (φ y) y) x = φ x) ∧
      IsClassicalSolution { clairautEquation f with domain := V }
        (fun x ↦ clairautSolution f (φ x) x) := by
  have hf₀ : ContDiffAt ℝ 2 f a₀ := hf.contDiffAt (hA.mem_nhds ha₀)
  have hinv : (fderiv ℝ
      (fun a ↦ fderiv ℝ (fun b ↦ clairautSolution f b (-∇ f a₀)) a) a₀).IsInvertible := by
    rw [clairaut_parameter_hessian hf₀]
    exact hessian
  obtain ⟨V, φ, hV, hxV, _, hφ₀, hφA, hφ, hstat, hv, hderiv, hsol, _⟩ :=
    (clairautSolution_isCompleteIntegral hA hf).exists_local_envelope (mem_univ _)
      ha₀ (clairaut_parameter_stationary (hf₀.differentiableAt (by norm_num))) hinv
  refine ⟨V, φ, hV, hxV, hφ₀, hφA, hφ, ?_, hv, ?_, hsol⟩
  · intro x hx
    have hd := hstat x hx
    rw [(hasFDerivAt_clairaut_parameter
      ((hf.contDiffAt (hA.mem_nhds (hφA hx))).differentiableAt (by norm_num)) x).fderiv] at hd
    apply (InnerProductSpace.toDual ℝ (ℝ^n)).injective
    rw [map_add, map_zero, toDual_gradient]
    exact hd
  · intro x hx
    rw [gradient, hderiv x hx]
    exact gradient_clairautSolution f (φ x) x

end NonlinearFirstOrder
