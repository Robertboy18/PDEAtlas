/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Characteristics.Equation
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import PDE.FDeriv.Operators

/-!
# Complete-integral envelopes

We prove the envelope theorem of Evans, §3.1.2, Theorem 1, for a smooth parameterized family of
solutions to `F(Du, u, x) = 0`. When the parameter derivative vanishes along a smooth selector,
the resulting envelope satisfies the same nonlinear first-order equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.1.2, Theorem 1, equations (10)-(13).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (partialDeriv)

namespace NonlinearFirstOrder

open scoped RealInnerProductSpace

variable {n : ℕ}

section PositiveDimension

variable [Fact (0 < n)]

/-!
## §3.1 Complete integrals and envelopes

Evans, §3.1.2, Theorem 1 applies on open spatial and parameter
domains: if `u(·;a)` satisfies a nonlinear first-order PDE residual for each
admissible parameter `a` and `a = φ(x)` satisfies the envelope equation
`Dₐu(x;φ(x)) = 0`, then the envelope `v(x) = u(x;φ(x))` satisfies the same
residual.

-/

section CompleteIntegralsEnvelopes

variable {m : ℕ}

/-- Evans, §3.1.2, Theorem 1: the local envelope construction preserves
`F(Du,u,x)=0` on an open domain.

The family is required to be `C¹` only on the product `U × A`, the selector
only on `U`, and the residual only for parameters in the open set `A`.
The regularity assumptions also show that the envelope is differentiable, so the conclusion is the
classical-solution predicate rather than merely the residual equation. -/
theorem envelope_isClassicalSolution {U : Set (ℝ^n)} {A : Set (ℝ^m)} {F : ℝ^n → ℝ → ℝ^n → ℝ}
    {u : ℝ^n → ℝ^m → ℝ} {φ : ℝ^n → ℝ^m} (hU : IsOpen U) (hA : IsOpen A)
    (hu : ContDiffOn ℝ 1 (fun xa : ℝ^n × ℝ^m ↦ u xa.1 xa.2) (U ×ˢ A)) (hφ : ContDiffOn ℝ 1 φ U)
    (hφA : Set.MapsTo φ U A)
    (hsol : ∀ a ∈ A, HasZeroResidual (n := n) { F := F, domain := U } (fun x : ℝ^n ↦ u x a))
    (henv : ∀ x ∈ U, fderiv ℝ (fun a : ℝ^m ↦ u x a) (φ x) = 0) :
    IsClassicalSolution (n := n) { F := F, domain := U } (fun x : ℝ^n ↦ u x (φ x)) := by
  intro x hxU
  have hxA : φ x ∈ A := hφA hxU
  set L := fderiv ℝ (fun xa : ℝ^n × ℝ^m ↦ u xa.1 xa.2) (x, φ x)
  have hL : HasFDerivAt (fun xa : ℝ^n × ℝ^m ↦ u xa.1 xa.2) L (x, φ x) :=
    ((hu.contDiffAt ((hU.prod hA).mem_nhds ⟨hxU, hxA⟩)).differentiableAt one_ne_zero).hasFDerivAt
  have hdφ := ((hφ.contDiffAt (hU.mem_nhds hxU)).differentiableAt one_ne_zero).hasFDerivAt
  -- Chain rules for the envelope, the frozen-parameter slice, and the parameter slice.
  have henvD : HasFDerivAt (fun y ↦ u y (φ y))
      (L.comp ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ φ x))) x :=
    (hL.comp x ((hasFDerivAt_id x).prodMk hdφ) :)
  have hsliceD : HasFDerivAt (fun y ↦ u y (φ x)) (L.comp (.inl ℝ _ _)) x :=
    (hL.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (φ x)) :)
  have hparD : HasFDerivAt (fun a ↦ u x a) (L.comp (.inr ℝ _ _)) (φ x) :=
    (hL.comp (φ x) (hasFDerivAt_prodMk_right (𝕜 := ℝ) x (φ x)) :)
  -- The envelope condition kills the parameter contribution.
  have heq : fderiv ℝ (fun y ↦ u y (φ y)) x = fderiv ℝ (fun y ↦ u y (φ x)) x := by
    rw [henvD.fderiv, hsliceD.fderiv]
    ext v
    have h := congrArg (· (fderiv ℝ φ x v)) (hparD.fderiv.symm.trans (henv x hxU))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, zero_apply] at h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.inl_apply]
    rw [show (v, fderiv ℝ φ x v) = (v, 0) + (0, fderiv ℝ φ x v) by simp, map_add, h, add_zero]
  refine ⟨henvD.differentiableAt, ?_⟩
  have hgrad : ∇ (fun y ↦ u y (φ y)) x = ∇ (fun y ↦ u y (φ x)) x := by
    simp only [gradient, heq]
  simpa [hgrad] using hsol (φ x) hxA x hxU

end CompleteIntegralsEnvelopes

end PositiveDimension

end NonlinearFirstOrder
