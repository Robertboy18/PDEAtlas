/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Parity under differentiation

Differentiation interchanges odd and even functions. Differentiating a family
with respect to a separate parameter preserves oddness in its other variable.
The results hold for the total derivative, including at points where it is
defined to be zero because the function is not differentiable.
-/

@[expose] public section

namespace PDE.Analysis

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of an odd function is even. -/
theorem even_deriv_of_odd {f : 𝕜 → F} (hf : Function.Odd f) :
    Function.Even (deriv f) := by
  have hfun : (fun r ↦ f (-r)) = -f := funext hf
  intro r
  have hderiv := congrFun (congrArg deriv hfun) r
  rw [deriv_comp_neg, deriv.neg] at hderiv
  exact neg_inj.mp hderiv

/-- The derivative of an even function is odd. -/
theorem odd_deriv_of_even {f : 𝕜 → F} (hf : Function.Even f) :
    Function.Odd (deriv f) := by
  have hfun : (fun r ↦ f (-r)) = f := funext hf
  intro r
  have hderiv := congrFun (congrArg deriv hfun) r
  rw [deriv_comp_neg] at hderiv
  exact neg_eq_iff_eq_neg.mp hderiv

/-- Differentiating a parameter preserves oddness in the other variable. -/
theorem odd_deriv_parameter {X : Type*} [Neg X]
    {φ : 𝕜 → X → F} (hodd : ∀ q, Function.Odd (φ q)) (t : 𝕜) :
    Function.Odd (fun r ↦ deriv (fun q ↦ φ q r) t) := by
  intro r
  have hfun : (fun q ↦ φ q (-r)) = -(fun q ↦ φ q r) :=
    funext fun q ↦ hodd q r
  have hderiv := congrArg (fun f : 𝕜 → F ↦ deriv f t) hfun
  simpa only [deriv.neg] using hderiv

end PDE.Analysis
