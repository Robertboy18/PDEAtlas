/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Parity under differentiation

Differentiation interchanges odd and even functions. Differentiating a family
with respect to a separate parameter preserves oddness in its other variable.
The results hold for the total derivative, including at points where it is
defined to be zero because the function is not differentiable.

The converse statements hold for differentiable functions of a real or complex variable with
values in a normed space, because there a function with zero derivative is constant. They are
standard and follow no particular source.

## Main results

* `PDE.Analysis.even_deriv_of_odd`, `PDE.Analysis.odd_deriv_of_even`: the derivative of an odd
  function is even, and the derivative of an even function is odd, over every nontrivially
  normed field.
* `PDE.Analysis.even_of_odd_deriv`: a differentiable function of a real or complex variable
  whose derivative is odd is even.
* `PDE.Analysis.odd_of_even_deriv`: a differentiable function of a real or complex variable
  that vanishes at `0` and whose derivative is even is odd. The value at `0` is needed: a
  nonzero constant has an even derivative and is not odd.
-/

@[expose] public section

namespace PDE.Analysis

section Derivative

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

end Derivative

section Primitive

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F}

/-- A differentiable function whose derivative is odd is even. -/
theorem even_of_odd_deriv (hf : Differentiable 𝕜 f) (hodd : (deriv f).Odd) : f.Even := by
  have hneg : Differentiable 𝕜 fun y ↦ f (-y) := hf.comp differentiable_neg
  have hsub (y : 𝕜) :
      HasDerivAt (fun y ↦ f (-y) - f y) (deriv (fun y ↦ f (-y)) y - deriv f y) y :=
    (hneg y).hasDerivAt.sub (hf y).hasDerivAt
  have hd (y : 𝕜) : deriv (fun y ↦ f (-y) - f y) y = 0 := by
    rw [(hsub y).deriv, deriv_comp_neg f y, hodd y, neg_neg, sub_self]
  intro x
  have h := is_const_of_deriv_eq_zero (fun y ↦ (hsub y).differentiableAt) hd x 0
  simp only [neg_zero, sub_self] at h
  exact sub_eq_zero.mp h

/-- A differentiable function that vanishes at `0` and whose derivative is even is odd. -/
theorem odd_of_even_deriv (hf : Differentiable 𝕜 f) (heven : (deriv f).Even) (h0 : f 0 = 0) :
    f.Odd := by
  have hneg : Differentiable 𝕜 fun y ↦ f (-y) := hf.comp differentiable_neg
  have hadd (y : 𝕜) :
      HasDerivAt (fun y ↦ f (-y) + f y) (deriv (fun y ↦ f (-y)) y + deriv f y) y :=
    (hneg y).hasDerivAt.add (hf y).hasDerivAt
  have hd (y : 𝕜) : deriv (fun y ↦ f (-y) + f y) y = 0 := by
    rw [(hadd y).deriv, deriv_comp_neg f y, heven y, neg_add_cancel]
  intro x
  have h := is_const_of_deriv_eq_zero (fun y ↦ (hadd y).differentiableAt) hd x 0
  simp only [neg_zero, h0, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

end Primitive

end PDE.Analysis
