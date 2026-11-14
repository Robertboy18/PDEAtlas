/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Parity of a function from the parity of its derivative

Differentiation interchanges odd and even functions (`PDE.Analysis.even_deriv_of_odd` and
`PDE.Analysis.odd_deriv_of_even`). The converse statements hold for differentiable functions of
a real or complex variable with values in a normed space, because there a function with zero
derivative is constant. They are standard and follow no particular source.

## Main results

* `PDE.Analysis.even_of_odd_deriv`: a differentiable function whose derivative is odd is even.
* `PDE.Analysis.odd_of_even_deriv`: a differentiable function that vanishes at `0` and whose
  derivative is even is odd. The value at `0` is needed: a nonzero constant has an even
  derivative and is not odd.
-/

@[expose] public section

namespace PDE.Analysis

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

end PDE.Analysis
