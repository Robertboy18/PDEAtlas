/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives through dual numbers

A dual number `z = a + b ε` records the value `a` and the derivative `b` of a function at a point:
`HasDualDerivAt g z x` says `g x = a` and `g'(x) = b`. Sums, differences, products and negations
of functions correspond to the same operations on dual numbers (the product rule is the
multiplication `ε² = 0`), so a polynomial expression evaluated on the dual numbers of its inputs
gives the value and the derivative of the expression.

## Main definitions

* `HasDualDerivAt`: `z` holds the value and the derivative of `g` at `x`.

## Main results

* `HasDualDerivAt.add`: the dual number of `f + g` is the sum of the dual numbers.
* `HasDualDerivAt.mul`: the dual number of `f * g` is the product of the dual numbers.
* `HasDualDerivAt.const`: a constant `c` has the dual number `c + 0 ε`.
* `HasDualDerivAt.id`: the identity has the dual number `x + ε` at `x`.
-/

@[expose] public section

namespace PDE.Analysis

open TrivSqZeroExt

/-- `z` holds the value and the derivative of `g` at `x`. -/
def HasDualDerivAt (g : ℝ → ℝ) (z : DualNumber ℝ) (x : ℝ) : Prop :=
  g x = z.fst ∧ HasDerivAt g z.snd x

namespace HasDualDerivAt

variable {f g : ℝ → ℝ} {a b : DualNumber ℝ} {x : ℝ}

/-- The dual number of `f + g` is the sum of the dual numbers of `f` and `g`. -/
theorem add (hf : HasDualDerivAt f a x) (hg : HasDualDerivAt g b x) :
    HasDualDerivAt (f + g) (a + b) x :=
  ⟨by simp [hf.1, hg.1], by rw [snd_add]; exact HasDerivAt.add hf.2 hg.2⟩

/-- The dual number of `f - g` is the difference of the dual numbers of `f` and `g`. -/
theorem sub (hf : HasDualDerivAt f a x) (hg : HasDualDerivAt g b x) :
    HasDualDerivAt (f - g) (a - b) x :=
  ⟨by simp [hf.1, hg.1], by rw [snd_sub]; exact HasDerivAt.sub hf.2 hg.2⟩

/-- The dual number of `-f` is the negative of the dual number of `f`. -/
theorem neg (hf : HasDualDerivAt f a x) : HasDualDerivAt (-f) (-a) x :=
  ⟨by simp [hf.1], by rw [snd_neg]; exact HasDerivAt.neg hf.2⟩

/-- **Product rule**: the dual number of `f * g` is the product of the dual numbers of `f` and `g`,
since `ε² = 0`. -/
theorem mul (hf : HasDualDerivAt f a x) (hg : HasDualDerivAt g b x) :
    HasDualDerivAt (f * g) (a * b) x := by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  have h := HasDerivAt.mul hf.2 hg.2
  rw [snd_mul]
  convert h using 1
  simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, hf.1, hg.1]
  ring

/-- A constant function `c` has the dual number `c + 0 ε` at every point. -/
theorem const (c : ℝ) (x : ℝ) : HasDualDerivAt (fun _ ↦ c) (inl c) x :=
  ⟨rfl, hasDerivAt_const x c⟩

/-- The identity has the dual number `x + ε` at `x`. -/
theorem id (x : ℝ) : HasDualDerivAt (fun y ↦ y) (inl x + inr 1) x :=
  ⟨by simp, (hasDerivAt_id' x).congr_deriv (by simp)⟩

end HasDualDerivAt

end PDE.Analysis
