/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Value and gradient bounds at a point

`PDE.HasPointBounds f x v d` says that a real function `f` is differentiable at `x` with
`|f x| ≤ v` and `‖Df(x)‖ ≤ d`. The bounds propagate through sums, differences, scalar multiples
and products by the Leibniz rule `D(fg) = f Dg + g Df`, and depend only on the germ of `f` at `x`.
This is the bookkeeping by which weighted estimates of explicit expressions (products of profile
derivatives, coordinates and velocity components) are checked one point at a time, before the
two-point estimates are derived from the gradient bounds by the mean value inequality.

## Main definitions

* `HasPointBounds`: `f` is differentiable at `x`, `|f x| ≤ v` and `‖Df(x)‖ ≤ d`.

## Main results

* `HasPointBounds.congr`: the bounds depend only on the germ of `f` at `x`.
* `HasPointBounds.add`: `f + g` has the bounds `(v + v', d + d')`.
* `HasPointBounds.mul`: `f g` has the bounds `(v v', v d' + v' d)`.
* `HasPointBounds.const_mul`: `a f` has the bounds `(|a| v, |a| d)`.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `f` is differentiable at `x`, `|f x| ≤ v` and `‖Df(x)‖ ≤ d`. -/
structure HasPointBounds (f : E → ℝ) (x : E) (v d : ℝ) : Prop where
  /-- Differentiability at the point. -/
  differentiableAt : DifferentiableAt ℝ f x
  /-- The value bound. -/
  abs_le : |f x| ≤ v
  /-- The gradient bound. -/
  norm_fderiv_le : ‖fderiv ℝ f x‖ ≤ d

namespace HasPointBounds

variable {f g : E → ℝ} {x : E} {v d v' d' : ℝ}

/-- The value bound is nonnegative. -/
theorem value_nonneg (h : HasPointBounds f x v d) : 0 ≤ v := (abs_nonneg _).trans h.abs_le

/-- The gradient bound is nonnegative. -/
theorem deriv_nonneg (h : HasPointBounds f x v d) : 0 ≤ d := (norm_nonneg _).trans h.norm_fderiv_le

/-- Monotonicity in the bounds. -/
theorem mono (h : HasPointBounds f x v d) (hv : v ≤ v') (hd : d ≤ d') :
    HasPointBounds f x v' d' :=
  ⟨h.differentiableAt, h.abs_le.trans hv, h.norm_fderiv_le.trans hd⟩

/-- The bounds depend only on the germ at the point. -/
theorem congr (h : HasPointBounds f x v d) (hfg : f =ᶠ[𝓝 x] g) : HasPointBounds g x v d where
  differentiableAt := h.differentiableAt.congr_of_eventuallyEq hfg.symm
  abs_le := by rw [← hfg.eq_of_nhds]; exact h.abs_le
  norm_fderiv_le := by rw [← hfg.fderiv_eq]; exact h.norm_fderiv_le

/-- Constants. -/
theorem const (a : ℝ) : HasPointBounds (fun _ : E ↦ a) x |a| 0 :=
  ⟨differentiableAt_const a, le_rfl, by simp⟩

/-- A function vanishing near the point. -/
theorem of_eventuallyEq_zero (h : f =ᶠ[𝓝 x] fun _ ↦ 0) : HasPointBounds f x 0 0 := by
  simpa using (const (x := x) (0 : ℝ)).congr h.symm

/-- Sums. -/
theorem add (hf : HasPointBounds f x v d) (hg : HasPointBounds g x v' d') :
    HasPointBounds (fun y ↦ f y + g y) x (v + v') (d + d') where
  differentiableAt := hf.differentiableAt.add hg.differentiableAt
  abs_le := (abs_add_le _ _).trans (add_le_add hf.abs_le hg.abs_le)
  norm_fderiv_le := by
    rw [fderiv_fun_add hf.differentiableAt hg.differentiableAt]
    exact (norm_add_le _ _).trans (add_le_add hf.norm_fderiv_le hg.norm_fderiv_le)

/-- Negation. -/
theorem neg (hf : HasPointBounds f x v d) : HasPointBounds (fun y ↦ -f y) x v d where
  differentiableAt := hf.differentiableAt.neg
  abs_le := by rw [abs_neg]; exact hf.abs_le
  norm_fderiv_le := by rw [fderiv_fun_neg, norm_neg]; exact hf.norm_fderiv_le

/-- Differences. -/
theorem sub (hf : HasPointBounds f x v d) (hg : HasPointBounds g x v' d') :
    HasPointBounds (fun y ↦ f y - g y) x (v + v') (d + d') := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Products, by the Leibniz rule. -/
theorem mul (hf : HasPointBounds f x v d) (hg : HasPointBounds g x v' d') :
    HasPointBounds (fun y ↦ f y * g y) x (v * v') (v * d' + v' * d) where
  differentiableAt := hf.differentiableAt.mul hg.differentiableAt
  abs_le := by
    rw [abs_mul]; exact mul_le_mul hf.abs_le hg.abs_le (abs_nonneg _) hf.value_nonneg
  norm_fderiv_le := by
    rw [fderiv_fun_mul hf.differentiableAt hg.differentiableAt]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact add_le_add (mul_le_mul hf.abs_le hg.norm_fderiv_le (norm_nonneg _) hf.value_nonneg)
      (mul_le_mul hg.abs_le hf.norm_fderiv_le (norm_nonneg _) hg.value_nonneg)

/-- Scalar multiples. -/
theorem const_mul (hf : HasPointBounds f x v d) (a : ℝ) :
    HasPointBounds (fun y ↦ a * f y) x (|a| * v) (|a| * d) := by
  simpa using (const (x := x) a).mul hf

end HasPointBounds

end PDE
