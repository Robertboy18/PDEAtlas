/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Derivatives of `φ ∘ ‖·‖` and of `‖·‖ ∘ u`

Two pointwise facts about a norm composed with a function, on either side, in every real normed
space. For a radial function `v(y) = φ(|y|)` that is differentiable at a point `x ≠ 0`, the
profile `φ` is differentiable at `|x|` and `|φ'(|x|)| ≤ ‖∇v(x)‖`. For a map `u` between real
normed spaces that is differentiable at `x`, the length `|u|` satisfies Kato's inequality
`‖∇|u|(x)‖ ≤ ‖∇u(x)‖`. Here `∇` is Mathlib's Fréchet derivative, which is `0` where the
function is not differentiable. Kato's inequality for Sobolev maps, with the weak gradient of
`|u|`, is not stated here.

On an inner product space `PDE.Analysis.Radial.norm_fderiv_comp_norm` gives
`‖∇v(x)‖ = |φ'(|x|)|` when `φ` is differentiable at `|x|`, so there the inequality for the
profile is an equality. For real functions `PDE.Analysis.Calculus.ae_hasDerivAt_abs` is the
chain rule for `|f|` almost everywhere.

## Main results

* `PDE.Analysis.Radial.hasDerivAt_of_hasFDerivAt_comp_norm`: if `y ↦ φ(|y|)` has the derivative
  `v'` at `x ≠ 0`, then `φ` has the derivative `v'(x / |x|)` at `|x|`.
* `PDE.Analysis.Radial.differentiableAt_of_differentiableAt_comp_norm`: the profile is
  differentiable at `|x|`.
* `PDE.Analysis.Radial.abs_deriv_le_norm_fderiv_comp_norm`: `|φ'(|x|)| ≤ ‖∇v(x)‖`.
* `PDE.norm_fderiv_norm_le`: Kato's inequality at a point.

## How it works

Along the ray through `x ≠ 0` the radial function is the profile: `φ(r) = v(r x / |x|)` for
`r > 0`. The chain rule along the ray gives `φ'(|x|) = ∇v(x) (x / |x|)`, and `x / |x|` is a unit
vector. For Kato's inequality the difference quotients satisfy
`| |u(x + h)| - |u(x)| | ≤ |u(x + h) - u(x)|`. In the limit `|∇|u|(x) h| ≤ |∇u(x) h|` for every
direction `h`, so the operator norms compare.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, American
  Mathematical Society, 2001, Chapter 6 (the derivative of the absolute value of a function).
  <https://doi.org/10.1090/gsm/014>
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace PDE.Analysis.Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : ℝ → ℝ} {x : E}

/-- **The profile of a radial function is differentiable where the function is.** If
`y ↦ φ(|y|)` has the derivative `v'` at a point `x ≠ 0` of a real normed space, then `φ` has
the derivative `v' (x / |x|)` at `|x|`: along the ray through `x` the function is `φ`. -/
theorem hasDerivAt_of_hasFDerivAt_comp_norm (hx : x ≠ 0) {v' : E →L[ℝ] ℝ}
    (hd : HasFDerivAt (fun y ↦ φ ‖y‖) v' x) :
    HasDerivAt φ (v' (NormedSpace.normalize x)) ‖x‖ := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hen : ‖NormedSpace.normalize x‖ = 1 := NormedSpace.norm_normalize hx
  have hγ : HasDerivAt (fun r : ℝ ↦ r • NormedSpace.normalize x) (NormedSpace.normalize x) ‖x‖ := by
    simpa using (hasDerivAt_id ‖x‖).smul_const (NormedSpace.normalize x)
  have hv : HasFDerivAt (fun y ↦ φ ‖y‖) v' (‖x‖ • NormedSpace.normalize x) := by
    rw [NormedSpace.norm_smul_normalize]
    exact hd
  refine (hv.comp_hasDerivAt ‖x‖ hγ).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hxn] with r hr
  simp only [Function.comp_apply, norm_smul, hen, mul_one, Real.norm_eq_abs,
    abs_of_pos (mem_Ioi.mp hr)]

/-- If a radial function `y ↦ φ(|y|)` is differentiable at `x ≠ 0`, its profile `φ` is
differentiable at `|x|`. -/
theorem differentiableAt_of_differentiableAt_comp_norm (hx : x ≠ 0)
    (hd : DifferentiableAt ℝ (fun y ↦ φ ‖y‖) x) : DifferentiableAt ℝ φ ‖x‖ :=
  (hasDerivAt_of_hasFDerivAt_comp_norm hx hd.hasFDerivAt).differentiableAt

/-- For a radial function `v(y) = φ(|y|)` on a real normed space that is differentiable at
`x ≠ 0`, `|φ'(|x|)| ≤ ‖∇v(x)‖`: the derivative of `φ` is the derivative of `v` in the radial
direction. -/
theorem abs_deriv_le_norm_fderiv_comp_norm (hx : x ≠ 0)
    (hd : DifferentiableAt ℝ (fun y ↦ φ ‖y‖) x) :
    |deriv φ ‖x‖| ≤ ‖fderiv ℝ (fun y ↦ φ ‖y‖) x‖ := by
  rw [(hasDerivAt_of_hasFDerivAt_comp_norm hx hd.hasFDerivAt).deriv, ← Real.norm_eq_abs]
  refine ((fderiv ℝ (fun y ↦ φ ‖y‖) x).le_opNorm _).trans_eq ?_
  rw [NormedSpace.norm_normalize hx, mul_one]

end PDE.Analysis.Radial

namespace PDE

/-- **Kato's inequality at a point.** If a map `u` between real normed spaces is
differentiable at `x`, then `‖∇|u|(x)‖ ≤ ‖∇u(x)‖`: the difference quotients of the length `|u|`
are at most those of `u`. Where `|u|` is not differentiable its derivative is `0` by
convention, and the inequality holds. -/
theorem norm_fderiv_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F} {x : E} (hu : DifferentiableAt ℝ u x) :
    ‖fderiv ℝ (fun y ↦ ‖u y‖) x‖ ≤ ‖fderiv ℝ u x‖ := by
  by_cases hw : DifferentiableAt ℝ (fun y ↦ ‖u y‖) x
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h ↦ ?_
    have h1 := (continuous_norm.tendsto (fderiv ℝ (fun y ↦ ‖u y‖) x h)).comp
      (hw.hasFDerivAt.lim_real h)
    have h2 := (continuous_norm.tendsto (fderiv ℝ u x h)).comp (hu.hasFDerivAt.lim_real h)
    refine (le_of_tendsto_of_tendsto h1 h2 ?_).trans ((fderiv ℝ u x).le_opNorm h)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    change ‖c • (‖u (x + c⁻¹ • h)‖ - ‖u x‖)‖ ≤ ‖c • (u (x + c⁻¹ • h) - u x)‖
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le (u (x + c⁻¹ • h)) (u x)) hc.le
  · rw [fderiv_zero_of_not_differentiableAt hw, norm_zero]
    exact norm_nonneg _

end PDE
