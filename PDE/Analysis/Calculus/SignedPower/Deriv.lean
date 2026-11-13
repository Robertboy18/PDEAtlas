/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SignedPower
public import PDE.Analysis.Calculus.PositivePartRpow
public import Mathlib.Analysis.Calculus.Deriv.Abs
import CAS.ExactTactic

/-!
# Differentiating odd real powers

For `r ≥ 1`, the derivative of `|x|^(r-1) x` is `r |x|^(r-1)` on the whole
real line. Splitting into positive and negative parts handles the origin without
assigning a derivative to `|x|` there.

This gives `C¹` regularity, but not arbitrary smoothness: already at exponent
two the first derivative has a corner. Semilinear equations with real power
sources must therefore state their regularity assumptions explicitly.
-/

@[expose] public section

open Set

namespace Real

/-- The odd power has derivative `r |x|^(r-1)` for `r ≥ 1`, including at zero.
The linear endpoint is handled separately; above it, both one-sided derivatives
at zero vanish. -/
theorem hasDerivAt_signedPower {r : ℝ} (hr : 1 ≤ r) (x : ℝ) :
    HasDerivAt (signedPower r) (r * |x| ^ (r - 1)) x := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · rw [show signedPower 1 = id from funext signedPower_one]
    simpa only [sub_self, rpow_zero, mul_one] using hasDerivAt_id x
  have hd := (PDE.Analysis.hasDerivAt_posPart_rpow hr x).sub
    ((PDE.Analysis.hasDerivAt_posPart_rpow hr (-x)).comp x (hasDerivAt_neg x))
  convert hd using 1
  · funext y
    rw [signedPower_eq_posPart_sub_negPart (zero_lt_one.trans hr)]
    simp only [Pi.sub_apply, Function.comp_apply, negPart_def, posPart_def]
  · have hp : r - 1 ≠ 0 := (sub_pos.mpr hr).ne'
    rcases le_total 0 x with hx | hx
    · simp [posPart_def, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx),
        abs_of_nonneg hx, hp]
    · simp [posPart_def, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx),
        abs_of_nonpos hx, hp]

/-- Every odd power of exponent at least one is continuously differentiable. -/
theorem contDiff_one_signedPower {r : ℝ} (hr : 1 ≤ r) :
    ContDiff ℝ 1 (signedPower r) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_signedPower hr x).differentiableAt, ?_⟩
  have hd : deriv (signedPower r) = fun x ↦ r * |x| ^ (r - 1) :=
    funext fun x ↦ (hasDerivAt_signedPower hr x).deriv
  rw [hd]
  exact continuous_const.mul ((continuous_rpow_const (sub_nonneg.mpr hr)).comp
    continuous_abs)

/-- The quadratic odd power `x |x|` is not twice continuously differentiable at zero.
Its first derivative is `2 |x|`, so a second derivative would differentiate the
absolute value at its corner. Thus a real power source cannot in general be
assumed smooth solely from the condition that its exponent exceeds one. -/
theorem not_contDiffAt_two_signedPower_two :
    ¬ ContDiffAt ℝ 2 (signedPower 2) 0 := by
  intro h
  have hd := (h.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun x : ℝ ↦ (2 : ℝ)⁻¹ * deriv (signedPower 2) x) = abs := by
    funext x
    rw [(hasDerivAt_signedPower (by norm_num : (1 : ℝ) ≤ 2) x).deriv]
    norm_num
    cas
  have ha := hd.const_mul ((2 : ℝ)⁻¹)
  rw [heq] at ha
  exact not_differentiableAt_abs_zero ha

end Real
