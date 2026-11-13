/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SmoothTransitionBounds

/-!
# A global derivative bound for the smooth transition

Reflection about the midpoint transfers the existing flat-endpoint estimate
to the whole transition interval. The derivative is zero outside that interval.

## Main results

* `smoothTransition_one_sub`: `σ(1 - t) = 1 - σ(t)` for `σ = Real.smoothTransition`.
* `deriv_smoothTransition_one_sub`: `σ'(1 - t) = σ'(t)`.
* `deriv_smoothTransition_zero_of_nonpos`: `σ'(t) = 0` for `t ≤ 0`.
* `deriv_smoothTransition_zero_of_one_le`: `σ'(t) = 0` for `t ≥ 1`.
* `abs_deriv_smoothTransition_le`: `|σ'(t)| ≤ 36` for every `t`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter Topology

/-- Reflection exchanges the two exponential factors defining the transition. -/
theorem smoothTransition_one_sub (t : ℝ) :
    Real.smoothTransition (1 - t) = 1 - Real.smoothTransition t := by
  have hden := (Real.smoothTransition.pos_denom t).ne'
  simp only [Real.smoothTransition, sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - t))]
  field_simp [hden]
  ring

/-- The transition derivative is symmetric about the midpoint. -/
theorem deriv_smoothTransition_one_sub (t : ℝ) :
    deriv Real.smoothTransition (1 - t) = deriv Real.smoothTransition t := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have hleft := (hd (1 - t)).hasDerivAt.comp t
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
  have hright := (hasDerivAt_const t 1).sub (hd t).hasDerivAt
  have heq : (fun s ↦ Real.smoothTransition (1 - s)) =
      (fun s ↦ 1 - Real.smoothTransition s) := funext smoothTransition_one_sub
  change HasDerivAt (fun s ↦ Real.smoothTransition (1 - s)) _ t at hleft
  rw [heq] at hleft
  have h := hleft.unique hright
  simpa using h

/-- The derivative vanishes on the entire nonpositive half-line, including its endpoint. -/
theorem deriv_smoothTransition_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  rcases lt_or_eq_of_le ht with ht | rfl
  · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ 0 := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    simpa using heq.deriv_eq
  · simpa using iteratedDeriv_smoothTransition_zero 1

/-- The derivative vanishes from the right endpoint onward. -/
theorem deriv_smoothTransition_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  rw [← deriv_smoothTransition_one_sub]
  exact deriv_smoothTransition_zero_of_nonpos (sub_nonpos.mpr ht)

/-- A uniform bound for the derivative, with no restriction on the input. -/
theorem abs_deriv_smoothTransition_le (t : ℝ) :
    |deriv Real.smoothTransition t| ≤ 36 := by
  by_cases ht : t ≤ 0
  · rw [deriv_smoothTransition_zero_of_nonpos ht, abs_zero]
    norm_num
  by_cases ht₁ : 1 ≤ t
  · rw [deriv_smoothTransition_zero_of_one_le ht₁, abs_zero]
    norm_num
  by_cases hmid : t ≤ 1 / 2
  · convert abs_deriv_smoothTransition_le_factorial_mul_pow 0 (le_of_not_ge ht) hmid
      using 1
    norm_num
  · rw [← deriv_smoothTransition_one_sub]
    convert abs_deriv_smoothTransition_le_factorial_mul_pow 0
      (by linarith : 0 ≤ 1 - t) (by linarith : 1 - t ≤ 1 / 2) using 1
    norm_num

end PDE.Analysis
