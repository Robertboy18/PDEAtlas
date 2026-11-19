/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Derivatives of positively homogeneous functions

Let `h` be positively homogeneous of degree `e`: `h (s • y) = s ^ e • h y` for `s > 0`. If `h` has
the derivative `L` at `v`, then it has the derivative `s ^ (e - 1) • L` at `s • v`, and
`L v = e • h v` (Euler's identity, from Mathlib's local version). Along a ray the derivatives of a
sum of homogeneous terms are therefore sums of powers of the distance.

## Main results

* `hasFDerivAt_smul_of_homogeneous`: `h` has the derivative `s ^ (e - 1) • L` at `s • v`.
* `apply_self_of_hasFDerivAt_of_homogeneous`: Euler's identity `L v = e • h v`.
-/

@[expose] public section

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {h : E → F} {e : ℝ}

/-- **Derivatives scale along rays**: if `h (s • y) = s ^ e • h y` for `s > 0` and `h` has the
derivative `L` at `v`, then `h` has the derivative `s ^ (e - 1) • L` at `s • v`. -/
theorem hasFDerivAt_smul_of_homogeneous (hh : ∀ s : ℝ, 0 < s → ∀ y, h (s • y) = s ^ e • h y)
    {v : E} {L : E →L[ℝ] F} (hv : HasFDerivAt h L v) {s : ℝ} (hs : 0 < s) :
    HasFDerivAt h (s ^ (e - 1) • L) (s • v) := by
  have hfun : h = fun y ↦ s ^ e • h (s⁻¹ • y) := by
    funext y
    rw [hh s⁻¹ (inv_pos.2 hs) y, smul_smul, Real.inv_rpow hs.le,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hs e).ne', one_smul]
  have hlin : HasFDerivAt (fun y : E ↦ s⁻¹ • y) (s⁻¹ • ContinuousLinearMap.id ℝ E) (s • v) :=
    (hasFDerivAt_id (s • v)).const_smul s⁻¹
  have hv' : HasFDerivAt h L (s⁻¹ • (s • v)) := by
    rwa [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  have hcomp := (hv'.comp (s • v) hlin).const_smul (s ^ e)
  rw [hfun]
  convert hcomp using 1
  · ext w
    simp
  · ext w
    simp [smul_smul, Real.rpow_sub_one hs.ne', div_eq_mul_inv]

/-- **Euler's identity**: if `h (s • y) = s ^ e • h y` for `s > 0` and `h` has the derivative `L`
at `v`, then `L v = e • h v` (the real-exponent case of Mathlib's
`HasFDerivAt.apply_self_eq_smul_of_eventuallyEq`). -/
theorem apply_self_of_hasFDerivAt_of_homogeneous
    (hh : ∀ s : ℝ, 0 < s → ∀ y, h (s • y) = s ^ e • h y) {v : E} {L : E →L[ℝ] F}
    (hv : HasFDerivAt h L v) : L v = e • h v := by
  have h := HasFDerivAt.apply_self_eq_smul_of_eventuallyEq hv
    (Real.hasDerivAt_rpow_const (x := 1) (p := e) (Or.inl one_ne_zero))
    (Filter.eventually_of_mem (lt_mem_nhds one_pos) fun s hs ↦ hh s hs v)
  simpa using h

end PDE.Analysis
