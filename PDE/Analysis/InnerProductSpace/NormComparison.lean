/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Norm bounds from inner-product inequalities

Cauchy–Schwarz turns a positive multiple of a squared norm bounded by an inner
product into a norm comparison, with the reciprocal coefficient preserved.
-/

@[expose] public section

namespace PDE.Analysis

/-- A positive quadratic lower bound on an inner product controls the first vector's
norm by the second vector's norm divided by that coefficient. -/
theorem norm_le_of_mul_norm_sq_le_inner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : H} {c : ℝ} (hc : 0 < c) (h : c * ‖a‖ ^ 2 ≤ inner ℝ b a) :
    ‖a‖ ≤ c⁻¹ * ‖b‖ := by
  have hbound := h.trans (real_inner_le_norm b a)
  by_cases hzero : ‖a‖ = 0
  · rw [hzero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg b)
  have hpos := lt_of_le_of_ne (norm_nonneg a) (Ne.symm hzero)
  rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ hc]
  exact (mul_le_mul_iff_right₀ hpos).1 (by nlinarith [hbound])

end PDE.Analysis
