/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Linear lower margins at a zero endpoint

A strictly positive left derivative gives a linear lower bound for the negative
function on a sufficiently short left interval. No differentiability across a
zero-extension corner is required.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE.Analysis.Calculus

/-- Any constant strictly below the left derivative gives a left endpoint margin.
The interval can be confined to any prescribed positive width. -/
theorem exists_left_linear_margin_of_hasDerivWithinAt
    {f : ℝ → ℝ} {L s k cmax : ℝ}
    (hf : HasDerivWithinAt f s (Iio L) L) (hzero : f L = 0)
    (hk : k < s) (hcmax : 0 < cmax) :
    ∃ c : ℝ, 0 < c ∧ c ≤ cmax ∧ ∀ x ∈ Ioo (L - c) L, k * (L - x) ≤ -f x := by
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (show L ∉ Iio L by simp)).mp hf
  have he : {x | k < slope f L x} ∈ 𝓝[<] L := hs (Ioi_mem_nhds hk)
  obtain ⟨l, hl, he⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset (sub_lt_self L hcmax)).mp he
  refine ⟨L - l, sub_pos.mpr hl.2, ?_, ?_⟩
  · linarith [hl.1]
  · intro x hx
    have hxl : l < x := by linarith [hx.1]
    have hslope : k < slope f L x := he ⟨hxl, hx.2⟩
    rw [slope_def_field, hzero, sub_zero] at hslope
    have hmul := (lt_div_iff_of_neg (sub_neg.mpr hx.2)).mp hslope
    nlinarith

/-- The same endpoint estimate for a function defined smoothly on both sides. -/
theorem exists_left_linear_margin_of_hasDerivAt
    {f : ℝ → ℝ} {L s k cmax : ℝ}
    (hf : HasDerivAt f s L) (hzero : f L = 0)
    (hk : k < s) (hcmax : 0 < cmax) :
    ∃ c : ℝ, 0 < c ∧ c ≤ cmax ∧ ∀ x ∈ Ioo (L - c) L, k * (L - x) ≤ -f x :=
  exists_left_linear_margin_of_hasDerivWithinAt hf.hasDerivWithinAt hzero hk hcmax

end PDE.Analysis.Calculus
