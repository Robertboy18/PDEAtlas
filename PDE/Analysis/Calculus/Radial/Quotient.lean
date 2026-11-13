/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Radial quotient bounds and axis-trace obstructions

The mean value theorem bounds `g(r) / r` by bounds for `g'` when `g(0) = 0`.
The closed-cell version uses `g'(0)` as the regularized axis value instead of
Lean's totalized division by zero.

Conversely, a nonzero continuous axis trace makes the quotient unbounded in every
right neighborhood. Adding a continuous remainder cannot remove this obstruction.
-/

@[expose] public section

namespace PDE.Analysis

open Set
open scoped Topology

/-- A vanishing radial trace converts derivative bounds into quotient bounds. -/
theorem radial_quotient_mem_Icc
    {g g' : ℝ → ℝ} {r lo hi : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn g (Icc 0 r))
    (hderiv : ∀ x ∈ Ioo 0 r, HasDerivAt g (g' x) x)
    (hzero : g 0 = 0) (hbound : ∀ x ∈ Ioo 0 r, g' x ∈ Icc lo hi) :
    g r / r ∈ Icc lo hi := by
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope g g' hr hcont hderiv
  simp only [hzero, sub_zero] at heq
  rw [← heq]
  exact hbound c hc

/-- The regularized quotient is enclosed on the entire closed first cell. -/
theorem regularized_radial_quotient_mem_Icc
    {g g' : ℝ → ℝ} {radius lo hi : ℝ}
    (hcont : ContinuousOn g (Icc 0 radius))
    (hderiv : ∀ x ∈ Ioo 0 radius, HasDerivAt g (g' x) x)
    (hzero : g 0 = 0) (hbound : ∀ x ∈ Icc 0 radius, g' x ∈ Icc lo hi)
    {r : ℝ} (hr : r ∈ Icc 0 radius) :
    (if r = 0 then g' 0 else g r / r) ∈ Icc lo hi := by
  split_ifs with h
  · subst r
    exact hbound 0 hr
  · have hpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm h)
    apply radial_quotient_mem_Icc hpos
      (hcont.mono (Icc_subset_Icc le_rfl hr.2))
    · intro x hx
      exact hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 hr.2⟩
    · exact hzero
    · intro x hx
      exact hbound x ⟨hx.1.le, le_trans hx.2.le hr.2⟩

/-- A continuous radial derivative can have a bounded quotient near the axis
only if its axis trace vanishes exactly. -/
theorem radial_trace_eq_zero_of_quotient_bound
    {g : ℝ → ℝ} {radius bound : ℝ} (hradius : 0 < radius)
    (hcont : ContinuousAt g 0)
    (hbound : ∀ r ∈ Ioo 0 radius, |g r / r| ≤ bound) : g 0 = 0 := by
  have hlim : Filter.Tendsto (fun r : ℝ ↦ |g r|) (𝓝[>] 0) (𝓝 |g 0|) :=
    hcont.abs.tendsto.mono_left nhdsWithin_le_nhds
  have hright : Filter.Tendsto (fun r : ℝ ↦ bound * r) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun r : ℝ ↦ bound * r) 0 :=
      continuousAt_const.mul continuousAt_id
    simpa only [mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hle : |g 0| ≤ 0 := le_of_tendsto_of_tendsto hlim hright (by
    filter_upwards [Ioo_mem_nhdsGT hradius] with r hr
    have hb := hbound r hr
    rw [abs_div, abs_of_pos hr.1] at hb
    exact (div_le_iff₀ hr.1).mp hb)
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

/-- Adding a continuous remainder cannot make a radial quotient bounded near
the axis unless its numerator vanishes there. The quotient's coefficient must
be nonzero. -/
theorem radial_trace_eq_zero_of_residual_bound
    {g remainder : ℝ → ℝ} {radius bound coefficient : ℝ}
    (hradius : 0 < radius) (hcoefficient : coefficient ≠ 0)
    (hg : ContinuousAt g 0) (hremainder : ContinuousAt remainder 0)
    (hbound : ∀ r ∈ Ioo 0 radius,
      |remainder r + coefficient * g r / r| ≤ bound) : g 0 = 0 := by
  have hcont : ContinuousAt (fun r ↦ r * remainder r + coefficient * g r) 0 :=
    (continuousAt_id.mul hremainder).add (continuousAt_const.mul hg)
  have hzero := radial_trace_eq_zero_of_quotient_bound hradius hcont (by
    intro r hr
    simpa [add_div, hr.1.ne'] using hbound r hr)
  simp only [zero_mul, zero_add] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hcoefficient

/-- A nonzero continuous radial trace makes the residual arbitrarily large
in every right neighborhood of the axis, despite any continuous remainder. -/
theorem exists_lt_abs_radial_residual
    {g remainder : ℝ → ℝ} {radius coefficient : ℝ}
    (hradius : 0 < radius) (hcoefficient : coefficient ≠ 0)
    (hg : ContinuousAt g 0) (hremainder : ContinuousAt remainder 0)
    (htrace : g 0 ≠ 0) (bound : ℝ) :
    ∃ r ∈ Ioo 0 radius, bound < |remainder r + coefficient * g r / r| := by
  by_contra! hbound
  exact htrace (radial_trace_eq_zero_of_residual_bound
    hradius hcoefficient hg hremainder hbound)

end PDE.Analysis
