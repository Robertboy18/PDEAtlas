/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Local uniform convergence of primitives

On a bounded interval, the error in a primitive is bounded by interval length times
the uniform error in its integrand. Thus taking primitives preserves local uniform
convergence of continuous functions.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} {l : Filter ι} {f : ℝ → E} {F : ι → ℝ → E}

/-- Local uniform convergence of continuous integrands implies local uniform convergence
of their primitives based at any fixed point. -/
theorem TendstoLocallyUniformly.intervalIntegral
    (h : TendstoLocallyUniformly F f l) (hF : ∀ i, Continuous (F i)) (a : ℝ) :
    TendstoLocallyUniformly (fun i x ↦ ∫ t in a..x, F i t) (fun x ↦ ∫ t in a..x, f t) l := by
  rcases l.eq_or_neBot with rfl | hl
  · exact fun _ _ _ ↦ ⟨univ, univ_mem, by simp⟩
  have hf : Continuous f := h.continuous (Frequently.of_forall hF)
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  let R : ℝ := max (max R₀ |a|) 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have haR : |a| ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hxR (x : ℝ) (hx : x ∈ K) : |x| ≤ R := by
    have hx₀ : |x| ≤ R₀ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hR₀ hx
    exact hx₀.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hconv := (tendstoLocallyUniformly_iff_forall_isCompact.mp h) (Icc (-R) R) isCompact_Icc
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hden : 0 < 2 * R + 1 := by positivity
  have hδ : 0 < ε / (2 * R + 1) := div_pos hε hden
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv _ hδ] with i hi x hx
  rw [dist_eq_norm, ← intervalIntegral.integral_sub
    (hf.intervalIntegrable a x) ((hF i).intervalIntegrable a x)]
  have hbound : ∀ t ∈ Ι a x, ‖f t - F i t‖ ≤ ε / (2 * R + 1) := by
    intro t ht
    simpa only [dist_eq_norm] using
      (hi t (uIcc_subset_Icc (abs_le.mp haR) (abs_le.mp (hxR x hx))
        (uIoc_subset_uIcc ht))).le
  calc
    ‖∫ t in a..x, f t - F i t‖ ≤ ε / (2 * R + 1) * |x - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ ≤ ε / (2 * R + 1) * (2 * R) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      calc
        |x - a| ≤ |x| + |a| := abs_sub _ _
        _ ≤ R + R := add_le_add (hxR x hx) haR
        _ = 2 * R := (two_mul R).symm
    _ < ε / (2 * R + 1) * (2 * R + 1) :=
      mul_lt_mul_of_pos_left (lt_add_one _) hδ
    _ = ε := div_mul_cancel₀ ε hden.ne'
