/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Periodic functions of one variable

Facts about functions with a period, stated with Mathlib's `Function.Periodic`. They are
standard and follow no particular source.

## Main results

* `Function.Periodic.deriv`: the derivative of a function of period `c` has period `c`, over
  every nontrivially normed field and with values in every normed space. Differentiability is
  not assumed.
* `PDE.Analysis.integral_deriv_eq_zero_of_periodic`: `∫₀ᶜ f' = 0` for every function `f` of
  period `c` that has the derivative `f'` at every point, when `f'` is interval integrable.
* `PDE.Analysis.eq_zero_of_integral_eq_zero_of_periodic`: a continuous nonnegative real function
  of period `c > 0` with `∫₀ᶜ f = 0` vanishes everywhere.
* `PDE.Analysis.exists_norm_le_of_periodic`: a map `f : ℝ → Y → E` that is jointly continuous on
  `ℝ × K`, for a compact set `K`, and has the period `L ≠ 0` in its real variable is bounded on
  `ℝ × K`. This is the form with a parameter of Mathlib's
  `Function.Periodic.isBounded_of_continuous`.
* `PDE.Analysis.apply_half_eq_zero_of_odd_of_periodic`: an odd function of period `L` with values
  in a real vector space vanishes at `L / 2`, and `PDE.Analysis.eq_zero_of_odd_of_periodic`: it
  vanishes at `L / 2 + k L` for every integer `k`.
-/

@[expose] public section

open Function MeasureTheory Set

namespace PDE.Analysis

/-- The derivative of a function of period `c` has period `c`. -/
protected theorem _root_.Function.Periodic.deriv {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {c : 𝕜} (hf : f.Periodic c) :
    (deriv f).Periodic c := fun x ↦ by
  rw [← deriv_comp_add_const, hf.funext]

/-- The integral over a period of the derivative of a periodic function is zero. -/
theorem integral_deriv_eq_zero_of_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f f' : ℝ → E} {c : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hper : f.Periodic c) (hint : IntervalIntegrable f' volume 0 c) :
    ∫ x in (0 : ℝ)..c, f' x = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hf x) hint, hper.eq, sub_self]

/-- A continuous nonnegative function of period `c > 0` whose integral over a period is zero
vanishes everywhere. -/
theorem eq_zero_of_integral_eq_zero_of_periodic {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x) (hper : f.Periodic c)
    (hint : ∫ x in (0 : ℝ)..c, f x = 0) (x : ℝ) : f x = 0 := by
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ hc x
  rw [hxy]
  refine le_antisymm (not_lt.mp fun hpos ↦ ?_) (hnn y)
  exact (intervalIntegral.integral_pos hc hf.continuousOn (fun z _ ↦ hnn z)
    ⟨y, Ico_subset_Icc_self hy, hpos⟩).ne' hint

/-- A map that is jointly continuous on `ℝ × K`, for a compact set `K` of parameters, and has
the period `L ≠ 0` in its real variable is bounded on `ℝ × K`. -/
theorem exists_norm_le_of_periodic {Y E : Type*} [TopologicalSpace Y] [SeminormedAddCommGroup E]
    {f : ℝ → Y → E} {K : Set Y} {L : ℝ} (hL : L ≠ 0) (hK : IsCompact K)
    (hf : ContinuousOn (uncurry f) (univ ×ˢ K)) (hper : ∀ t ∈ K, (f · t).Periodic L) :
    ∃ M, ∀ x, ∀ t ∈ K, ‖f x t‖ ≤ M := by
  wlog hpos : 0 < L generalizing L
  · exact this (neg_ne_zero.mpr hL) (fun t ht ↦ (hper t ht).neg)
      (neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hpos) hL))
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hf.mono (prod_mono (subset_univ (Icc 0 L)) subset_rfl))
  refine ⟨M, fun x t ht ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := (hper t ht).exists_mem_Ico₀ hpos x
  rw [show f x t = f y t from hxy]
  exact hM (y, t) ⟨Ico_subset_Icc_self hy, ht⟩

/-- An odd function of period `L` vanishes at `L / 2`. -/
theorem apply_half_eq_zero_of_odd_of_periodic {E : Type*} [AddCommGroup E] [Module ℝ E]
    {g : ℝ → E} {L : ℝ} (hodd : g.Odd) (hper : g.Periodic L) : g (L / 2) = 0 := by
  have h := hper (-(L / 2))
  rw [show -(L / 2) + L = L / 2 by ring, hodd (L / 2)] at h
  have h2 : (2 : ℝ) • g (L / 2) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h
  rw [← inv_smul_smul₀ (two_ne_zero' ℝ) (g (L / 2)), h2, smul_zero]

/-- An odd function of period `L` vanishes at the odd multiples of `L / 2`. -/
theorem eq_zero_of_odd_of_periodic {E : Type*} [AddCommGroup E] [Module ℝ E] {g : ℝ → E}
    {L : ℝ} (hodd : g.Odd) (hper : g.Periodic L) (k : ℤ) : g (L / 2 + k * L) = 0 := by
  rw [(hper.int_mul k) (L / 2)]
  exact apply_half_eq_zero_of_odd_of_periodic hodd hper

end PDE.Analysis
