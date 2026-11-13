/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

import CAS.ExactTactic
import PDE.Analysis.Calculus.SmoothTransitionDerivatives

/-!
# A logarithmically slow scalar cutoff

The outer radius is `δ` and the logarithmic width is `L`. The inner radius
`δ * exp (-L)` is positive. Constancy below this inner radius supplies smoothness
at zero, where the logarithmic expression itself is not used.

Both weighted derivative bounds use one constant chosen from the first two
ordinary derivatives of Mathlib's fixed smooth transition, before either
parameter is chosen. This is a scalar profile; no normal-coordinate or ambient
Hessian estimate is asserted here.
-/

@[expose] public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace PDE.Analysis

/-- A cutoff with outer radius `δ` and logarithmic width `L`, extended as one
on the nonpositive half-line. For positive parameters its inner plateau ends at
`δ * Real.exp (-L)`. -/
def logarithmicCutoff (δ L r : ℝ) : ℝ :=
  if 0 < r then Real.smoothTransition ((Real.log δ - Real.log r) / L) else 1

private theorem logarithmicCutoff_eq_one {δ L r : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hr : r ≤ δ * Real.exp (-L)) :
    logarithmicCutoff δ L r = 1 := by
  by_cases hr0 : 0 < r
  · rw [logarithmicCutoff, ite_eq_left hr0]
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hL).2
    have hlog := Real.log_le_log hr0 hr
    rw [Real.log_mul hδ.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    cas using [hlog]
  · simp only [logarithmicCutoff, ite_eq_right hr0]

private theorem logarithmicCutoff_eq_zero {δ L r : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hr : δ ≤ r) :
    logarithmicCutoff δ L r = 0 := by
  rw [logarithmicCutoff, ite_eq_left (hδ.trans_le hr)]
  exact Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (Real.log_le_log hδ hr)) hL.le)

private theorem logarithmicCutoff_mem_Icc (δ L r : ℝ) :
    logarithmicCutoff δ L r ∈ Icc (0 : ℝ) 1 := by
  by_cases hr : 0 < r
  · simp only [logarithmicCutoff, ite_eq_left hr]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · simp [logarithmicCutoff, hr]

private theorem contDiff_logarithmicCutoff {δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) :
    ContDiff ℝ ∞ (logarithmicCutoff δ L) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : 0 < r
  · have hphase : ContDiffAt ℝ ∞ (fun s : ℝ ↦ (Real.log δ - Real.log s) / L) r :=
      (contDiffAt_const.sub (Real.contDiffAt_log.mpr hr.ne')).div_const L
    refine (Real.smoothTransition.contDiffAt.comp r hphase).congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hr] with s hs
    simp only [logarithmicCutoff, ite_eq_left hs, Function.comp_def]
  · have hε : 0 < δ * Real.exp (-L) := mul_pos hδ (Real.exp_pos _)
    have hrε : r < δ * Real.exp (-L) := (le_of_not_gt hr).trans_lt hε
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hrε] with s hs
    exact logarithmicCutoff_eq_one hδ hL hs.le

-- The transition itself has a noncompact plateau, but its derivative does not.

private theorem hasDerivAt_logarithmicCutoff {δ L r : ℝ} (hr : 0 < r) :
    HasDerivAt (logarithmicCutoff δ L)
      (-deriv Real.smoothTransition ((Real.log δ - Real.log r) / L) / (L * r)) r := by
  have hphase : HasDerivAt (fun s : ℝ ↦ (Real.log δ - Real.log s) / L)
      (-1 / (L * r)) r := by
    cas
  have htransition : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  have hcomp := (htransition ((Real.log δ - Real.log r) / L)).hasDerivAt.comp r hphase
  have halgebra :
      deriv Real.smoothTransition ((Real.log δ - Real.log r) / L) * (-1 / (L * r)) =
        -deriv Real.smoothTransition ((Real.log δ - Real.log r) / L) / (L * r) := by
    cas
  refine (hcomp.congr_deriv halgebra).congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hr] with s hs
  simp only [logarithmicCutoff, ite_eq_left hs, Function.comp_def]

private theorem deriv_deriv_logarithmicCutoff {δ L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    deriv (deriv (logarithmicCutoff δ L)) r =
      deriv (deriv Real.smoothTransition) ((Real.log δ - Real.log r) / L) /
          (L ^ 2 * r ^ 2) +
        deriv Real.smoothTransition ((Real.log δ - Real.log r) / L) / (L * r ^ 2) := by
  let u : ℝ → ℝ := fun s ↦ (Real.log δ - Real.log s) / L
  have hphase : HasDerivAt u (-1 / (L * r)) r := by
    dsimp only [u]
    cas
  have htransition : Differentiable ℝ (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two
  have hnum := ((htransition (u r)).hasDerivAt.comp r hphase).neg
  have hden : HasDerivAt (fun s : ℝ ↦ L * s) L r := by
    cas
  have hquot := hnum.fun_div hden (mul_ne_zero hL.ne' hr.ne')
  have halgebra :
      (-(deriv (deriv Real.smoothTransition) (u r) * (-1 / (L * r))) * (L * r) -
          (-deriv Real.smoothTransition (u r)) * L) / (L * r) ^ 2 =
        deriv (deriv Real.smoothTransition) (u r) / (L ^ 2 * r ^ 2) +
          deriv Real.smoothTransition (u r) / (L * r ^ 2) := by
    cas using [hL, hr]
  have heq : deriv (logarithmicCutoff δ L) =ᶠ[𝓝 r]
      (fun s ↦ -deriv Real.smoothTransition (u s) / (L * s)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact (hasDerivAt_logarithmicCutoff hs).deriv
  exact ((hquot.congr_deriv halgebra).congr_of_eventuallyEq heq).deriv

/-- One constant controls both weighted derivatives of the logarithmic cutoff,
independently of its outer radius and logarithmic width. The inner plateau has
strictly positive radius, and smoothness is global on the scalar line. -/
theorem exists_pos_logarithmicCutoff_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ δ L : ℝ, 0 < δ → 1 ≤ L →
      0 < δ * Real.exp (-L) ∧ δ * Real.exp (-L) < δ ∧
      ContDiff ℝ ∞ (logarithmicCutoff δ L) ∧
      (∀ r, r ≤ δ * Real.exp (-L) → logarithmicCutoff δ L r = 1) ∧
      (∀ r, δ ≤ r → logarithmicCutoff δ L r = 0) ∧
      (∀ r, logarithmicCutoff δ L r ∈ Icc (0 : ℝ) 1) ∧
      (∀ r, 0 < r →
        r * |deriv (logarithmicCutoff δ L) r| ≤ C / L ∧
        r ^ 2 * |deriv (deriv (logarithmicCutoff δ L)) r| ≤ C / L) := by
  have hd : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv Real.smoothTransition)) :=
    (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨M₁, hM₁⟩ :=
    hasCompactSupport_deriv_smoothTransition.exists_bound_of_continuous hd.continuous
  obtain ⟨M₂, hM₂⟩ :=
    hasCompactSupport_deriv_smoothTransition.deriv.exists_bound_of_continuous hdd.continuous
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  refine ⟨M₁ + M₂ + 1, by positivity, ?_⟩
  intro δ L hδ hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLsq : L ≤ L ^ 2 := by
    cas using [mul_le_mul_of_nonneg_left hL hLpos.le]
  have hε : 0 < δ * Real.exp (-L) := mul_pos hδ (Real.exp_pos _)
  have hεδ : δ * Real.exp (-L) < δ := by
    have hexp : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hLpos)
    simpa only [mul_one] using mul_lt_mul_of_pos_left hexp hδ
  refine ⟨hε, hεδ, contDiff_logarithmicCutoff hδ hLpos,
    (fun r hr ↦ logarithmicCutoff_eq_one hδ hLpos hr),
    (fun r hr ↦ logarithmicCutoff_eq_zero hδ hLpos hr),
    logarithmicCutoff_mem_Icc δ L, ?_⟩
  intro r hr
  have hfirst := hM₁ ((Real.log δ - Real.log r) / L)
  have hsecond := hM₂ ((Real.log δ - Real.log r) / L)
  simp only [Real.norm_eq_abs] at hfirst hsecond
  constructor
  · rw [(hasDerivAt_logarithmicCutoff hr).deriv]
    simp only [abs_div, abs_neg, abs_mul, abs_of_pos hLpos, abs_of_pos hr]
    calc
      r * (|deriv Real.smoothTransition ((Real.log δ - Real.log r) / L)| / (L * r)) =
          |deriv Real.smoothTransition ((Real.log δ - Real.log r) / L)| / L := by
        cas using [hLpos, hr]
      _ ≤ M₁ / L := div_le_div_of_nonneg_right hfirst hLpos.le
      _ ≤ (M₁ + M₂ + 1) / L :=
        div_le_div_of_nonneg_right (by cas using [hM₂0]) hLpos.le
  · rw [deriv_deriv_logarithmicCutoff hLpos hr]
    have hcancel (q a : ℝ) : r ^ 2 * (a / (q * r ^ 2)) = a / q := by
      rw [← mul_div_assoc, mul_comm (r ^ 2), mul_div_mul_right _ _ (pow_ne_zero 2 hr.ne')]
    calc
      r ^ 2 * |deriv (deriv Real.smoothTransition) ((Real.log δ - Real.log r) / L) /
          (L ^ 2 * r ^ 2) +
          deriv Real.smoothTransition ((Real.log δ - Real.log r) / L) / (L * r ^ 2)| ≤
        r ^ 2 * (|deriv (deriv Real.smoothTransition) ((Real.log δ - Real.log r) / L) /
          (L ^ 2 * r ^ 2)| +
          |deriv Real.smoothTransition ((Real.log δ - Real.log r) / L) / (L * r ^ 2)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (sq_nonneg r)
      _ = |deriv (deriv Real.smoothTransition) ((Real.log δ - Real.log r) / L)| / L ^ 2 +
          |deriv Real.smoothTransition ((Real.log δ - Real.log r) / L)| / L := by
        simp only [abs_div, abs_mul, abs_pow, abs_of_pos hLpos, abs_of_pos hr]
        rw [mul_add, hcancel, hcancel]
      _ ≤ M₂ / L ^ 2 + M₁ / L := add_le_add
        (div_le_div_of_nonneg_right hsecond (sq_nonneg L))
        (div_le_div_of_nonneg_right hfirst hLpos.le)
      _ ≤ M₂ / L + M₁ / L := add_le_add
        (div_le_div_of_nonneg_left hM₂0 hLpos hLsq) le_rfl
      _ = (M₁ + M₂) / L := by cas
      _ ≤ (M₁ + M₂ + 1) / L :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hLpos.le

end PDE.Analysis
