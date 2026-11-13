/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Recovering homogeneous coefficients from Taylor remainders

A native analytic expansion whose value is of order at least `N` has zero
homogeneous diagonal coefficients below `N`. This finite-order version of
analytic uniqueness allows polynomial approximations to determine coefficients.
-/

@[expose] public section

open scoped Topology

open Filter Asymptotics

variable {E : Type*} [NormedAddCommGroup E]

/-- Near zero, a higher nonnegative integral power of the norm is bounded by a lower one. -/
theorem Asymptotics.isBigO_norm_pow_norm_pow {N n : ℕ} (hn : n ≤ N) :
    (fun y : E ↦ ‖y‖ ^ N) =O[𝓝 0] fun y ↦ ‖y‖ ^ n := by
  apply IsBigO.of_bound'
  filter_upwards [Metric.ball_mem_nhds (0 : E) zero_lt_one] with y hy
  have hy' : ‖y‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hy
  simpa only [norm_pow, norm_norm] using
    pow_le_pow_of_le_one (norm_nonneg y) hy'.le hn

variable [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An analytic function of order at least `N` has no homogeneous terms of lower degree. -/
theorem HasFPowerSeriesAt.apply_eq_zero_of_isBigO_norm_pow
    {f : E → F} {p : FormalMultilinearSeries ℝ E F} (hp : HasFPowerSeriesAt f p 0)
    {N n : ℕ} (hf : f =O[𝓝 0] fun y ↦ ‖y‖ ^ N) (hn : n < N) :
    ∀ y, p n (fun _ ↦ y) = 0 := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hsum : p.partialSum (n + 1) = fun y ↦ p n (fun _ ↦ y) := by
      funext y
      refine Finset.sum_eq_single n (fun k hk hkn ↦ ?_) (by simp)
      exact ih k ((Finset.mem_range_succ_iff.mp hk).lt_of_ne hkn)
        ((Finset.mem_range_succ_iff.mp hk).trans_lt hn) y
    have hrem : (fun y ↦ f y - p.partialSum (n + 1) y) =O[𝓝 0] fun y ↦ ‖y‖ ^ (n + 1) := by
      simpa only [zero_add] using hp.isBigO_sub_partialSum_pow (n + 1)
    have hf' := hf.trans (Asymptotics.isBigO_norm_pow_norm_pow (Nat.succ_le_of_lt hn))
    have hdiag : (fun y ↦ p n (fun _ ↦ y)) =O[𝓝 0] fun y ↦ ‖y‖ ^ (n + 1) := by
      simpa only [Pi.sub_apply, sub_sub_cancel, hsum] using hf'.sub hrem
    exact hdiag.continuousMultilinearMap_apply_eq_zero
