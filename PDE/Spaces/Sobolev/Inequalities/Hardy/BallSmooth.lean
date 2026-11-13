/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Hardy.BallRegularization
public import PDE.Spaces.Sobolev.Inequalities.Hardy.IntegralLimit
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The singular Hardy weight for smooth functions on a ball

Letting the positive regularization tend to zero proves integrability of the
inverse-square energy. The origin is a null set, and Fatou's lemma retains the
uniform estimate. The data have no boundary condition.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology

namespace SobolevSpace.Hardy

variable {n : ℕ}

/-- Removing the regularization proves, rather than assumes, finiteness of the
singular energy for an arbitrary ambient C¹ function on a positive-radius ball. -/
theorem integrable_hardy_ball_and_bound_of_contDiff (hn : 3 ≤ n)
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x ↦ u x ^ 2 / ‖x‖ ^ 2) (ball (0 : ℝ^n) r) ∧
      (∫ x in ball (0 : ℝ^n) r, u x ^ 2 / ‖x‖ ^ 2) ≤
        4 * (∫ x in ball (0 : ℝ^n) r, ‖fderiv ℝ u x‖ ^ 2) +
          2 * (n : ℝ) / r ^ 2 * ∫ x in ball (0 : ℝ^n) r, u x ^ 2 := by
  let : NeZero n := ⟨by omega⟩
  let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply integrable_and_integral_le_of_ae_limit_nonneg_of_tendsto_bound
    (u := fun k x ↦ u x ^ 2 / (‖x‖ ^ 2 + ε k))
    (b := fun _ ↦ 4 * (∫ x in ball (0 : ℝ^n) r, ‖fderiv ℝ u x‖ ^ 2) +
      2 * (n : ℝ) / r ^ 2 * ∫ x in ball (0 : ℝ^n) r, u x ^ 2)
  · intro k
    have hc : Continuous (fun x ↦ u x ^ 2 / (‖x‖ ^ 2 + ε k)) :=
      (hu.continuous.pow 2).div ((continuous_norm.pow 2).add continuous_const)
        (fun x ↦ (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) (hε k)).ne')
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℝ^n) r)).mono_set
      ball_subset_closedBall
  · intro k
    exact Eventually.of_forall fun x ↦ div_nonneg (sq_nonneg _) (by positivity)
  · exact fun k ↦ integral_regularized_hardy_ball hn hu hr (hε k)
  · exact tendsto_const_nhds
  · filter_upwards [(volume.restrict (ball (0 : ℝ^n) r)).ae_ne 0] with x hx
    have hnorm : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    convert! (tendsto_const_nhds (x := u x ^ 2)).div
      (hεlim.const_add (‖x‖ ^ 2)) (by simpa only [add_zero] using hnorm) using 1
    simp only [add_zero]

/-- Division by distance to the center is square-integrable for smooth data,
without an origin value or a boundary trace condition. -/
theorem memLp_div_norm_ball_of_contDiff (hn : 3 ≤ n)
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 0 < r) :
    MemLp (fun x ↦ u x / ‖x‖) 2 (volume.restrict (ball (0 : ℝ^n) r)) := by
  have hm : AEStronglyMeasurable (fun x ↦ u x / ‖x‖)
      (volume.restrict (ball (0 : ℝ^n) r)) :=
    (hu.continuous.measurable.div continuous_norm.measurable).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [div_pow] using! (integrable_hardy_ball_and_bound_of_contDiff hn hu hr).1

end SobolevSpace.Hardy
