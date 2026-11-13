/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import CAS.ExactTactic

/-!
# A positive smooth radius

The radius is constant on the inner ball and agrees with the ordinary radius
outside twice that ball. Its negative powers are bounded smooth coefficients
for the one-dimensional radial wave equation.
-/

@[expose] public noncomputable section

open Filter BoundedContinuousFunction
open scoped Topology

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- A smooth interpolation between the positive constant `c` and the identity. -/
def cutoffRadius (c r : ℝ) : ℝ :=
  c + Real.smoothTransition (r / c - 1) * (r - c)

/-- The cutoff radius is constant on the inner interval. -/
theorem cutoffRadius_eq_const {c r : ℝ} (hc : 0 < c) (hr : r ≤ c) :
    cutoffRadius c r = c := by
  have he : r / c - 1 ≤ 0 := sub_nonpos.mpr ((div_le_one hc).mpr hr)
  simp only [cutoffRadius, Real.smoothTransition.zero_of_nonpos he, zero_mul, add_zero]

/-- Beyond twice the cutoff scale the radius is unchanged. -/
theorem cutoffRadius_eq_self {c r : ℝ} (hc : 0 < c) (hr : 2 * c ≤ r) :
    cutoffRadius c r = r := by
  have he : 1 ≤ r / c - 1 := by
    have := (le_div_iff₀ hc).mpr hr
    linarith
  rw [cutoffRadius, Real.smoothTransition.one_of_one_le he]
  cas

/-- The regularized radius stays between the cutoff scale and the larger of
that scale and the original argument. -/
theorem cutoffRadius_bounds {c : ℝ} (hc : 0 < c) (r : ℝ) :
    c ≤ cutoffRadius c r ∧ cutoffRadius c r ≤ max c r := by
  by_cases hr : r ≤ c
  · simp [cutoffRadius_eq_const hc hr, max_eq_left hr]
  · have hrc : 0 ≤ r - c := sub_nonneg.mpr (le_of_not_ge hr)
    have hlo := mul_nonneg (Real.smoothTransition.nonneg (r / c - 1)) hrc
    have hhi := mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one (r / c - 1)) hrc
    rw [max_eq_right (le_of_not_ge hr), cutoffRadius]
    constructor <;> linarith

/-- The scalar cutoff radius is smooth. -/
theorem contDiff_cutoffRadius (c : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (cutoffRadius c) :=
  contDiff_const.add ((Real.smoothTransition.contDiff.comp
    ((contDiff_id.div_const c).sub contDiff_const)).mul (contDiff_id.sub contDiff_const))

/-- Composing the cutoff radius with the norm is smooth even at the origin. -/
theorem contDiff_cutoffRadius_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {c : ℝ} (hc : 0 < c) {k : ℕ∞} :
    ContDiff ℝ k (fun x : E ↦ cutoffRadius c ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := c)).congr_of_eventuallyEq
    filter_upwards [continuous_norm.continuousAt.eventually
      (gt_mem_nhds (by simpa using hc : ‖(0 : E)‖ < c))] with y hy
    exact cutoffRadius_eq_const hc hy.le
  · exact (contDiff_cutoffRadius c).contDiffAt.comp x (contDiffAt_norm ℝ hx)

/-- A negative power of the cutoff radius is a bounded continuous coefficient. -/
def radialCoefficient {c : ℝ} (hc : 0 < c) {p : ℝ} (hp : 1 ≤ p) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun r ↦ cutoffRadius c r ^ (1 - p),
      ((contDiff_cutoffRadius c (k := 1)).rpow_const_of_ne
        (fun r ↦ (hc.trans_le (cutoffRadius_bounds hc r).1).ne')).continuous⟩
    (2 * c ^ (1 - p)) (by
      intro r s
      have hb (y : ℝ) : 0 ≤ cutoffRadius c y ^ (1 - p) ∧
          cutoffRadius c y ^ (1 - p) ≤ c ^ (1 - p) :=
        ⟨Real.rpow_nonneg (hc.le.trans (cutoffRadius_bounds hc y).1) _,
          Real.rpow_le_rpow_of_nonpos hc (cutoffRadius_bounds hc y).1 (sub_nonpos.mpr hp)⟩
      change dist (cutoffRadius c r ^ (1 - p)) (cutoffRadius c s ^ (1 - p)) ≤ _
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [(hb r).1, (hb r).2, (hb s).1, (hb s).2])

/-- Evaluation of the bounded radial coefficient. -/
theorem radialCoefficient_apply {c p : ℝ} (hc : 0 < c) (hp : 1 ≤ p) (r : ℝ) :
    radialCoefficient hc hp r = cutoffRadius c r ^ (1 - p) := rfl

/-- The bounded coefficient is smooth, although the power reaction at zero need not be. -/
theorem contDiff_radialCoefficient {c p : ℝ} (hc : 0 < c) (hp : 1 ≤ p) {k : ℕ∞} :
    ContDiff ℝ k (radialCoefficient hc hp) :=
  (contDiff_cutoffRadius c).rpow_const_of_ne
    (fun r ↦ (hc.trans_le (cutoffRadius_bounds hc r).1).ne')

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
