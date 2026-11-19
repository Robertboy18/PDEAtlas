/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# An integrable kernel for fractional localization

A bounded Lipschitz cutoff has a first-order increment near the origin and
a bounded increment at infinity. For `0 < s < 1`, the corresponding p-th power
fractional kernel is integrable. The harmless shifted radial tail below
allows direct use of Mathlib's integrability theorem at infinity.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set

namespace SobolevSpace.Fractional.Localization

variable {n : ℕ} {s : ℝ}

/-- A radial majorant for a power of the increment of a bounded Lipschitz cutoff. -/
def cutoffKernel (n : ℕ) (s : ℝ) (h : ℝ^n) (p : ℝ := 2) : ℝ :=
  if ‖h‖ < 1 then ‖h‖ ^ (-(n : ℝ) - p * s + p)
  else 2 ^ ((n : ℝ) + p * s) * (1 + ‖h‖) ^ (-((n : ℝ) + p * s))

theorem cutoffKernel_nonneg (h : ℝ^n) (p : ℝ := 2) :
    0 ≤ cutoffKernel n s h (p := p) := by
  unfold cutoffKernel
  split <;> positivity

theorem measurable_cutoffKernel (p : ℝ := 2) :
    Measurable (cutoffKernel n s (p := p)) := by
  unfold cutoffKernel
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    (by fun_prop) (by fun_prop)

/-- The near-origin exponent uses `s < 1`; the tail uses `0 < s`.
Dimension zero is included, with its finite Haar measure. -/
theorem integrable_cutoffKernel (hs0 : 0 < s) (hs1 : s < 1) (p : ℝ := 2)
    (hp : 0 < p := by norm_num) :
    Integrable (cutoffKernel n s (p := p)) volume := by
  by_cases hn : n = 0
  · subst n
    have hconst : cutoffKernel 0 s (p := p) = fun _ ↦ cutoffKernel 0 s (p := p) 0 :=
      funext fun x ↦ congrArg (cutoffKernel 0 s (p := p)) (Subsingleton.elim x 0)
    rw [hconst]
    exact integrable_const _
  have hdim : 1 ≤ Module.finrank ℝ (ℝ^n) := by
    rw [finrank_euclideanSpace_fin]
    omega
  have hmeas : AEStronglyMeasurable (cutoffKernel n s (p := p)) volume :=
    (measurable_cutoffKernel p).aestronglyMeasurable
  rw [← integrableOn_univ, ← Set.union_compl_self (ball (0 : ℝ^n) 1)]
  refine IntegrableOn.union ?_ ?_
  · apply integrableOn_ball_of_norm_le_rpow (μ := volume) hdim
      (C := 1) (α := (n : ℝ) + p * s - p) ?_ ?_ hmeas
    · rw [finrank_euclideanSpace_fin]
      nlinarith
    · filter_upwards [ae_restrict_mem measurableSet_ball] with h hh
      have hh' : ‖h‖ < 1 := by simpa only [mem_ball_zero_iff] using hh
      rw [Real.norm_of_nonneg (cutoffKernel_nonneg h p), cutoffKernel, ite_eq_left hh', one_mul]
      rw [show -(n : ℝ) - p * s + p = -((n : ℝ) + p * s - p) by ring]
  · have htail :
        Integrable (fun h : ℝ^n ↦
          2 ^ ((n : ℝ) + p * s) * (1 + ‖h‖) ^ (-((n : ℝ) + p * s))) volume :=
      (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; nlinarith)).const_mul _
    refine htail.integrableOn.congr_fun ?_ measurableSet_ball.compl
    intro h hh
    have hh' : ¬‖h‖ < 1 := by simpa only [mem_compl_iff, mem_ball_zero_iff] using hh
    exact (ite_eq_right hh').symm

/-- At distance at least one, the shifted tail dominates the fractional power. -/
theorem rpow_le_cutoffKernel_of_one_le {p : ℝ} (hs : 0 ≤ (n : ℝ) + p * s)
    {h : ℝ^n} (hh : 1 ≤ ‖h‖) :
    ‖h‖ ^ (-((n : ℝ) + p * s)) ≤ cutoffKernel n s h (p := p) := by
  have hr : 0 < ‖h‖ := lt_of_lt_of_le zero_lt_one hh
  rw [cutoffKernel, ite_eq_right (not_lt.mpr hh)]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + ‖h‖)
    (by linarith : 1 + ‖h‖ ≤ 2 * ‖h‖) hs
  rw [Real.mul_rpow (by norm_num) (norm_nonneg h)] at hp
  rw [Real.rpow_neg hr.le, Real.rpow_neg (by positivity), ← div_eq_mul_inv, ← one_div]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hr _)
    (by positivity : 0 < (1 + ‖h‖) ^ ((n : ℝ) + p * s))).mpr
  simpa only [one_mul] using hp

end SobolevSpace.Fractional.Localization
