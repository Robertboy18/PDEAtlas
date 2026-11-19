/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Uniform approximation by time averages

A continuous Banach-valued field is uniformly approximated on compact sets
by its time averages, provided the averaging windows remain in the set.
The same estimate applies to supplied spatial and temporal derivative fields.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open MeasureTheory Metric Set
open scoped Interval

variable {E F : Type*} [PseudoMetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Time averages converge uniformly on a compact set along windows contained
in that set. The estimate applies to any Banach-valued field, including its jets. -/
theorem exists_timeAverage_norm_sub_le
    {K : Set (E × ℝ)} {f : E × ℝ → F}
    (hK : IsCompact K) (hf : ContinuousOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, ∀ h : ℝ, |h| < δ →
      (∀ s ∈ Icc (0 : ℝ) 1, (p.1, p.2 + h * s) ∈ K) →
      ‖(∫ s in (0 : ℝ)..1, f (p.1, p.2 + h * s)) - f p‖ ≤ ε := by
  obtain ⟨δ, hδ, hcontrol⟩ := uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hf) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp h hh hwindow
  have hcont : ContinuousOn (fun s : ℝ ↦ f (p.1, p.2 + h * s)) (Icc (0 : ℝ) 1) :=
    hf.comp (continuous_const.prodMk
      (continuous_const.add (continuous_const.mul continuous_id))).continuousOn hwindow
  have hint : IntervalIntegrable (fun s : ℝ ↦ f (p.1, p.2 + h * s)) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  have hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖f (p.1, p.2 + h * s) - f p‖ ≤ ε := by
    have hdist : dist (p.1, p.2 + h * s) p ≤ |h| := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      simp only [add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
      exact max_le (abs_nonneg h) (mul_le_of_le_one_right (abs_nonneg h) hs.2)
    simpa only [dist_eq_norm] using
      (hcontrol (p.1, p.2 + h * s) (hwindow s hs) p hp (hdist.trans_lt hh)).le
  calc
    ‖(∫ s in (0 : ℝ)..1, f (p.1, p.2 + h * s)) - f p‖ =
        ‖∫ s in (0 : ℝ)..1, f (p.1, p.2 + h * s) - f p‖ := by
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
      simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    _ ≤ ε := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := ε)
        (f := fun s ↦ f (p.1, p.2 + h * s) - f p) (fun s hs ↦ by
          rw [uIoc_of_le zero_le_one] at hs
          exact hbound s ⟨hs.1.le, hs.2⟩)
      simpa only [sub_zero, abs_one, mul_one] using h

end PDE.Analysis
