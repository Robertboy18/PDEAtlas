/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import CAS.ExactTactic

/-!
# Exponential bounds for oriented primitives

A primitive based at zero preserves any positive exponential growth rate,
with norm bound `C / η`. Time reversal treats negative endpoints.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_integral_zero_to_le_exp_of_nonneg
    {η C : ℝ} {f : ℝ → E} (hη : 0 < η) (hC : 0 ≤ C)
    (hbound : ∀ s, ‖f s‖ ≤ Real.exp (η * |s|) * C) {t : ℝ} (ht : 0 ≤ t) :
    ‖∫ s in (0 : ℝ)..t, f s‖ ≤ Real.exp (η * t) * (C / η) := by
  have hg : Continuous (fun s ↦ Real.exp (η * s) * C) := by fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
    (f := f) (g := fun s ↦ Real.exp (η * s) * C)
    (Filter.Eventually.of_forall fun s hs ↦ by
      simpa only [abs_of_pos hs.1] using hbound s)
    (hg.intervalIntegrable 0 t)
  have hd : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun r ↦ Real.exp (η * r) * (C / η)) (Real.exp (η * s) * C) s := by
    intro s _
    cas using hη
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hg.intervalIntegrable 0 t)] at hi
  simp only [mul_zero, Real.exp_zero, one_mul] at hi
  exact hi.trans (sub_le_self _ (div_nonneg hC hη.le))

/-- The primitive of an exponentially bounded function has the same growth
rate on both halves of the real line. -/
theorem norm_integral_zero_to_le_of_exponential_bound
    {η C : ℝ} {f : ℝ → E} (hη : 0 < η) (hC : 0 ≤ C)
    (hbound : ∀ s, ‖f s‖ ≤ Real.exp (η * |s|) * C) (t : ℝ) :
    ‖∫ s in (0 : ℝ)..t, f s‖ ≤ Real.exp (η * |t|) * (C / η) := by
  rcases le_total 0 t with ht | ht
  · simpa only [abs_of_nonneg ht] using
      norm_integral_zero_to_le_exp_of_nonneg hη hC hbound ht
  · have hi := norm_integral_zero_to_le_exp_of_nonneg hη hC
      (f := fun s ↦ f (-s)) (fun s ↦ by simpa only [abs_neg] using hbound (-s))
      (neg_nonneg.mpr ht)
    rw [intervalIntegral.integral_comp_neg, neg_zero, neg_neg,
      intervalIntegral.integral_symm, norm_neg] at hi
    simpa only [abs_of_nonpos ht] using hi

end PDE.Analysis
