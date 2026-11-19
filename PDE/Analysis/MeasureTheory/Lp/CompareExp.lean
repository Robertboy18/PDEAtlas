/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Comparing `Lᵖ` seminorms on a common support

Mathlib's finite-measure exponent comparison, for a function supported in an
arbitrary set. The support set need not be
measurable: its measurable hull has the same measure.
-/

@[expose] public section

noncomputable section


namespace MeasureTheory

open Set
open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E]
variable {μ : Measure α} {f : α → E}

/-- If `f` is supported in `s`, compare two `Lᵖ` seminorms using the measure
of `s` rather than the measure of the whole ambient space. -/
theorem eLpNorm_le_eLpNorm_mul_rpow_measure_of_support_subset
    {p q : ℝ≥0∞} (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f μ) {s : Set α}
    (hsupp : f.support ⊆ s) :
    eLpNorm f p μ ≤
      eLpNorm f q μ * μ s ^ (1 / p.toReal - 1 / q.toReal) := by
  let t := toMeasurable μ s
  have hsupport : f.support ⊆ t :=
    hsupp.trans (subset_toMeasurable μ s)
  have hfRestrict :
      AEStronglyMeasurable f (μ.restrict t) :=
    hf.mono_measure Measure.restrict_le_self
  calc
    eLpNorm f p μ = eLpNorm f p (μ.restrict t) :=
      (eLpNorm_restrict_eq_of_support_subset hf hsupport).symm
    _ ≤ eLpNorm f q (μ.restrict t) *
          (μ.restrict t) Set.univ ^
            (1 / p.toReal - 1 / q.toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hfRestrict
    _ = eLpNorm f q μ *
          μ s ^ (1 / p.toReal - 1 / q.toReal) := by
      rw [eLpNorm_restrict_eq_of_support_subset hf hsupport]
      simp [t, measure_toMeasurable]

end MeasureTheory
