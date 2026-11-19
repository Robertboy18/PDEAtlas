/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# Essential bounds and integral averages

An integrable function bounded above almost everywhere has the same upper
bound for its average on a set of positive finite measure.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Elliptic.Regularity.Campanato

/-- An essential upper bound passes to the normalized integral. -/
theorem setAverage_le_of_ae_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s : Set X} (hs0 : μ s ≠ 0) (hsfin : μ s ≠ ∞)
    {f : X → ℝ} (hf : IntegrableOn f s μ) {M : ℝ}
    (hbound : ∀ᵐ x ∂μ.restrict s, f x ≤ M) :
    (⨍ x in s, f x ∂μ) ≤ M := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hsfin
  calc
    _ ≤ ⨍ _x in s, M ∂μ :=
      integral_mono_ae hf.to_average (integrable_const M).to_average
        (hbound.filter_mono (Measure.ae_smul_measure_le _))
    _ = M := setAverage_const hs0 hsfin M

end PDE.Elliptic.Regularity.Campanato
