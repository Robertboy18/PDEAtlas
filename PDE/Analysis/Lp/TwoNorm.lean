/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# A bound of an `L²` norm is a bound of the integral of the square

A bound is often stated as `‖f‖_{L²} ≤ ε` and computed as `∫ |f|² ≤ ε²`. For Mathlib's
extended seminorm `eLpNorm f 2 μ` the two are equivalent, on every measure space, for every
almost everywhere strongly measurable `f` with values in a normed group and every `ε ≥ 0`
(`PDE.Analysis.eLpNorm_two_le_ofReal_iff`). The proof squares both sides:
`eLpNorm f 2 μ ^ 2 = ∫⁻ ‖f‖²` by `eLpNorm_nnreal_pow_eq_lintegral`, and squaring is monotone on
`[0, ∞]`. The same equivalence for an exponent other than `2` is not stated here.
-/

@[expose] public section

namespace PDE.Analysis

open MeasureTheory
open scoped ENNReal

/-- For an almost everywhere strongly measurable `f` and `ε ≥ 0`, `‖f‖_{L²(μ)} ≤ ε` if and only
if `∫⁻ ‖f‖² ∂μ ≤ ε²`, with both sides in `[0, ∞]`. -/
theorem eLpNorm_two_le_ofReal_iff {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ) {ε : ℝ} (hε : 0 ≤ ε) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal ε ↔
      ∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ ≤ ENNReal.ofReal (ε ^ 2) := by
  have h2 : eLpNorm f 2 μ ^ 2 = ∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (μ := μ) (f := f)
      (by norm_num) hf
    simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
    rw [h]
    refine lintegral_congr fun a ↦ ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [← h2, ENNReal.ofReal_pow hε]
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).symm

end PDE.Analysis
