/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The power integral of an Lp representative

An almost-everywhere representative has the same power integral as its `Lᵖ`
class. This lets integral estimates pass to norm estimates without choosing
a preferred representative.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integral of the p-th power of any representative is the p-th power
of the norm of its `Lᵖ` class. -/
theorem lintegral_enorm_rpow_eq_of_ae (hp : p ≠ ∞) (v : Lp F p μ) {f : α → F}
    (hf : (v : α → F) =ᵐ[μ] f) :
    (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) = ENNReal.ofReal (‖v‖ ^ p.toReal) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  calc
    _ = ∫⁻ x, ‖v x‖ₑ ^ p.toReal ∂μ :=
      lintegral_congr_ae (hf.fun_comp (fun x : F ↦ ‖x‖ₑ ^ p.toReal)).symm
    _ = _ := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le,
        ofReal_norm, Lp.enorm_def,
        eLpNorm_eq_eLpNorm' hp0 hp (Lp.aestronglyMeasurable v)]
      exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hr

end MeasureTheory.Lp
