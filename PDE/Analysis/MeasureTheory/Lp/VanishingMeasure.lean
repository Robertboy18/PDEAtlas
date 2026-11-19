/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Lower Lᵖ norms on sets of vanishing measure

A uniform Lᑫ bound forces the Lᵖ norm to vanish when the underlying measure
vanishes and `0 < p < q < ∞`. Both the functions and the measures may vary.
In particular, the functions need not converge pointwise on a shrinking set.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {ι α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable {l : Filter ι} {μ : ι → Measure α} {f : ι → α → E}

/-- A bounded family in Lᑫ tends to zero in Lᵖ as its measure tends to zero.
The strict exponent gap supplies the positive power in Hölder's inequality. -/
theorem tendsto_eLpNorm_of_measure_univ_tendsto_zero
    {p q C : ℝ≥0∞} (hp : 0 < p) (hpq : p < q) (hq : q ≠ ∞) (hC : C ≠ ∞)
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) (μ i))
    (hbound : ∀ᶠ i in l, eLpNorm (f i) q (μ i) ≤ C)
    (hμ : Tendsto (fun i ↦ μ i univ) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (f i) p (μ i)) l (𝓝 0) := by
  have hpfinite : p ≠ ∞ := ne_of_lt (hpq.trans_le le_top)
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hpfinite
  have hpqReal : p.toReal < q.toReal :=
    (ENNReal.toReal_lt_toReal hpfinite hq).2 hpq
  have hexponent : 0 < 1 / p.toReal - 1 / q.toReal :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hpReal hpqReal)
  have hmajorant := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hexponent).comp hμ
  simp only [Function.comp_def] at hmajorant
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajorant
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hf, hbound] with i hfi hbi
  exact (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq.le hfi).trans
    (mul_le_mul_left hbi _)

/-- The real Lᵖ norms also vanish under a uniform higher-exponent bound.
The estimate is made first in `eLpNorm`, so a nonintegrable function cannot
be mistaken for a function of norm zero. -/
theorem tendsto_lpNorm_of_measure_univ_tendsto_zero
    {p q C : ℝ≥0∞} (hp : 0 < p) (hpq : p < q) (hq : q ≠ ∞) (hC : C ≠ ∞)
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) (μ i))
    (hbound : ∀ᶠ i in l, eLpNorm (f i) q (μ i) ≤ C)
    (hμ : Tendsto (fun i ↦ μ i univ) l (𝓝 0)) :
    Tendsto (fun i ↦ lpNorm (f i) p (μ i)) l (𝓝 0) := by
  have h := tendsto_eLpNorm_of_measure_univ_tendsto_zero hp hpq hq hC hf hbound hμ
  simpa only [Function.comp_def, ENNReal.toReal_zero, toReal_eLpNorm] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

end MeasureTheory
