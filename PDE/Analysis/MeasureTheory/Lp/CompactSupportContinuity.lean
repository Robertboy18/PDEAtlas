/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactLpCurry
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Continuity of compactly supported section norms

Joint continuity and a common compact support give continuity of the actual Lp norm.
The sections form a continuous curve in `Lp`, and the norm on `Lp` is continuous.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

/-- Common compact support turns joint continuity into continuity of the actual Lp norm. -/
theorem continuous_lpNorm_of_common_compact_support
    {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure Y} [IsFiniteMeasureOnCompacts μ]
    (K : TopologicalSpace.Compacts Y) [SecondCountableTopologyEither K E]
    {f : X → Y → E} (hf : Continuous f.uncurry)
    (hsupp : ∀ t x, x ∉ K → f t x = 0) :
    Continuous (fun t ↦ lpNorm (f t) p μ) := by
  have hm (t : X) : MemLp (f t) p μ := by
    apply (hf.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
    apply K.isCompact.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ K.isCompact.isClosed
    intro x hx
    by_contra hnot
    exact hx (hsupp t x hnot)
  let : IsFiniteMeasure (μ.restrict (K : Set Y)) :=
    isFiniteMeasure_restrict.mpr K.isCompact.measure_lt_top.ne
  have hc := continuous_Lp_of_common_compact_support K hf hsupp
    (v := fun t ↦ (hm t).toLp (f t)) (fun t ↦ (hm t).coeFn_toLp)
  simpa only [Lp.norm_toLp, lpNorm] using hc.norm

end MeasureTheory
