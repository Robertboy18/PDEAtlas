/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Analysis.MeasureTheory.Lp.CompactSupportContinuity
public import PDE.Common.Euclidean.SpaceTime

/-!
# Continuity of spacetime section norms

Joint continuity on an open time band and common compact spatial support imply
continuity of actual Lp section norms on each interior closed time interval.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE PDE.Common
open scoped ENNReal

namespace PDE.Analysis

/-- A continuous field with a common compact spatial support has continuous actual
section norms on each interior closed time interval. -/
theorem continuousOn_lpNorm_of_common_spatial_support
    {n : ℕ} {v : ℝ^(n + 1) → ℝ} {T s τ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hv : ContinuousOn v {q | 0 < q 0 ∧ q 0 < T})
    (K : TopologicalSpace.Compacts (ℝ^n))
    (hsupp : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^n, x ∉ K → v (timeSpaceCons t x) = 0)
    (hs : 0 < s) (hτ : τ < T) :
    ContinuousOn (fun t ↦ lpNorm (fun x ↦ v (timeSpaceCons t x)) p volume) (Icc s τ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply MeasureTheory.continuous_lpNorm_of_common_compact_support K
    (f := fun t : Icc s τ ↦ fun x ↦ v (timeSpaceCons t x))
  · apply hv.comp_continuous
      ((timeSpaceContinuousLinearEquiv n).symm.continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
    intro q
    simpa using And.intro (hs.trans_le q.1.property.1) (q.1.property.2.trans_lt hτ)
  · intro t x hx
    exact hsupp t ⟨hs.trans_le t.property.1, t.property.2.trans_lt hτ⟩ x hx

end PDE.Analysis
