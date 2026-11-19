/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.BoxIntegral.Partition.Measure
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Complementary level measures on a box

Continuity is needed only on the closed box. Restricting first to that box
makes its sublevel measurable, even if the function is arbitrary outside.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open BoxIntegral MeasureTheory Set

variable {ι : Type*} [Finite ι]

/-- Sublevel and strict superlevel measures add to the volume of the box. -/
theorem measure_restrict_sublevel_add_superlevel
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : Box ι) {u : (ι → ℝ) → ℝ} (hu : ContinuousOn u I.Icc) (t : ℝ) :
    (μ.restrict {x | u x ≤ t}).real I + (μ.restrict {x | t < u x}).real I =
      μ.real I := by
  let S := I.Icc ∩ {x | u x ≤ t}
  have hS : MeasurableSet S :=
    (isClosed_Icc.isClosed_le hu continuousOn_const).measurableSet
  have hlo : (I : Set (ι → ℝ)) ∩ S = (I : Set (ι → ℝ)) ∩ {x | u x ≤ t} := by
    ext x
    constructor
    · exact fun h ↦ ⟨h.1, h.2.2⟩
    · exact fun h ↦ ⟨h.1, Box.coe_subset_Icc h.1, h.2⟩
  have hhi : (I : Set (ι → ℝ)) \ S = (I : Set (ι → ℝ)) ∩ {x | t < u x} := by
    ext x
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      change t < u x
      exact lt_of_not_ge (fun hx ↦ h.2 ⟨Box.coe_subset_Icc h.1, hx⟩)
    · intro h
      refine ⟨h.1, ?_⟩
      intro hx
      have hlo : u x ≤ t := hx.2
      have hhi : t < u x := h.2
      exact (not_le_of_gt hhi) hlo
  rw [measureReal_restrict_apply I.measurableSet_coe,
    measureReal_restrict_apply I.measurableSet_coe, ← hlo, ← hhi]
  exact measureReal_inter_add_sdiff hS (I.measure_coe_lt_top μ).ne

/-- A fixed sublevel fraction leaves at most its complementary fraction above
the same level. -/
theorem measure_restrict_superlevel_le_of_sublevel
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : Box ι) {u : (ι → ℝ) → ℝ} (hu : ContinuousOn u I.Icc)
    (t η : ℝ) (hlo : η * μ.real I ≤ (μ.restrict {x | u x ≤ t}).real I) :
    (μ.restrict {x | t < u x}).real I ≤ (1 - η) * μ.real I := by
  have h := measure_restrict_sublevel_add_superlevel μ I hu t
  calc
    (μ.restrict {x | t < u x}).real I =
        μ.real I - (μ.restrict {x | u x ≤ t}).real I := eq_sub_of_add_eq' h
    _ ≤ μ.real I - η * μ.real I := sub_le_sub_left hlo _
    _ = (1 - η) * μ.real I := by rw [sub_mul, one_mul]

end PDE.Analysis
