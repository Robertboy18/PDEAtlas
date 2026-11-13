/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.BoxIntegral.Partition.Split
public import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import CAS.ExactTactic

/-!
# Anisotropic subdivision of boxes

Bisecting one coordinate after the usual central subdivision quarters that side and
halves all other sides. The pieces form Mathlib `BoxIntegral.Prepartition`s, so Mathlib's
partition lemmas give their covering and refinement properties.
-/

@[expose] public noncomputable section

open Function Set

namespace BoxIntegral.Prepartition

variable {ι : Type*} {I J : Box ι}

open scoped Classical in
/-- Bisecting a box in one coordinate halves that side and preserves the others. -/
theorem upper_sub_lower_of_mem_split_midpoint (j : ι)
    (hJ : J ∈ split I j ((I.lower j + I.upper j) / 2)) (i : ι) :
    J.upper i - J.lower i =
      if i = j then (I.upper i - I.lower i) / 2 else I.upper i - I.lower i := by
  classical
  have hmid : (I.lower j + I.upper j) / 2 ∈ Ioo (I.lower j) (I.upper j) :=
    ⟨left_lt_add_div_two.2 (I.lower_lt_upper j),
      add_div_two_lt_right.2 (I.lower_lt_upper j)⟩
  rcases mem_split_iff.1 hJ with hJ | hJ
  · rw [Box.splitLower_def hmid] at hJ
    cases WithBot.coe_injective hJ
    by_cases hij : i = j
    · subst i
      simp only [update_self, ↓reduceIte]
      cas
    · simp [hij]
  · rw [Box.splitUpper_def hmid] at hJ
    cases WithBot.coe_injective hJ
    by_cases hij : i = j
    · subst i
      simp only [update_self, ↓reduceIte]
      cas
    · simp [hij]

variable [Fintype ι]

/-- Central subdivision followed by a second bisection in the selected coordinate. -/
def splitCenterTwiceAt (I : Box ι) (j : ι) : Prepartition I :=
  (splitCenter I).biUnion fun J ↦ split J j ((J.lower j + J.upper j) / 2)

/-- The anisotropic subdivision covers the original box. -/
theorem isPartition_splitCenterTwiceAt (I : Box ι) (j : ι) :
    IsPartition (splitCenterTwiceAt I j) :=
  (isPartition_splitCenter I).biUnion fun _ _ ↦ isPartitionSplit _ _ _

open scoped Classical in
/-- Anisotropic children have one quarter of the selected side and one half of every
other side. In particular, parabolic boxes retain their time-to-space-squared ratio. -/
theorem upper_sub_lower_of_mem_splitCenterTwiceAt (j : ι)
    (hJ : J ∈ splitCenterTwiceAt I j) (i : ι) :
    J.upper i - J.lower i = (I.upper i - I.lower i) / (if i = j then 4 else 2) := by
  classical
  obtain ⟨K, hK, hJK⟩ := (splitCenter I).mem_biUnion.1 hJ
  rw [upper_sub_lower_of_mem_split_midpoint j hJK,
    upper_sub_lower_of_mem_splitCenter hK]
  split_ifs <;> cas

end BoxIntegral.Prepartition
