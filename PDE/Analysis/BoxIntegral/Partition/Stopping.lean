/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.BoxIntegral.Partition.Contraction

/-!
# Finite stopping covers under contracting subdivision

A stopping rule selects pairwise disjoint subboxes covering a prescribed
set. Every selected box retains a smallness predicate and a second predicate
forced either by a nonsmall child or by local separation. The subdivision may
contract different coordinates at different rates.
-/

@[expose] public noncomputable section

namespace BoxIntegral.Prepartition

open Set
open scoped Topology

variable {ι : Type*}

/-- A contracting subdivision and a local stopping rule produce a finite
prepartition covering `E ∩ I`. No measure, equal scaling, or fixed aspect ratio
is required. The auxiliary predicate records properties preserved by splitting. -/
theorem exists_stopping_cover
    (I : Box ι) (division : ι → ℝ) (hdivision : ∀ i, 1 < division i)
    (split : ∀ J : Box ι, Prepartition J)
    (hpartition : ∀ J, (split J).IsPartition)
    (hside : ∀ J K, K ∈ split J → ∀ i,
      K.upper i - K.lower i = (J.upper i - J.lower i) / division i)
    (E : Set (ι → ℝ)) (P small good : Box ι → Prop) (hPI : P I)
    (hPsplit : ∀ J ≤ I, P J → ∀ K ∈ split J, P K)
    (hstop : ∀ J ≤ I, P J → ∀ K ∈ split J, ¬small K → good J)
    (hlocal : ∀ z ∈ I.Icc, ∃ U ∈ 𝓝[I.Icc] z, ∀ J ≤ I, ∀ m : ℕ,
      z ∈ J.Icc → J.Icc ⊆ U →
      (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / division i ^ m) →
      P J → good J ∨ Disjoint (J : Set (ι → ℝ)) E)
    (hsmall : small I) :
    ∃ π : Prepartition I, E ∩ (I : Set (ι → ℝ)) ⊆ π.iUnion ∧
      ∀ J ∈ π, P J ∧ small J ∧ good J := by
  classical
  apply I.subbox_induction_on_division division hdivision split hside
    (p := fun J ↦ P J → small J →
      ∃ π : Prepartition J, E ∩ (J : Set (ι → ℝ)) ⊆ π.iUnion ∧
        ∀ K ∈ π, P K ∧ small K ∧ good K) ?_ ?_ hPI hsmall
  · intro J hJI hchildren hPJ hJsmall
    by_cases hbad : ∃ K ∈ split J, ¬small K
    · obtain ⟨K, hK, hKbad⟩ := hbad
      refine ⟨single J J le_rfl, ?_, ?_⟩
      · rw [iUnion_single]
        exact inter_subset_right
      · intro Q hQ
        have hQJ : Q = J := (mem_single le_rfl).mp hQ
        subst Q
        exact ⟨hPJ, hJsmall, hstop J hJI hPJ K hK hKbad⟩
    · have hex (K : Box ι) :
          ∃ π : Prepartition K, K ∈ split J →
            E ∩ (K : Set (ι → ℝ)) ⊆ π.iUnion ∧
              ∀ Q ∈ π, P Q ∧ small Q ∧ good Q := by
        by_cases hK : K ∈ split J
        · obtain ⟨π, hcover, hgood⟩ := hchildren K hK (hPsplit J hJI hPJ K hK)
            (by_contra fun h ↦ hbad ⟨K, hK, h⟩)
          exact ⟨π, fun _ ↦ ⟨hcover, hgood⟩⟩
        · exact ⟨⊥, fun h ↦ False.elim (hK h)⟩
      choose π hπ using hex
      refine ⟨(split J).biUnion π, ?_, ?_⟩
      · intro x hx
        have hxsplit : x ∈ (split J).iUnion := by
          rw [(hpartition J).iUnion_eq]
          exact hx.2
        obtain ⟨K, hK, hxK⟩ := (split J).mem_iUnion.mp hxsplit
        rw [iUnion_biUnion]
        exact Set.mem_iUnion.mpr ⟨K,
          Set.mem_iUnion.mpr ⟨hK, (hπ K hK).1 ⟨hx.1, hxK⟩⟩⟩
      · intro Q hQ
        obtain ⟨K, hK, hQK⟩ := (split J).mem_biUnion.mp hQ
        exact (hπ K hK).2 Q hQK
  · intro z hz
    obtain ⟨U, hU, hterminal⟩ := hlocal z hz
    refine ⟨U, hU, ?_⟩
    intro J hJI m hzJ hJU hlength hPJ hJsmall
    rcases hterminal J hJI m hzJ hJU hlength hPJ with hgood | hdisjoint
    · refine ⟨single J J le_rfl, ?_, ?_⟩
      · rw [iUnion_single]
        exact inter_subset_right
      · intro K hK
        have hKJ : K = J := (mem_single le_rfl).mp hK
        subst K
        exact ⟨hPJ, hJsmall, hgood⟩
    · refine ⟨⊥, ?_, by simp⟩
      rw [iUnion_bot, hdisjoint.symm.inter_eq]

end BoxIntegral.Prepartition
