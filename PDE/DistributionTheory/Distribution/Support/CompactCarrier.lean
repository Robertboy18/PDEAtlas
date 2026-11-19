/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Support

/-!
# Compact carriers of distributions

A distribution-like functional has a compact carrier if it vanishes on the complement of some
compact set. This is the compact-support hypothesis used by pushforward and
convolution constructions: unlike compactness of `dsupport` alone, it directly supplies the
vanishing statement needed when testing the distribution.
-/

@[expose] public section

namespace Distribution

variable {α β 𝓕 V : Type*}
variable [FunLike 𝓕 α β] [TopologicalSpace α] [Zero β] [Zero V]

/-- A distribution-like functional has a compact carrier if it vanishes outside a compact set. -/
def HasCompactCarrier (T : 𝓕 → V) : Prop :=
  ∃ K : Set α, IsCompact K ∧ IsVanishingOn T Kᶜ

/-- A closed carrier contains the distributional support. -/
theorem dsupport_subset_of_isVanishingOn_compl
    {T : 𝓕 → V} {K : Set α}
    (hT : IsVanishingOn T Kᶜ) (hK : IsClosed K) :
    dsupport T ⊆ K := by
  intro x hx
  exact (mem_dsupport_iff x).mp hx K hT hK

section T2Space

variable [T2Space α]

/-- A compact carrier makes the distributional support compact. -/
theorem HasCompactCarrier.isCompact_dsupport
    {T : 𝓕 → V} (hT : HasCompactCarrier T) :
    IsCompact (dsupport T) := by
  rcases hT with ⟨K, hK, hvan⟩
  exact hK.of_isClosed_subset isClosed_dsupport
    (dsupport_subset_of_isVanishingOn_compl hvan hK.isClosed)

end T2Space

end Distribution
