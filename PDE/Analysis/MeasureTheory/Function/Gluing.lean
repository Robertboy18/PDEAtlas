/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Gluing almost everywhere equal local functions

Functions on a countable measurable cover glue when their representatives agree
almost everywhere on each overlap. Countability gives a single exceptional null
set for all pairs. Outside it, any choice of a cover member gives the same value.
Measurability of the glued function follows from its local almost everywhere
equalities, without requiring a measurable choice of cover member.
-/

@[expose] public noncomputable section

open Set TopologicalSpace

namespace MeasureTheory

variable {α β ι : Type*} [MeasurableSpace α] [Countable ι]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [Nonempty β]

/-- Compatible local representatives on a countable measurable cover have one
almost everywhere strongly measurable representative on their union. -/
theorem exists_aestronglyMeasurable_of_ae_eq_on_intersections
    {μ : Measure α} (U : ι → Set α) (hU : ∀ i, MeasurableSet (U i))
    (f : ι → α → β) (hf : ∀ i, AEStronglyMeasurable (f i) (μ.restrict (U i)))
    (hpair : ∀ i j, f i =ᵐ[μ.restrict (U i ∩ U j)] f j) :
    ∃ g : α → β, AEStronglyMeasurable g (μ.restrict (⋃ i, U i)) ∧
      ∀ i, g =ᵐ[μ.restrict (U i)] f i := by
  classical
  let g (x : α) : β :=
    if hx : ∃ i, x ∈ U i then f hx.choose x else Classical.arbitrary β
  have hall : ∀ᵐ x ∂μ, ∀ i j, x ∈ U i ∩ U j → f i x = f j x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
      (ae_restrict_iff' ((hU i).inter (hU j))).mp (hpair i j)
  have hlocal (i : ι) : g =ᵐ[μ.restrict (U i)] f i := by
    apply (ae_restrict_iff' (hU i)).mpr
    filter_upwards [hall] with x hx hxi
    have hmem : ∃ j, x ∈ U j := ⟨i, hxi⟩
    dsimp only [g]
    rw [dite_eq_left hmem]
    exact hx hmem.choose i ⟨hmem.choose_spec, hxi⟩
  exact ⟨g, AEStronglyMeasurable.iUnion fun i ↦ (hf i).congr (hlocal i).symm, hlocal⟩

end MeasureTheory
