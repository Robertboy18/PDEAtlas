/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Lifting through an injective map of Banach spaces

If a bounded linear map takes values in the range of an injective bounded map from
a Banach space, its unique linear lift is bounded by the closed graph theorem.
No closed-range hypothesis on the injective map is needed.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A bounded map whose range lies in the range of an injective bounded map
has a bounded linear lift, provided both source spaces are complete. -/
theorem exists_lift_of_injective (A : E →L[𝕜] G) (B : F →L[𝕜] G)
    (hA : Function.Injective A) (hB : ∀ y, ∃ x, A x = B y) :
    ∃ T : F →L[𝕜] E, A.comp T = B := by
  choose t ht using hB
  let L : F →ₗ[𝕜] E :=
    { toFun := t
      map_add' := fun x y ↦ hA (by simp only [ht, map_add])
      map_smul' := fun r y ↦ hA (by simp only [ht, map_smul, RingHom.id_apply]) }
  have hL (y : F) : A (L y) = B y := ht y
  let T : F →L[𝕜] E := ofSeqClosedGraph (g := L) (by
    intro s y x hs hx
    apply hA
    have hleft := (A.continuous.tendsto x).comp hx
    have hright := (B.continuous.tendsto y).comp hs
    simp only [Function.comp_def, hL] at hleft
    exact (tendsto_nhds_unique hleft hright).trans (hL y).symm)
  exact ⟨T, ext hL⟩

end ContinuousLinearMap
