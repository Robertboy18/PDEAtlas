/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Norm-preserving lifts through nested submodules

Equality with the iterated ambient image gives a continuous linear inclusion
back into the nested subspace, with unchanged vectors and norms.
-/

@[expose] public noncomputable section

namespace Submodule

/-- Lift a subspace of the ambient space through two nested submodules.
The equality of images preserves the ambient vector exactly. -/
def nestedLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Submodule ℝ E) (K : Submodule ℝ H) (V : Submodule ℝ K)
    (S : Submodule ℝ E) (hS : S = (V.map K.subtype).map H.subtype) :
    S →L[ℝ] K := by
  let J := S.subtypeL
  have hp (x : S) : J x ∈ H := by
    change (x : E) ∈ H
    obtain ⟨y, _, hy⟩ := (le_of_eq hS) x.property
    exact hy ▸ y.property
  let P := J.codRestrict H hp
  have hk (x : S) : P x ∈ K := by
    obtain ⟨y, ⟨z, _, hzy⟩, hy⟩ := (le_of_eq hS) x.property
    have hx : P x = (z : H) :=
      Subtype.ext (hy.symm.trans (congrArg Subtype.val hzy).symm)
    exact hx.symm ▸ z.property
  exact P.codRestrict K hk

/-- Forgetting the nested memberships recovers the original ambient vector. -/
@[simp]
theorem nestedLift_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Submodule ℝ E) (K : Submodule ℝ H) (V : Submodule ℝ K)
    (S : Submodule ℝ E) (hS : S = (V.map K.subtype).map H.subtype) (x : S) :
    (((nestedLift H K V S hS x : K) : H) : E) = x.val := rfl

/-- Every vector of the innermost subspace has a norm-preserving preimage. -/
theorem nestedLift_has_preimage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Submodule ℝ E) (K : Submodule ℝ H) (V : Submodule ℝ K)
    (S : Submodule ℝ E) (hS : S = (V.map K.subtype).map H.subtype) (x : V) :
    ∃ y : S, nestedLift H K V S hS y = (x : K) ∧ ‖y‖ = ‖x‖ := by
  have hx : (((x : K) : H) : E) ∈ S := by
    rw [hS]
    exact ⟨(x : K).val, ⟨x.val, x.property, rfl⟩, rfl⟩
  refine ⟨⟨_, hx⟩, ?_, rfl⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

end Submodule
