/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Bounded inverses of closed partial linear maps

A closed partial linear map between Banach spaces has a bounded ambient inverse
when it is bijective on its domain. The construction uses Mathlib's `LinearPMap.inverse`
and the closed graph theorem. The operator domain need not be complete in the
norm inherited from the ambient space.
-/

@[expose] public section

noncomputable section

namespace LinearPMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (B : E →ₗ.[𝕜] F)

/-- Extend the native partial inverse to all data in the range of a surjective operator. -/
def inverseLinearMap (hB : Function.Surjective B.toFun) : F →ₗ[𝕜] E :=
  B.inverse.toFun.comp ((LinearMap.id : F →ₗ[𝕜] F).codRestrict B.inverse.domain
    fun y ↦ by
      rw [inverse_domain]
      exact hB y)

/-- Totalizing a surjective operator's inverse preserves its entire graph. -/
theorem inverseLinearMap_graph (hB : Function.Surjective B.toFun) :
    (B.inverseLinearMap hB).graph = B.inverse.graph := by
  ext ⟨y, x⟩
  rw [LinearMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · intro h
    exact ⟨⟨y, by rw [inverse_domain]; exact hB y⟩, rfl, h.symm⟩
  · rintro ⟨z, rfl, h⟩
    exact h.symm

variable [CompleteSpace E] [CompleteSpace F]

/-- The bounded ambient inverse of a closed operator bijective on its natural domain. -/
def boundedInverse (hclosed : B.IsClosed) (hB : Function.Bijective B.toFun) : F →L[𝕜] E :=
  ContinuousLinearMap.ofIsClosedGraph (g := B.inverseLinearMap hB.2) <| by
    rw [B.inverseLinearMap_graph]
    exact (inverse_closed_iff (ker_eq_bot.mpr hB.1)).2 hclosed

/-- The bounded inverse recovers every vector in the original operator domain. -/
@[simp]
theorem boundedInverse_apply (hclosed : B.IsClosed) (hB : Function.Bijective B.toFun)
    (x : B.domain) :
    B.boundedInverse hclosed hB (B x) = x :=
  inverse_apply_eq (ker_eq_bot.mpr hB.1) rfl

/-- Every value of the bounded inverse lies in the original operator domain. -/
theorem boundedInverse_mem_domain (hclosed : B.IsClosed) (hB : Function.Bijective B.toFun)
    (y : F) :
    B.boundedInverse hclosed hB y ∈ B.domain := by
  obtain ⟨x, rfl⟩ := hB.2 y
  simpa only [toFun_eq_coe, boundedInverse_apply] using x.property

/-- Applying the partial operator to its bounded inverse recovers arbitrary ambient data. -/
@[simp]
theorem apply_boundedInverse (hclosed : B.IsClosed) (hB : Function.Bijective B.toFun)
    (y : F) :
    B ⟨B.boundedInverse hclosed hB y, B.boundedInverse_mem_domain hclosed hB y⟩ = y := by
  obtain ⟨x, rfl⟩ := hB.2 y
  simp only [toFun_eq_coe, boundedInverse_apply]

/-- A domain-valued right inverse agrees with the constructed bounded inverse. -/
theorem eq_boundedInverse (hclosed : B.IsClosed) (hB : Function.Bijective B.toFun)
    (R : F →L[𝕜] E) (hR_domain : ∀ y : F, R y ∈ B.domain)
    (hR : ∀ y : F, B ⟨R y, hR_domain y⟩ = y) :
    R = B.boundedInverse hclosed hB := by
  ext y
  simpa only [hR] using (B.boundedInverse_apply hclosed hB ⟨R y, hR_domain y⟩).symm

end LinearPMap
