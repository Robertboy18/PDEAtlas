/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.CompactCutoff
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Finite decomposition of a test function under an open cover

A smooth partition of unity decomposes any compactly supported test function
into finitely many test functions supported in prescribed members of an open
cover. The identity holds in the test-function space, so linear
distributional identities pass from local tests to the original test without
an additional differentiation argument.
-/

@[expose] public noncomputable section

open Set TopologicalSpace
open scoped Distributions Manifold

namespace TestFunction

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A test function is a finite sum of tests subordinate to any open cover of
its compact support. Neither the cover nor its index type need be countable. -/
theorem exists_finset_sum_subordinate
    (φ : 𝓓((⊤ : Opens E), ℝ)) (U : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (hcover : tsupport φ ⊆ ⋃ i, U i) :
    ∃ s : Finset ι, ∃ ψ : ι → 𝓓((⊤ : Opens E), ℝ),
      (∀ i, tsupport (ψ i) ⊆ U i) ∧ φ = ∑ i ∈ s, ψ i := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) (isClosed_tsupport (φ : E → ℝ)) U hU hcover
  let ψ (i : ι) : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨fun x ↦ ρ i x * φ x, (ρ i).contMDiff.contDiff.mul φ.contDiff,
      φ.hasCompactSupport.mul_left, subset_univ _⟩
  have hs := ρ.locallyFinite.finite_nonempty_inter_compact φ.hasCompactSupport
  refine ⟨hs.toFinset, ψ, ?_, ?_⟩
  · intro i
    exact tsupport_mul_subset_left.trans (hρ i)
  · ext x
    rw [show (∑ i ∈ hs.toFinset, ψ i) x = ∑ i ∈ hs.toFinset, ψ i x from
      by simpa only [FunLike.coeAddMonoidHom_apply, Finset.sum_apply] using
        congrFun (map_sum (FunLike.coeAddMonoidHom 𝓓((⊤ : Opens E), ℝ) E ℝ)
          ψ hs.toFinset) x]
    by_cases hx : φ x = 0
    · simp [ψ, hx]
    · have hxK := subset_tsupport φ hx
      have hfin : Function.support (fun i ↦ ρ i x) ⊆ hs.toFinset := by
        intro i hi
        exact hs.mem_toFinset.mpr ⟨x, hi, hxK⟩
      have hsum : ∑ i ∈ hs.toFinset, ρ i x = 1 :=
        (finsum_eq_sum_of_support_subset _ hfin).symm.trans (ρ.sum_eq_one hxK)
      change φ x = ∑ i ∈ hs.toFinset, ρ i x * φ x
      rw [← Finset.sum_mul, hsum, one_mul]

end TestFunction
