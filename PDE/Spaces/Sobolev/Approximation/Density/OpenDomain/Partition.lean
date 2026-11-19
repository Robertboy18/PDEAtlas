/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Compactly supported partitions on open domains

A compact exhaustion of an open subset of Euclidean space gives a countable smooth partition
of unity. Each partition function extends smoothly by zero to the ambient space. Local
finiteness holds on the open domain, where the partition sums to one.
-/

@[expose] public noncomputable section

open Function Set TopologicalSpace
open scoped Distributions Manifold

namespace SobolevSpace.Approximation.OpenDomain

/-- Every open domain has a countable partition by ambient test functions supported inside it.
The supports are locally finite in the domain's relative topology. -/
theorem exists_testFunction_partition {n : ℕ} (Ω : Opens (ℝ^n)) :
    ∃ ψ : ℕ → 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      (∀ i, tsupport (ψ i).toFun ⊆ Ω) ∧
      LocallyFinite (fun i ↦ (Subtype.val : Ω → ℝ^n) ⁻¹' support (ψ i).toFun) ∧
      (∀ x : Ω, ∑ᶠ i, (ψ i).toFun x = 1) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let K : CompactExhaustion Ω := CompactExhaustion.choice Ω
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ℝ^n)) isClosed_univ (fun i ↦ interior (K i))
    (fun _ ↦ isOpen_interior) (by
      intro x _
      obtain ⟨i, hi⟩ := K.exists_mem x
      exact mem_iUnion.mpr ⟨i + 1, K.subset_interior_succ i hi⟩)
  have hc (i : ℕ) : HasCompactSupport (ρ i : Ω → ℝ) :=
    (K.isCompact i).of_isClosed_subset isClosed_closure
      ((hρ i).trans interior_subset)
  let ψ : ℕ → 𝓓((⊤ : Opens (ℝ^n)), ℝ) := fun i ↦
    ⟨Subtype.val.extend (ρ i) 0,
      (ContMDiff.extend_zero (hc i) (ρ i).contMDiff).contDiff,
      (hc i).extend_zero continuous_subtype_val, subset_univ _⟩
  have heq (i : ℕ) (x : Ω) : (ψ i).toFun x = ρ i x :=
    congrFun (extend_comp Subtype.val_injective (ρ i) 0) x
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro i
    exact ((hc i).tsupport_extend_zero_subset continuous_subtype_val).trans
      (Subtype.coe_image_subset _ _)
  · convert ρ.locallyFinite using 1
    ext i x
    change (ψ i).toFun x ≠ 0 ↔ ρ i x ≠ 0
    rw [heq]
  · intro x
    simp_rw [heq]
    exact ρ.sum_eq_one (mem_univ x)

end SobolevSpace.Approximation.OpenDomain
