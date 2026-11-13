/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.ClassicalHigherOrder

/-!
# Finite-dimensional classical extension with prescribed closure values

Scalar finite-order reflection extends the components. Continuity of the given map
on the closure identifies the resulting extension there, including its boundary values.
The hypotheses are interior classical derivatives and their uniform continuity.
-/

@[expose] public noncomputable section

namespace SobolevSpace

open Set

variable {n m : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ^m}

/-- A finite-dimensional map with raw finite classical closure regularity has an
ambient extension of the same order agreeing with its prescribed closure values. -/
theorem exists_contDiff_succ_extension_vector (k : ℕ)
    (hu : ∀ i, ContDiffUpToBoundary (k + 1) (fun x ↦ u x i) Ω)
    (hc : ContinuousOn u (closure Ω)) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (k + 1) Ω) :
    ∃ U : ℝ^n → ℝ^m, ContDiff ℝ (k + 1) U ∧ EqOn U u (closure Ω) := by
  choose g hg _ hgu using fun i ↦
    (hu i).exists_contDiff_succ_extension k hopen hbounded hgraph
  let U : ℝ^n → ℝ^m := fun x ↦ WithLp.toLp 2 (fun i ↦ g i x)
  have hU : ContDiff ℝ (k + 1) U := contDiff_euclidean.mpr hg
  have heq : EqOn U u Ω := by
    intro x hx
    ext i
    exact hgu i hx
  exact ⟨U, hU, heq.of_subset_closure hU.continuous.continuousOn hc
    subset_closure Subset.rfl⟩

end SobolevSpace
