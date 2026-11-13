/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Classical

/-!
# Compact classical extension from finite closure regularity

Interior derivatives that are uniformly continuous up to a bounded graph boundary admit
compactly supported ambient extensions of the same finite order. The induction extends
the coordinate derivatives at the preceding order, assembles their first jet in
the domain, and applies the finite-order reflection construction.

The order `k + 1` and the dimension are positive. The domain is bounded and open, and its
graph boundary is `C^{k+1}`, the order of the data.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open Set

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- Raw `C^{k+1}` data up to a bounded `C^{k+1}` graph boundary have a compact ambient
`C^{k+1}` extension. Neither ambient derivatives nor their extensions are assumed. -/
theorem exists_contDiff_succ_extension (k : ℕ)
    (hf : ContDiffUpToBoundary (k + 1) f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (k + 1) Ω) :
    ∃ g : ℝ^n → ℝ, ContDiff ℝ (k + 1) g ∧ HasCompactSupport g ∧ EqOn g f Ω := by
  induction k generalizing f with
  | zero =>
    exact hf.exists_contDiff_one_extension hopen hbounded
      (Boundary.hasContDiffGraphBoundary_one_iff.mp hgraph)
  | succ k ih =>
    have hgraph' : Boundary.HasContDiffGraphBoundary (k + 1) Ω :=
      hgraph.of_le (by exact_mod_cast Nat.le_succ (k + 1))
    obtain ⟨F, hF, _, hFf⟩ := ih (hf.of_le (Nat.le_succ (k + 1))) hgraph'
    have hi (i : Fin n) : ∃ g : ℝ^n → ℝ,
        ContDiff ℝ (k + 1) g ∧ HasCompactSupport g ∧ EqOn g (∂[i] f) Ω :=
      ih (hf.partialDeriv_of_succ hopen i) hgraph'
    choose g hg _ hgf using hi
    let F' : ℝ^n → (ℝ^n →L[ℝ] ℝ) :=
      fun x ↦ ∑ i, g i x • EuclideanSpace.proj i
    have hF' : ContDiff ℝ (k + 1) F' :=
      ContDiff.sum fun i _ ↦ (hg i).smul_const _
    have hderiv (x : ℝ^n) (hx : x ∈ Ω) : HasFDerivAt F (F' x) x := by
      have hfd : F' x = fderiv ℝ f x := by
        ext v
        simp only [F', sum_apply, smul_apply, smul_eq_mul,
          PDE.fderiv_apply_eq_sum_partialDeriv_mul]
        exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * v i) (hgf i hx)
      rw [hfd]
      apply (hf.contDiffOn.contDiffAt (hopen.mem_nhds hx)).differentiableAt
        (by simp) |>.hasFDerivAt.congr_of_eventuallyEq
      exact hFf.eventuallyEq_of_mem (hopen.mem_nhds hx)
    obtain ⟨atlas, hchart, hinv⟩ :=
      hgraph.exists_c1ExtensionAtlas (by simp) hopen hbounded
    let := atlas
    obtain ⟨G, hG, hcompact, hGF⟩ :=
      Extension.C1.exists_contDiff_succ_extension_of_jet (k + 1)
        hchart hinv hF hF' hderiv
    exact ⟨G, hG, hcompact, hGF.trans hFf⟩

end SobolevSpace.ContDiffUpToBoundary
