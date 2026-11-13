/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Classical

/-!
# Vanishing boundary values and distance to the complement

A compact classical extension supplies a Lipschitz bound. Evaluating at a
nearest frontier point then controls a function with zero boundary values.
-/

@[expose] public noncomputable section

open Set

namespace SobolevSpace.ContDiffUpToBoundary

/-- Classical first-order closure regularity and zero boundary values imply
linear decay with distance to the complement on a bounded graph domain. -/
theorem exists_norm_le_mul_infDist_compl
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}
    (hf : ContDiffUpToBoundary 1 f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : SobolevSpace.Boundary.HasC1GraphBoundary Ω)
    (hcont : ContinuousOn f (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, f x = 0) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ Ω, ‖f x‖ ≤ L * Metric.infDist x Ωᶜ := by
  let : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  obtain ⟨g, hg, hgc, hgf⟩ := hf.exists_contDiff_one_extension hopen hbounded hgraph
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hgf' : EqOn g f (closure Ω) :=
    hgf.of_subset_closure hg.continuous.continuousOn hcont subset_closure Subset.rfl
  refine ⟨(K : ℝ) + 1, by positivity, fun x hx ↦ ?_⟩
  have hΩ : Ω ≠ univ := by
    intro heq
    have hc := hbounded.isCompact_closure
    rw [heq, closure_univ] at hc
    exact hc.ne_univ rfl
  obtain ⟨y, hy, hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hΩ
  have hgy : g y = 0 := (hgf' (frontier_subset_closure hy)).trans (hzero y hy)
  have h := hK.dist_le_mul x y
  rw [hgf hx, hgy, dist_zero_right, ← hxy] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) Metric.infDist_nonneg)

end SobolevSpace.ContDiffUpToBoundary
