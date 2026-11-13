/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Topological compact-approximation criteria

General compact-operator and finite-rank facts for the Fréchet-Kolmogorov
argument: a bounded family uniformly approximable by compact operators is
totally bounded, finite sums of compact maps are compact, and real rank-one
operators are compact.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace Rellich

open Set
open scoped Topology InnerProductSpace RealInnerProductSpace

section CompactApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded family uniformly approximable by compact linear operators is
totally bounded.  This separates the topological part of
Fréchet-Kolmogorov from the analytic construction of smoothing
approximations. -/
theorem totallyBounded_of_uniform_compact_approximation
    (S : Set E) (hS : Bornology.IsBounded S)
    (happrox : ∀ ε > 0, ∃ A : E →L[ℝ] E,
      IsCompactOperator A ∧ ∀ x ∈ S, ‖A x - x‖ < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨A, hAcompact, hAclose⟩ := happrox (ε / 2) hε2
  obtain ⟨K, hKcompact, hAK⟩ :=
    hAcompact.image_subset_compact_of_bounded hS
  obtain ⟨t, htFinite, hKcover⟩ :=
    (Metric.totallyBounded_iff.mp hKcompact.totallyBounded) (ε / 2) hε2
  refine ⟨t, htFinite, fun x hx ↦ ?_⟩
  have hAxK : A x ∈ K := hAK ⟨x, hx, rfl⟩
  have hAxCover := hKcover hAxK
  simp only [Set.mem_iUnion] at hAxCover ⊢
  obtain ⟨y, hyT, hAxy⟩ := hAxCover
  refine ⟨y, hyT, ?_⟩
  calc
    dist x y ≤ dist x (A x) + dist (A x) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add
      (by simpa [dist_eq_norm, norm_sub_rev] using hAclose x hx) hAxy
    _ = ε := by ring

end CompactApproximation

section FiniteSums

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite sum of compact continuous linear maps is compact. -/
theorem isCompactOperator_finset_sum
    {ι : Type*} (s : Finset ι) (A : ι → E →L[ℝ] F)
    (hA : ∀ i ∈ s, IsCompactOperator (A i)) :
    IsCompactOperator
      ((∑ i ∈ s, A i : E →L[ℝ] F) : E → F) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (isCompactOperator_zero :
        IsCompactOperator (0 : E → F))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hA i (by simp)).add
        (ih fun j hj ↦ hA j (by simp [hj]))

end FiniteSums

section FiniteRank

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real Hilbert-space rank-one operator is compact because it factors
through the one-dimensional space `ℝ`. -/
theorem isCompactOperator_rankOne_real (x y : E) :
    IsCompactOperator (InnerProductSpace.rankOne ℝ x y) := by
  rw [InnerProductSpace.rankOne_def']
  exact
    (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ y)).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℝ x)

end FiniteRank

end Rellich
end GraphSpace
end SobolevSpace
