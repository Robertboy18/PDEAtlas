/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Gluing

/-!
# The union of classical solution intervals

Unbounded existence times give a global classical solution by overlap
uniqueness. If existence times are nonempty and bounded, their positive finite
supremum is attained by a solution on the open time interval and is maximal.
The nonemptiness input is a local solution, not a local existence axiom.
-/

@[expose] public noncomputable section

open PDE.Common Set
open scoped Topology

namespace WaveEquation.SmallData.Classical

variable {n : ℕ}

/-- A global forward classical solution, with an arbitrary regular backward
extension and with the displacement and velocity traces. -/
structure IsGlobalSolution
    (f : ℝ → ℝ) (g h : ℝ^n → ℝ) (u : ℝ^(n + 1) → ℝ) : Prop where
  regular : ContDiff ℝ 2 u
  equation : ∀ p, 0 ≤ p 0 → waveOperator u p = -f (u p)
  position : ∀ x, u (timeSpaceCons 0 x) = g x
  velocity : ∀ x, (∂[0] u) (timeSpaceCons 0 x) = h x

/-- A finite maximal classical endpoint means nonextendibility of the
field among solutions with the same Cauchy data. -/
structure IsMaximalSolutionBefore
    (f : ℝ → ℝ) (g h : ℝ^n → ℝ) (T : ℝ) (u : ℝ^(n + 1) → ℝ) : Prop
    extends IsSolutionBefore f g h T u where
  nonextendible : ∀ {S : ℝ} {v : ℝ^(n + 1) → ℝ}, T < S →
    IsSolutionBefore f g h S v →
    (∀ p, p 0 ∈ Ico 0 T → v p = u p) → False

/-- Every positive finite restriction of a global solution is admissible. -/
theorem IsGlobalSolution.before {f : ℝ → ℝ} {g h : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : IsGlobalSolution f g h u) {T : ℝ} (hT : 0 < T) :
    IsSolutionBefore f g h T u :=
  ⟨hT, hu.regular.contDiffOn, fun p hp ↦ hu.equation p hp.1, hu.position, hu.velocity⟩

private theorem isSolutionBefore_of_cofinal {f : ℝ → ℝ} {g h : ℝ^n → ℝ} {T : ℝ} {u : ℝ^(n + 1) → ℝ}
    (hT : 0 < T) (hcover : ∀ S < T, ∃ A : ℝ, S < A ∧ IsSolutionBefore f g h A u) :
    IsSolutionBefore f g h T u := by
  obtain ⟨A, _, hA⟩ := hcover 0 hT
  refine ⟨hT, ?_, ?_, hA.position, hA.velocity⟩
  · intro p hp
    obtain ⟨B, hpB, hB⟩ := hcover (p 0) hp
    exact (hB.regular.contDiffAt
      ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds hpB))
      |>.contDiffWithinAt
  · intro p hp
    obtain ⟨B, hpB, hB⟩ := hcover (p 0) hp.2
    exact hB.equation p ⟨hp.1, hpB⟩

private theorem isGlobalSolution_of_unbounded {f : ℝ → ℝ} {g h : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hcover : ∀ S : ℝ, ∃ A : ℝ, S < A ∧ IsSolutionBefore f g h A u) :
    IsGlobalSolution f g h u := by
  obtain ⟨A, _, hA⟩ := hcover 0
  refine ⟨?_, ?_, hA.position, hA.velocity⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro p
    obtain ⟨B, hpB, hB⟩ := hcover (p 0)
    exact hB.regular.contDiffAt
      ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds hpB)
  · intro p hp
    obtain ⟨B, hpB, hB⟩ := hcover (p 0)
    exact hB.equation p ⟨hp, hpB⟩

/-- Arbitrarily long classical solutions with common data glue to a
global solution. Agreement on overlaps follows from the PDE. -/
theorem exists_globalSolution_of_unbounded [Fact (0 < n)] {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {g h : ℝ^n → ℝ} (hunbounded : ¬ BddAbove (existenceTimes f g h)) :
    ∃ u, IsGlobalSolution f g h u := by
  obtain ⟨a, ⟨u₀, h₀⟩, _⟩ := not_bddAbove_iff.mp hunbounded 0
  refine ⟨solutionUnion f g h a u₀, isGlobalSolution_of_unbounded ?_⟩
  intro S
  obtain ⟨A, ⟨u, hu⟩, hSA⟩ := not_bddAbove_iff.mp hunbounded S
  exact ⟨A, hSA, isSolutionBefore_solutionUnion hf h₀ hu⟩

/-- A bounded nonempty set of classical existence times has a
solution up to its positive supremum, nonextendible there. This theorem starts
from the supplied local field and does not infer its existence from regularity
of the reaction alone. -/
theorem exists_maximalSolution_of_bounded [Fact (0 < n)] {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {g h : ℝ^n → ℝ} (hbounded : BddAbove (existenceTimes f g h)) {a : ℝ} {u₀ : ℝ^(n + 1) → ℝ}
    (h₀ : IsSolutionBefore f g h a u₀) :
    ∃ u, IsMaximalSolutionBefore f g h (sSup (existenceTimes f g h)) u := by
  let E := existenceTimes f g h
  have hE : E.Nonempty := ⟨a, u₀, h₀⟩
  have hT : 0 < sSup E := h₀.time_pos.trans_le (le_csSup hbounded ⟨u₀, h₀⟩)
  let v := solutionUnion f g h a u₀
  have hsol : IsSolutionBefore f g h (sSup E) v := by
    apply isSolutionBefore_of_cofinal hT
    intro S hS
    obtain ⟨A, ⟨u, hu⟩, hSA⟩ := (lt_csSup_iff hbounded hE).mp hS
    exact ⟨A, hSA, isSolutionBefore_solutionUnion hf h₀ hu⟩
  refine ⟨v, hsol, ?_⟩
  intro S w hS hw _
  exact (not_lt_of_ge (le_csSup hbounded ⟨w, hw⟩)) hS

end WaveEquation.SmallData.Classical
