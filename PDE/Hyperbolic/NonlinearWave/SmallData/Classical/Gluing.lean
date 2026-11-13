/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Solution
import PDE.FDeriv.Calculus

/-!
# Gluing all classical wave intervals

PDE uniqueness makes the values on overlapping forward intervals
independent of the chosen solution. A fixed initial solution is retained on an
open neighborhood of the initial slice, including negative times. This makes
the glued field C² across zero without imposing a backward PDE or comparing
arbitrary negative-time extensions.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set Filter
open scoped Topology

namespace WaveEquation.SmallData.Classical

variable {n : ℕ}

/-- Glue all admissible forward waves, using a fixed initial solution below
half its positive horizon. Outside the union of the forward intervals, the
value is arbitrary. The regularity and agreement theorems require the initial
field to belong to the classical solution class. -/
def solutionUnion (f : ℝ → ℝ) (g h : ℝ^n → ℝ)
    (a : ℝ) (u₀ : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) : ℝ := by
  classical
  exact if p 0 < a / 2 then u₀ p else
    if hp : ∃ T : ℝ, p 0 < T ∧ ∃ u : ℝ^(n + 1) → ℝ,
        IsSolutionBefore f g h T u then
      hp.choose_spec.2.choose p
    else 0

/-- The union agrees with every admissible wave on its forward interval. -/
theorem solutionUnion_eq [Fact (0 < n)] {f : ℝ → ℝ} (hf : LocallyLipschitz f) {g h : ℝ^n → ℝ}
    {a T : ℝ} {u₀ u : ℝ^(n + 1) → ℝ} (h₀ : IsSolutionBefore f g h a u₀)
    (hu : IsSolutionBefore f g h T u) {p : ℝ^(n + 1)} (hp : p 0 ∈ Ico 0 T) :
    solutionUnion f g h a u₀ p = u p := by
  classical
  unfold solutionUnion
  split_ifs with ha ht
  · exact h₀.eq_on_overlap hf hu p ⟨hp.1, lt_min (ha.trans (half_lt_self h₀.time_pos)) hp.2⟩
  · exact ht.choose_spec.2.choose_spec.eq_on_overlap hf hu p ⟨hp.1, lt_min ht.choose_spec.1 hp.2⟩
  · exact (ht ⟨T, hp.2, u, hu⟩).elim

/-- The fixed initial wave supplies the entire germ below half its horizon,
so the union has two-sided regularity at the initial slice. -/
theorem solutionUnion_eventuallyEq_initial {f : ℝ → ℝ} {g h : ℝ^n → ℝ} {a : ℝ} {u₀ : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hp : p 0 < a / 2) :
    solutionUnion f g h a u₀ =ᶠ[𝓝 p] u₀ := by
  filter_upwards
    [(isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds hp] with q hq
  simp [solutionUnion, show q 0 < a / 2 from hq]

/-- At a strictly positive time, overlap uniqueness identifies the union with
an admissible field on an open spacetime neighborhood. -/
theorem solutionUnion_eventuallyEq [Fact (0 < n)] {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {g h : ℝ^n → ℝ} {a T : ℝ} {u₀ u : ℝ^(n + 1) → ℝ} (h₀ : IsSolutionBefore f g h a u₀)
    (hu : IsSolutionBefore f g h T u) {p : ℝ^(n + 1)} (hp : p 0 ∈ Ioo 0 T) :
    solutionUnion f g h a u₀ =ᶠ[𝓝 p] u := by
  filter_upwards [(isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds hp.1,
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds hp.2] with q hq₀ hqT
  exact solutionUnion_eq hf h₀ hu ⟨hq₀.le, hqT⟩

/-- The glued field is a classical wave on every admissible
interval. Neither a fixed-point identity nor derivative bounds enter the gluing. -/
theorem isSolutionBefore_solutionUnion [Fact (0 < n)] {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {g h : ℝ^n → ℝ} {a T : ℝ} {u₀ u : ℝ^(n + 1) → ℝ} (h₀ : IsSolutionBefore f g h a u₀)
    (hu : IsSolutionBefore f g h T u) :
    IsSolutionBefore f g h T (solutionUnion f g h a u₀) := by
  have hzero (x : ℝ^n) : solutionUnion f g h a u₀ =ᶠ[𝓝 (timeSpaceCons 0 x)] u₀ :=
    solutionUnion_eventuallyEq_initial (by simpa using half_pos h₀.time_pos)
  refine ⟨hu.time_pos, ?_, ?_, ?_, ?_⟩
  · intro p hp
    by_cases hp₀ : 0 < p 0
    · have hr := hu.regular.contDiffAt
        ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds hp)
      exact (hr.congr_of_eventuallyEq
        (solutionUnion_eventuallyEq hf h₀ hu ⟨hp₀, hp⟩)).contDiffWithinAt
    · have hpa : p 0 < a / 2 := (le_of_not_gt hp₀).trans_lt (half_pos h₀.time_pos)
      have hr := h₀.regular.contDiffAt
        ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds
          (hpa.trans (half_lt_self h₀.time_pos)))
      exact (hr.congr_of_eventuallyEq (solutionUnion_eventuallyEq_initial hpa)).contDiffWithinAt
  · intro p hp
    by_cases hp₀ : 0 < p 0
    · have he := solutionUnion_eventuallyEq hf h₀ hu ⟨hp₀, hp.2⟩
      rw [waveOperator_congr_nhds he, he.eq_of_nhds]
      exact hu.equation p hp
    · have hpz : p 0 = 0 := le_antisymm (le_of_not_gt hp₀) hp.1
      have he := solutionUnion_eventuallyEq_initial (f := f) (g := g) (h := h) (u₀ := u₀)
        (show p 0 < a / 2 by rw [hpz]; exact half_pos h₀.time_pos)
      rw [waveOperator_congr_nhds he, he.eq_of_nhds]
      exact h₀.equation p ⟨hp.1, by rw [hpz]; exact h₀.time_pos⟩
  · intro x
    rw [(hzero x).eq_of_nhds, h₀.position]
  · intro x
    rw [PDE.partialDeriv_congr_nhds 0 (hzero x), h₀.velocity]

end WaveEquation.SmallData.Classical
