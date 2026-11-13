/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Lifespan
public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.Forward

/-!
# Finite classical existence horizons in the strict Strauss range

For compactly supported displacement of nonnegative integral and velocity of positive
integral in three dimensions, all classical existence times have a
common finite upper bound when `1 < p < 1 + sqrt 2`. This strengthens absence
of a global solution: arbitrarily long distinct local solutions are excluded.

Finite propagation is derived from their PDE and initial support. No solution
support, mass differential inequality, local existence theorem, continuation
criterion, or smoothness beyond C¹ of the scalar power is an input to the bound.
The maximal-solution corollary explicitly requires one local solution.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common Set

namespace WaveEquation.SmallData.Classical

/-- The strict Strauss obstruction applies to the global classical PDE
without assuming finite propagation: it follows from compact Cauchy support. -/
theorem not_globalSolution_three_of_lt_strauss {g h : ℝ^3 → ℝ} {R p : ℝ} (hg : ContDiff ℝ 3 g)
    (hh : ContDiff ℝ 2 h) (hgs : ∀ x, R < ‖x‖ → g x = 0) (hhs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R)
    (hp : 1 < p) (hcrit : p < 1 + Real.sqrt 2) (hG : 0 ≤ ∫ x, g x) (hpositive : 0 < ∫ x, h x)
    {u : ℝ^4 → ℝ} (hu : IsGlobalSolution (fun z ↦ -|z| ^ p) g h u) :
    False := by
  apply not_global_forward_solution_three_of_lt_strauss hg hh hgs hhs hR hp hcrit
    hG hpositive hu.regular.contDiffOn
    (fun t ht x ↦ by simpa using hu.equation (timeSpaceCons t x) (by simpa using ht.le)) hu.position
  intro x
  rw [← hu.velocity x]
  exact (PDE.hasDerivAt_timeSpaceCons u 0 x
    (hu.regular.differentiable (by norm_num) _)).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Ici 0 0 (by simp))

/-- A common finite upper bound for all classical solution durations.
The statement remains meaningful without assuming any local solution exists;
nonemptiness must be established separately by a local construction. -/
theorem bddAbove_existenceTimes_three_of_lt_strauss {g h : ℝ^3 → ℝ} {R p : ℝ} (hg : ContDiff ℝ 3 g)
    (hh : ContDiff ℝ 2 h) (hgs : ∀ x, R < ‖x‖ → g x = 0) (hhs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R)
    (hp : 1 < p) (hcrit : p < 1 + Real.sqrt 2) (hG : 0 ≤ ∫ x, g x) (hpositive : 0 < ∫ x, h x) :
    BddAbove (existenceTimes (fun z ↦ -|z| ^ p) g h) := by
  by_contra hbound
  obtain ⟨u, hu⟩ := exists_globalSolution_of_unbounded (locallyLipschitz_neg_abs_rpow hp) hbound
  exact not_globalSolution_three_of_lt_strauss hg hh hgs hhs hR hp hcrit hG hpositive hu

/-- Every local classical solution in the strict Strauss range belongs
to a finite maximal classical solution with the same data. The initial local field is explicit. -/
theorem exists_maximalSolution_three_of_lt_strauss {g h : ℝ^3 → ℝ} {R p : ℝ} (hg : ContDiff ℝ 3 g)
    (hh : ContDiff ℝ 2 h) (hgs : ∀ x, R < ‖x‖ → g x = 0) (hhs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R)
    (hp : 1 < p) (hcrit : p < 1 + Real.sqrt 2) (hG : 0 ≤ ∫ x, g x) (hpositive : 0 < ∫ x, h x)
    {a : ℝ} {u₀ : ℝ^4 → ℝ} (h₀ : IsSolutionBefore (fun z ↦ -|z| ^ p) g h a u₀) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, IsMaximalSolutionBefore (fun z ↦ -|z| ^ p) g h T u ∧ ∀ z, z 0 ∈
      Ico 0 a → u z = u₀ z := by
  obtain ⟨u, hu⟩ := exists_maximalSolution_of_bounded (locallyLipschitz_neg_abs_rpow hp)
    (bddAbove_existenceTimes_three_of_lt_strauss hg hh hgs hhs hR hp hcrit hG hpositive) h₀
  refine ⟨_, u, hu, ?_⟩
  have ha : a ≤ sSup (existenceTimes (fun z ↦ -|z| ^ p) g h) :=
    le_csSup (bddAbove_existenceTimes_three_of_lt_strauss hg hh hgs hhs hR hp hcrit hG hpositive)
      ⟨u₀, h₀⟩
  exact fun z hz ↦ hu.toIsSolutionBefore.eq_on_overlap (locallyLipschitz_neg_abs_rpow hp) h₀ z
    ⟨hz.1, lt_min (hz.2.trans_le ha) hz.2⟩

end WaveEquation.SmallData.Classical
