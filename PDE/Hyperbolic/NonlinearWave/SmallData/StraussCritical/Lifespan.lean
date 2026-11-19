/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.Nonexistence
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.FinitePropagation
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Lifespan

/-!
# A common finite classical duration at the critical Strauss exponent

Finite propagation removes the support-cone hypothesis from the global obstruction. Local uniqueness
and gluing rule out an unbounded family of distinct classical solution durations.

The maximal-solution corollary explicitly starts with a local solution.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common Set

namespace WaveEquation.SmallData.Classical

/-- Critical Strauss nonexistence from compact data alone: finite propagation
is derived from the global equation and Cauchy traces. -/
theorem not_globalSolution_three_at_strauss {h : ℝ^3 → ℝ} {R : ℝ} (hh : ContDiff ℝ 2 h)
    (hhn : ∀ x, 0 ≤ h x) (hs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R) (hpositive : 0 < ∫ x, h x)
    {u : ℝ^4 → ℝ} (hu : IsGlobalSolution (fun z ↦ -|z| ^ (1 + Real.sqrt 2)) (fun _ ↦ 0) h u) :
    False := by
  have hp : 1 < 1 + Real.sqrt 2 := lt_trans one_lt_two two_lt_one_add_sqrt_two
  have hsupport : HasForwardSupport u R :=
    fun t ht x hx ↦ (hu.before (T := t + 1) (by linarith)).eq_zero_of_norm_gt
      (locallyLipschitz_neg_abs_rpow hp)
      (by simp [Real.zero_rpow (by linarith : 1 + Real.sqrt 2 ≠ 0)])
      (fun _ _ ↦ rfl) hs ⟨ht, lt_add_one t⟩ x hx
  exact not_global_cauchy_solution_three_at_strauss hu.regular hsupport hh hhn hR
    (fun t ht x ↦ by simpa using hu.equation (timeSpaceCons t x) (by simpa using ht.le))
    hu.position hu.velocity hpositive

/-- All classical solution durations have a common finite upper bound
at `p=1+√2`. No support cone or desired mass estimate is an input. -/
theorem bddAbove_existenceTimes_three_at_strauss {h : ℝ^3 → ℝ} {R : ℝ} (hh : ContDiff ℝ 2 h)
    (hhn : ∀ x, 0 ≤ h x) (hs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R) (hpositive : 0 < ∫ x, h x) :
    BddAbove (existenceTimes (fun z ↦ -|z| ^ (1 + Real.sqrt 2)) (fun _ ↦ 0) h) := by
  by_contra hbound
  obtain ⟨u, hu⟩ := exists_globalSolution_of_unbounded
    (locallyLipschitz_neg_abs_rpow (lt_trans one_lt_two two_lt_one_add_sqrt_two)) hbound
  exact not_globalSolution_three_at_strauss hh hhn hs hR hpositive hu

/-- A finite positive duration bound stated with the classical PDE,
regularity, and initial traces, with no solution support assumption. -/
theorem exists_classical_duration_bound_three_at_strauss {h : ℝ^3 → ℝ} {R : ℝ} (hh : ContDiff ℝ 2 h)
    (hhn : ∀ x, 0 ≤ h x) (hs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R) (hpositive : 0 < ∫ x, h x) :
    ∃ B : ℝ, 0 < B ∧ ∀ T : ℝ, 0 < T → ∀ u : ℝ^4 → ℝ,
      ContDiffOn ℝ 2 u {z | z 0 < T} →
      (∀ z, z 0 ∈ Ico 0 T → waveOperator u z = |u z| ^ (1 + Real.sqrt 2)) →
      (∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0) →
      (∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) → T ≤ B := by
  obtain ⟨B, hB⟩ := bddAbove_existenceTimes_three_at_strauss hh hhn hs hR hpositive
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro T hT u hu hPDE hzero hinitial
  have hsol : IsSolutionBefore (fun z ↦ -|z| ^ (1 + Real.sqrt 2)) (fun _ ↦ 0) h T u :=
    ⟨hT, hu, fun z hz ↦ by simpa only [neg_neg] using hPDE z hz, hzero, hinitial⟩
  exact (hB ⟨u, hsol⟩).trans (le_max_left _ _)

/-- Any local solution at the critical Strauss power embeds in a finite
maximal classical solution. The local field is explicit, and is not constructed here. -/
theorem exists_maximalSolution_three_at_strauss {h : ℝ^3 → ℝ} {R : ℝ} (hh : ContDiff ℝ 2 h)
    (hhn : ∀ x, 0 ≤ h x) (hs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R) (hpositive : 0 < ∫ x, h x)
    {a : ℝ} {u₀ : ℝ^4 → ℝ}
    (h₀ : IsSolutionBefore (fun z ↦ -|z| ^ (1 + Real.sqrt 2)) (fun _ ↦ 0) h a u₀) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, IsMaximalSolutionBefore (fun z ↦ -|z| ^ (1 + Real.sqrt 2)) (fun _ ↦ 0) h
      T u ∧ ∀ z, z 0 ∈ Ico 0 a → u z = u₀ z := by
  have hf := locallyLipschitz_neg_abs_rpow (lt_trans one_lt_two two_lt_one_add_sqrt_two)
  have hb := bddAbove_existenceTimes_three_at_strauss hh hhn hs hR hpositive
  obtain ⟨u, hu⟩ := exists_maximalSolution_of_bounded hf hb h₀
  refine ⟨_, u, hu, ?_⟩
  have ha : a ≤ sSup (existenceTimes
      (fun z ↦ -|z| ^ (1 + Real.sqrt 2)) (fun _ ↦ 0) h) := le_csSup hb ⟨u₀, h₀⟩
  exact fun z hz ↦ hu.toIsSolutionBefore.eq_on_overlap hf h₀ z
    ⟨hz.1, lt_min (hz.2.trans_le ha) hz.2⟩

end WaveEquation.SmallData.Classical
