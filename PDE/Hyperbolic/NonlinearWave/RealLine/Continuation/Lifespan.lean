/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Continuation.Gluing
public import PDE.Hyperbolic.NonlinearWave.RealLine.Continuation.Local

/-!
# Global existence or a finite maximal lifespan

Take the supremum of all positive horizons admitting a bounded classical wave.
Overlap uniqueness glues their solutions. If the horizons are unbounded, the
glued wave is global. Otherwise it exists before their positive finite supremum
and is nonextendible there.

For a C¹ reaction and bounded C²/C¹ initial data with bounded first displacement
derivative, local existence starts this construction and uniform continuation
forces unbounded range arbitrarily near any finite maximal endpoint. This is a
one-dimensional classical result; merely local Lipschitz regularity of the
reaction supplies uniqueness and gluing only, not C² local existence.
-/

@[expose] public noncomputable section

open PDE.Common Set
open scoped BoundedContinuousFunction

namespace WaveEquation

/-- A global forward classical wave with bounded range on every finite strip.
The field is C² across the initial slice. -/
structure IsGlobalBoundedClassicalWave
    (f : ℝ → ℝ) (g h : ℝ →ᵇ ℝ) (u : ℝ^2 → ℝ) : Prop where
  regular : ContDiff ℝ 2 u
  equation : ∀ p : ℝ^2, 0 ≤ p 0 → waveOperator (n := 1) u p = -f (u p)
  position : ∀ x : ℝ^1, u (timeSpaceCons 0 x) = g (x 0)
  velocity : ∀ x : ℝ^1, (∂[0] u) (timeSpaceCons 0 x) = h (x 0)
  bounded : ∀ S : NNReal, ∃ R : ℝ, ∀ p : ℝ^2, p 0 ∈ Icc 0 (S : ℝ) → |u p| ≤ R

/-- A global wave restricts to the bounded classical class on every positive
finite interval. -/
theorem IsGlobalBoundedClassicalWave.before {f : ℝ → ℝ} {g h : ℝ →ᵇ ℝ} {u : ℝ^2 → ℝ}
    (hu : IsGlobalBoundedClassicalWave f g h u) {T : ℝ} (hT : 0 < T) :
    IsBoundedClassicalWaveBefore f g h T u :=
  ⟨hT, hu.regular.contDiffOn, fun p hp ↦ hu.equation p hp.1, hu.position, hu.velocity,
    fun S hS ↦ hu.bounded ⟨S, hS.1⟩⟩

/-- The global and finite maximal cases cannot both occur for the same Cauchy
data. The comparison uses uniqueness of classical PDE solutions. -/
theorem IsMaximalBoundedClassicalWaveBefore.not_global {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {g h : ℝ →ᵇ ℝ} {T : ℝ} {u v : ℝ^2 → ℝ} (hu : IsMaximalBoundedClassicalWaveBefore f g h T u)
    (hv : IsGlobalBoundedClassicalWave f g h v) :
    False := by
  have hV := hv.before (T := T + 1) (by linarith [hu.time_pos])
  apply hu.nonextendible (lt_add_one T) hV
  intro p hp
  exact hV.eq_on_overlap hf hu.toIsBoundedClassicalWaveBefore p
    ⟨hp.1, lt_min (hp.2.trans (lt_add_one T)) hp.2⟩

private theorem isBoundedClassicalWaveBefore_of_cofinal
    {f : ℝ → ℝ} {g h : ℝ →ᵇ ℝ} {T : ℝ} {u : ℝ^2 → ℝ} (hT : 0 < T)
    (hcover : ∀ S < T, ∃ A : ℝ, S < A ∧ IsBoundedClassicalWaveBefore f g h A u) :
    IsBoundedClassicalWaveBefore f g h T u := by
  obtain ⟨A, _, hA⟩ := hcover 0 hT
  refine ⟨hT, ?_, ?_, hA.position, hA.velocity, ?_⟩
  · intro p hp
    obtain ⟨B, hpB, hB⟩ := hcover (p 0) hp
    exact (hB.regular.contDiffAt
      ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds hpB))
      |>.contDiffWithinAt
  · intro p hp
    obtain ⟨B, hpB, hB⟩ := hcover (p 0) hp.2
    exact hB.equation p ⟨hp.1, hpB⟩
  · intro S hS
    obtain ⟨B, hSB, hB⟩ := hcover S hS.2
    exact hB.bounded S ⟨hS.1, hSB⟩

private theorem isGlobalBoundedClassicalWave_of_unbounded {f : ℝ → ℝ} {g h : ℝ →ᵇ ℝ} {u : ℝ^2 → ℝ}
    (hcover : ∀ S : ℝ, ∃ A : ℝ, S < A ∧ IsBoundedClassicalWaveBefore f g h A u) :
    IsGlobalBoundedClassicalWave f g h u := by
  obtain ⟨A, _, hA⟩ := hcover 0
  refine ⟨?_, ?_, hA.position, hA.velocity, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro p
    obtain ⟨B, hpB, hB⟩ := hcover (p 0)
    exact hB.regular.contDiffAt
      ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds hpB)
  · intro p hp
    obtain ⟨B, hpB, hB⟩ := hcover (p 0)
    exact hB.equation p ⟨hp, hpB⟩
  · intro S
    obtain ⟨B, hSB, hB⟩ := hcover S
    exact hB.bounded S ⟨S.coe_nonneg, hSB⟩

/-- Given one local classical wave, PDE uniqueness constructs either a
global wave or a wave at a finite maximal endpoint. Local existence is an
explicit input here; local Lipschitz regularity alone is not used to infer it. -/
theorem exists_global_or_maximal_bounded_classicalWave {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {g h : ℝ →ᵇ ℝ} {a : ℝ} {u₀ : ℝ^2 → ℝ} (h₀ : IsBoundedClassicalWaveBefore f g h a u₀) :
    (∃ u : ℝ^2 → ℝ, IsGlobalBoundedClassicalWave f g h u) ∨
      ∃ T : ℝ, ∃ u : ℝ^2 → ℝ, IsMaximalBoundedClassicalWaveBefore f g h T u := by
  let E : Set ℝ := {T | ∃ u : ℝ^2 → ℝ, IsBoundedClassicalWaveBefore f g h T u}
  let v := classicalWaveUnion f g h a u₀
  have hE : E.Nonempty := ⟨a, u₀, h₀⟩
  have hv (T : ℝ) (hT : T ∈ E) : IsBoundedClassicalWaveBefore f g h T v := by
    obtain ⟨u, hu⟩ := hT
    exact isBoundedClassicalWaveBefore_classicalWaveUnion hf h₀ hu
  by_cases hbounded : BddAbove E
  · have hT : 0 < sSup E := h₀.time_pos.trans_le (le_csSup hbounded ⟨u₀, h₀⟩)
    have hsol : IsBoundedClassicalWaveBefore f g h (sSup E) v := by
      apply isBoundedClassicalWaveBefore_of_cofinal hT
      intro S hS
      obtain ⟨A, hA, hSA⟩ := (lt_csSup_iff hbounded hE).mp hS
      exact ⟨A, hSA, hv A hA⟩
    right
    refine ⟨sSup E, v, hsol, ?_⟩
    intro S w hS hw _
    exact (not_lt_of_ge (le_csSup hbounded ⟨w, hw⟩)) hS
  · left
    refine ⟨v, isGlobalBoundedClassicalWave_of_unbounded ?_⟩
    intro S
    obtain ⟨A, hA, hSA⟩ := not_bddAbove_iff.mp hbounded S
    exact ⟨A, hSA, hv A hA⟩

/-- For C¹ reactions and bounded C²/C¹ initial data with bounded first
displacement derivative, there exists either a global classical wave or a
finite maximal classical wave with unbounded range arbitrarily near its endpoint. -/
theorem exists_classicalWave_lifespan_alternative {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {D : ℝ} (hD : ∀ x : ℝ, ‖deriv g x‖ ≤ D) :
    (∃ u : ℝ^2 → ℝ, IsGlobalBoundedClassicalWave f g h u) ∨
      ∃ T : ℝ, ∃ u : ℝ^2 → ℝ, IsMaximalBoundedClassicalWaveBefore f g h T u ∧
        ∀ S ∈ Ico 0 T, ∀ R : ℝ, ∃ p : ℝ^2, p 0 ∈ Ioo S T ∧ R < |u p| := by
  obtain ⟨a, u₀, h₀⟩ := exists_bounded_classicalWaveBefore hf hg hh hD
  rcases exists_global_or_maximal_bounded_classicalWave hf.locallyLipschitz h₀ with
    hglobal | ⟨T, u, hu⟩
  · exact Or.inl hglobal
  · exact Or.inr ⟨T, u, hu, hu.unbounded_range_near_endpoint hf hg hh hD⟩

end WaveEquation
