/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Exhausting a half-line by bounded open intervals

A countable exhaustion transfers almost-everywhere assertions and strong measurability
from finite intervals to a half-line. The target of a strongly measurable function need
not be separable.
-/

@[expose] public section

open Set TopologicalSpace

namespace MeasureTheory

private theorem iUnion_Ioo_nat_add (a : ℝ) :
    (⋃ n : ℕ, Ioo a (a + n + 1)) = Ioi a := by
  ext t
  simp only [mem_iUnion, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨_, ht, _⟩
    exact ht
  · intro ht
    obtain ⟨n, hn⟩ := exists_nat_gt (t - a)
    exact ⟨n, ht, by linarith⟩

/-- Almost-everywhere assertions on every finite initial interval hold on the
whole open half-line. No uncountable intersection of exceptional sets is used. -/
theorem ae_restrict_Ioi_of_forall_Ioo {μ : Measure ℝ} {a : ℝ} {p : ℝ → Prop}
    (h : ∀ b, a < b → ∀ᵐ t ∂μ.restrict (Ioo a b), p t) :
    ∀ᵐ t ∂μ.restrict (Ioi a), p t := by
  rw [← iUnion_Ioo_nat_add a, ae_restrict_iUnion_iff]
  intro n
  exact h _ (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- Strong measurability on finite initial intervals gives strong measurability
on the open half-line, including for nonseparable targets. -/
theorem aestronglyMeasurable_restrict_Ioi_of_forall_Ioo
    {E : Type*} [TopologicalSpace E] [PseudoMetrizableSpace E]
    {μ : Measure ℝ} {a : ℝ} {f : ℝ → E}
    (h : ∀ b, a < b → AEStronglyMeasurable f (μ.restrict (Ioo a b))) :
    AEStronglyMeasurable f (μ.restrict (Ioi a)) := by
  rw [← iUnion_Ioo_nat_add a]
  exact AEStronglyMeasurable.iUnion fun n ↦ h _ (by linarith [Nat.cast_nonneg (α := ℝ) n])

end MeasureTheory
