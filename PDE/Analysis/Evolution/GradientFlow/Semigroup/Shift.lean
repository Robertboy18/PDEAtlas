/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Solution.Basic
public import PDE.Analysis.Evolution.Time.WeakDerivative.Translation

/-!
# Restarting a weak subgradient flow

If `(u, g)` is a weak subgradient flow and `s ≥ 0`, then so is
`(u(s + ·), g(s + ·))`. Translation preserves the weak derivative and the
inclusion `-g ∈ ∂I(u)`, and `s + (0, ∞) ⊆ (0, ∞)`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A nonnegative time translation is again a weak flow of the same energy. -/
theorem IsSubgradientFlow.shift {I : H → EReal} {u g : ℝ → H}
    (h : IsSubgradientFlow I u g) {s : ℝ} (hs : 0 ≤ s) :
    IsSubgradientFlow I (fun t ↦ u (s + t)) (fun t ↦ g (s + t)) := by
  have hsubset : Ioi (0 : ℝ) ⊆ (fun t ↦ s + t) ⁻¹' Ioi 0 := by
    intro t ht
    exact lt_add_of_le_of_pos hs ht
  have hmeasure := volume.restrict_mono_set hsubset
  have hp := (measurePreserving_add_left (volume : Measure ℝ) s).restrict_preimage
    (measurableSet_Ioi (a := (0 : ℝ)))
  refine ⟨?_, ?_, (h.weakDerivative.comp_const_add isOpen_Ioi s).mono hsubset, ?_⟩
  · exact h.continuousOn.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht ↦ add_nonneg hs ht)
  · exact (h.velocity_memLp.comp_measurePreserving hp).mono_measure hmeasure
  · exact (hp.quasiMeasurePreserving.ae h.inclusion).filter_mono (ae_mono hmeasure)

end PDE.Analysis.Evolution
