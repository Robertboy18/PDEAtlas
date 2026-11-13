/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Order.Lattice

/-!
# Almost-everywhere bounds for continuous functions on open sets

For a measure positive on nonempty open sets, continuous functions cannot
violate an almost-everywhere inequality at a point of an open domain.
-/

@[expose] public section

namespace PDE.Analysis

open MeasureTheory Set

/-- Extend an almost-everywhere inequality between continuous real functions
to every point of an open set. -/
theorem leOn_open_of_ae_le
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {U : Set X} {f g : X → ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (h : ∀ᵐ x ∂μ.restrict U, f x ≤ g x) :
    ∀ x ∈ U, f x ≤ g x := by
  have heq : (fun x ↦ max (f x) (g x)) =ᵐ[μ.restrict U] g :=
    h.mono fun _ hx ↦ max_eq_right hx
  have hpoint := Measure.eqOn_open_of_ae_eq heq hU (hf.sup hg) hg
  intro x hx
  exact max_eq_right_iff.mp (hpoint hx)

end PDE.Analysis
