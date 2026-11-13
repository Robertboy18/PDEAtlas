/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# A canonical representative of an almost-everywhere class

`continuousRepresentative μ f` is a continuous function almost everywhere equal to `f` when
such a function exists, and `f` itself otherwise. For a measure positive on nonempty open sets
the continuous representative is unique, so this choice turns statements about classes into
pointwise statements: a function with a smooth representative is replaced by that smooth
function.
-/

@[expose] public section

namespace MeasureTheory

variable {X F : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace F]

/-- A continuous function almost everywhere equal to `f` if one exists, and `f` otherwise. -/
noncomputable def continuousRepresentative (μ : Measure X) (f : X → F) : X → F := by
  classical
  exact if h : ∃ g : X → F, Continuous g ∧ g =ᵐ[μ] f then h.choose else f

/-- The chosen representative lies in the almost-everywhere class of `f`. -/
theorem continuousRepresentative_ae_eq (μ : Measure X) (f : X → F) :
    continuousRepresentative μ f =ᵐ[μ] f := by
  classical
  unfold continuousRepresentative
  split_ifs with h
  · exact h.choose_spec.2
  · exact Filter.EventuallyEq.rfl

/-- If the class of `f` has a continuous member, the chosen representative is continuous. -/
theorem continuous_continuousRepresentative {μ : Measure X} {f : X → F}
    (h : ∃ g : X → F, Continuous g ∧ g =ᵐ[μ] f) : Continuous (continuousRepresentative μ f) := by
  classical
  unfold continuousRepresentative
  split_ifs
  exact h.choose_spec.1

/-- For a measure positive on open sets, the chosen representative is every continuous member
of the class. -/
theorem continuousRepresentative_eq [T2Space F] {μ : Measure X} [μ.IsOpenPosMeasure]
    {f g : X → F} (hg : Continuous g) (hgf : g =ᵐ[μ] f) :
    continuousRepresentative μ f = g :=
  (Continuous.ae_eq_iff_eq μ (continuous_continuousRepresentative ⟨g, hg, hgf⟩) hg).mp
    ((continuousRepresentative_ae_eq μ f).trans hgf.symm)

end MeasureTheory
