/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions

/-!
# Boundary regularity: shared setup

We define `SobolevSpace.C2BoundaryAtlas`, the operational chart structure used by the
flattened-boundary regularity argument. It extends the first-order extension atlas with `C²`
regularity of the total chart and inverse-chart representatives; concrete atlas constructions and
derivations from geometric boundary hypotheses are elsewhere.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

/-- Operational boundary atlas whose chart and inverse representatives are `C²`.

This extends `Boundary.C1ExtensionAtlas` with the regularity used in the flattened-boundary
argument. Its construction from a geometric `C²`-boundary predicate is a separate
result. -/
structure C2BoundaryAtlas (n : ℕ) [Fact (0 < n)] (Ω : Set (ℝ^n)) : Type
    extends Boundary.C1ExtensionAtlas n Ω where
  /-- Every total chart representative is twice continuously differentiable. -/
  chart_contDiff_two : ∀ i : Fin toC1ExtensionAtlas.N,
    ContDiff ℝ 2 (fun x ↦ toC1ExtensionAtlas.chart i x)
  /-- Every total inverse-chart representative is twice continuously differentiable. -/
  chart_symm_contDiff_two : ∀ i : Fin toC1ExtensionAtlas.N,
    ContDiff ℝ 2 (fun y ↦ (toC1ExtensionAtlas.chart i).symm y)

end SobolevSpace
