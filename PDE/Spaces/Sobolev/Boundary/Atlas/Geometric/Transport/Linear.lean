/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary

/-!
# Linear transport of raw graph boundary geometry

An invertible linear coordinate change preserves the graph condition by
composition of the local coordinates. Orthogonality is not needed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Boundary

open Set

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Pulling back by any continuous linear equivalence preserves C¹ graph geometry. -/
theorem HasC1GraphBoundary.preimage_continuousLinearEquiv
    (hΩ : HasC1GraphBoundary Ω) (A : ℝ^n ≃L[ℝ] ℝ^n) :
    HasC1GraphBoundary (A ⁻¹' Ω) := by
  intro x hx
  have hAx : A x ∈ frontier Ω := by
    change x ∈ A.toHomeomorph ⁻¹' frontier Ω
    rwa [A.toHomeomorph.preimage_frontier]
  obtain ⟨e, g, hg, heq, hside⟩ := hΩ (A x) hAx
  refine ⟨A.trans e, g, hg, heq, ?_⟩
  exact A.continuous.continuousAt.eventually hside

/-- Linear transport also preserves the full finite or infinite graph regularity. -/
theorem HasContDiffGraphBoundary.preimage_continuousLinearEquiv
    {k : ℕ∞} (hΩ : HasContDiffGraphBoundary k Ω) (A : ℝ^n ≃L[ℝ] ℝ^n) :
    HasContDiffGraphBoundary k (A ⁻¹' Ω) := by
  intro x hx
  have hAx : A x ∈ frontier Ω := by
    change x ∈ A.toHomeomorph ⁻¹' frontier Ω
    rwa [A.toHomeomorph.preimage_frontier]
  obtain ⟨e, g, s, hs, hxs, hg, heq, hside⟩ := hΩ (A x) hAx
  refine ⟨A.trans e, g, s, hs, hxs, hg, heq, ?_⟩
  exact A.continuous.continuousAt.eventually hside

end SobolevSpace.Boundary
