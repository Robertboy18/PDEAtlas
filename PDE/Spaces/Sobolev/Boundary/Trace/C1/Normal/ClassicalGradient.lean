/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Vanishing
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Gradient
import PDE.Spaces.Sobolev.Extension.C1.Classical

/-!
# The completed gradient of zero boundary data is normal

A C¹ extension of the scalar field agrees with its prescribed continuous
closure values. Differentiating curves on the boundary makes its
gradient normal there. Uniqueness of the continuous gradient completion
transfers that fact to the raw closure gradient.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Set

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The completed gradient of raw C¹ zero boundary data is its normal
derivative times the outward unit normal. -/
theorem completedGradient_eq_normal_smul
    (hgraph : Boundary.HasC1GraphBoundary Ω) {u : ℝ^n → ℝ}
    (hu : ContDiffUpToBoundary 1 u Ω) (hc : ContinuousOn u (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, u x = 0) {x : ℝ^n} (hx : x ∈ frontier Ω) :
    hu.completedGradient x =
      inner ℝ (hu.completedGradient x) (outwardUnitNormal (Ω := Ω) ⟨x, hx⟩) •
        outwardUnitNormal (Ω := Ω) ⟨x, hx⟩ := by
  obtain ⟨U, hU, _, heq⟩ :=
    hu.exists_contDiff_one_extension hΩ.isOpen hΩ.bounded hgraph
  have hclosed : EqOn U u (closure Ω) :=
    heq.of_subset_closure hU.continuous.continuousOn hc subset_closure Subset.rfl
  rw [hu.completedGradient_eq_gradient_extension hΩ.isOpen hU heq
    (frontier_subset_closure hx)]
  apply gradient_eq_normal_smul_of_vanishing_on_frontier hx
    ((hU.differentiable one_ne_zero x).hasFDerivAt)
  exact Filter.Eventually.of_forall fun y hy ↦ (hclosed (frontier_subset_closure hy)).trans
    (hzero y hy)

end SobolevSpace.Trace.C1
