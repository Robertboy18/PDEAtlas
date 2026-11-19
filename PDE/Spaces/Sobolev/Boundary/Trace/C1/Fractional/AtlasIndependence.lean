/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.AtlasEquiv

/-!
# Independence of the half-order boundary space from the atlas

The change of atlas of `AtlasEquiv` is bounded by the constructed lifting and trace norms;
the chart norms need not be equal. Both atlases therefore define the same physical surface
data: the ranges of the two boundary-value maps agree.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open scoped Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable (A B : Boundary.C1ExtensionAtlas (m + 1) Ω)

/-- The comparison operator is bounded by the target trace norm times the source lifting norm. -/
theorem opNorm_atlasEquiv_le :
    ‖(atlasEquiv A B).toContinuousLinearMap‖ ≤
      ‖fractionalTrace (hΩ := B)‖ * ‖lifting (hΩ := A)‖ :=
  (fractionalTrace (hΩ := B)).opNorm_comp_le (lifting (hΩ := A))

/-- The target chart norm is controlled by the source chart norm with the constructed constants. -/
theorem norm_atlasEquiv_le (g : HalfOrderBoundarySpace (hΩ := A)) :
    ‖atlasEquiv A B g‖ ≤ (‖fractionalTrace (hΩ := B)‖ * ‖lifting (hΩ := A)‖) * ‖g‖ :=
  ((atlasEquiv A B).toContinuousLinearMap.le_opNorm g).trans
    (mul_le_mul_of_nonneg_right (opNorm_atlasEquiv_le A B) (norm_nonneg g))

/-- The reverse comparison gives the other inequality between the two chart norms. -/
theorem norm_le_norm_atlasEquiv (g : HalfOrderBoundarySpace (hΩ := A)) :
    ‖g‖ ≤ (‖fractionalTrace (hΩ := A)‖ * ‖lifting (hΩ := B)‖) * ‖atlasEquiv A B g‖ := by
  simpa only [← atlasEquiv_symm A B, ContinuousLinearEquiv.symm_apply_apply] using
    norm_atlasEquiv_le B A (atlasEquiv A B g)

/-- The same physical surface data belong to the half-order space for every operational atlas. -/
theorem range_boundaryValue_eq_of_atlases :
    Set.range (boundaryValue (hΩ := A)) = Set.range (boundaryValue (hΩ := B)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g, rfl⟩
    exact ⟨atlasEquiv A B g, boundaryValue_atlasEquiv A B g⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨atlasEquiv B A g, boundaryValue_atlasEquiv B A g⟩

end SobolevSpace.Trace.C1.Fractional
