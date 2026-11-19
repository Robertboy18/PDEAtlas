/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.RegularLevel

/-!
# Operational Sobolev atlases on arbitrary Euclidean balls

The regular defining function `R² - ‖x-z‖²` constructs a smooth graph boundary
and hence an operational extension atlas on every ball of positive radius.
This supplies the geometric input to the Sobolev truncation APIs.
-/

@[expose] public noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace SobolevSpace.Boundary

variable {n : ℕ} [Fact (0 < n)]

/-- The regular defining function gives a C¹ graph boundary on every
Euclidean ball of positive radius. -/
theorem hasContDiffGraphBoundary_ball (z : ℝ^n) {R : ℝ} (hR : 0 < R) :
    HasContDiffGraphBoundary 1 (ball z R) := by
  let f : ℝ^n → ℝ := fun x ↦ R ^ 2 - ‖x - z‖ ^ 2
  have hf : ContDiff ℝ 1 f :=
    contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  apply hasContDiffGraphBoundary_of_regular_level
    (f := f) (c := 0) hf.contDiffOn isOpen_univ le_rfl
  · intro x hx
    have hxR : ‖x - z‖ = R := by
      simpa only [frontier_ball z hR.ne', mem_sphere, dist_eq_norm] using hx
    exact ⟨mem_univ x, by simp only [f, hxR, sub_self]⟩
  · intro x hx hzero
    have hxR : ‖x - z‖ = R := by
      simpa only [frontier_ball z hR.ne', mem_sphere, dist_eq_norm] using hx
    have hd := (hasFDerivAt_const (R ^ 2) x).sub
      ((hasStrictFDerivAt_norm_sq (x - z)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const z))
    have he := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (x - z)) (hd.fderiv.symm.trans hzero)
    simp only [sub_apply, zero_apply, ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, two_smul,
      real_inner_self_eq_norm_sq, hxR] at he
    nlinarith [sq_pos_of_pos hR]
  · intro x _
    rw [mem_ball_iff_norm]
    dsimp only [f]
    constructor <;> intro hx <;> nlinarith [norm_nonneg (x - z)]

/-- Every Euclidean ball of positive radius has an operational C¹ extension
atlas, constructed from its regular defining function. -/
theorem nonempty_c1ExtensionAtlas_ball (z : ℝ^n) {R : ℝ} (hR : 0 < R) :
    Nonempty (C1ExtensionAtlas n (ball z R)) := by
  obtain ⟨atlas, _, _⟩ := (hasContDiffGraphBoundary_ball z hR).exists_c1ExtensionAtlas
    le_rfl isOpen_ball isBounded_ball
  exact ⟨atlas⟩

end SobolevSpace.Boundary
