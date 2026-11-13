/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.DefiningFunction
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Regular defining functions for balls

The defining function `r² - ‖x - c‖²` supplies the C¹ boundary hypothesis
needed by smooth approximation up to the boundary of a ball.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology RealInnerProductSpace

namespace SobolevSpace.Boundary

/-- Every positive-radius Euclidean ball has a C¹ boundary in the local defining-function sense. -/
theorem hasC1Boundary_ball {n : ℕ} (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    HasC1Boundary (ball c r) := by
  intro x hx
  rw [frontier_ball c hr.ne'] at hx
  have hnorm : ‖x - c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hx
  let f : ℝ^n → ℝ := fun y ↦ r ^ 2 - ‖y - c‖ ^ 2
  have hd := (((hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).sub_const c)).const_sub (r ^ 2)
  change HasFDerivAt f _ x at hd
  refine ⟨f, (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq
    (𝕜 := ℝ))).contDiffAt, by simp [f, hnorm], ?_, ?_⟩
  · intro hz
    rw [hd.fderiv] at hz
    have h := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (x - c)) hz
    simp only [neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_apply, nsmul_eq_mul, Nat.cast_ofNat, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, zero_apply, hnorm] at h
    nlinarith [sq_pos_of_pos hr]
  · apply Eventually.of_forall
    intro y
    rw [mem_ball, dist_eq_norm]
    change ‖y - c‖ < r ↔ 0 < r ^ 2 - ‖y - c‖ ^ 2
    constructor <;> intro h <;> nlinarith [norm_nonneg (y - c)]

end SobolevSpace.Boundary
