/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.DefiningFunction
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The intrinsic outward normal of the unit ball

The defining function `1-‖x‖²` identifies the atlas normal with the radius
vector. The argument includes one-dimensional balls, whose two normal vectors
are the endpoint signs.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Set Metric

variable {n : ℕ} [Fact (0 < n)]
variable [Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1)]

/-- Every operational C¹ atlas of the unit ball yields the usual radial normal. -/
theorem outwardUnitNormal_unitBall {x : ℝ^n} (hx : x ∈ frontier (ball (0 : ℝ^n) 1)) :
    outwardUnitNormal (Ω := ball (0 : ℝ^n) 1) ⟨x, hx⟩ = x := by
  have hnorm {y : ℝ^n} (hy : y ∈ frontier (ball (0 : ℝ^n) 1)) : ‖y‖ = 1 := by
    simpa only [frontier_ball (0 : ℝ^n) one_ne_zero, mem_sphere, dist_zero_right] using hy
  have hd : HasFDerivAt (fun y : ℝ^n ↦ 1 - ‖y‖ ^ 2) ((-2 : ℝ) • innerSL ℝ x) x := by
    simpa only [neg_smul, two_smul] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub 1
  have hne : (-2 : ℝ) • innerSL ℝ x ≠ 0 := by
    intro h
    have hv := congrArg (fun f : ℝ^n →L[ℝ] ℝ ↦ f x) h
    simp only [smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      hnorm hx, one_pow, smul_eq_mul, mul_one, zero_apply] at hv
    norm_num at hv
  have hnormal := outwardUnitNormal_eq_of_defining_function hx hd hne
    (Filter.Eventually.of_forall fun y hy ↦ by rw [hnorm hy]; norm_num)
    (Filter.Eventually.of_forall fun y hy ↦ by
      have hlt : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
      nlinarith [norm_nonneg y])
  have hriesz :
      (InnerProductSpace.toDual ℝ (ℝ^n)).symm ((-2 : ℝ) • innerSL ℝ x) = (-2 : ℝ) • x := by
    apply (InnerProductSpace.toDual ℝ (ℝ^n)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul]
    rfl
  rw [hnormal, hriesz]
  norm_num [norm_smul, hnorm hx, smul_smul]

end SobolevSpace.Trace.C1
