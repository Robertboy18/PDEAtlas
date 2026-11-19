/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.UnitBall.Hessian
public import PDE.Analysis.InnerProductSpace.Ball.LineIntersection
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Interior directional derivatives near the sphere

For nonnegative zero boundary data, the outward derivative is nonpositive.
A positive second derivative in an outward direction makes the first derivative
strictly negative at all nearby interior points: follow the line to the
sphere and apply the mean value theorem. This also applies when the normal
derivative vanishes at the sphere point.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Set Metric Filter PDE.Analysis
open scoped Topology RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]
variable [Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1)]

/-- A positive directional Hessian at the sphere forces a strictly negative
first derivative at every sufficiently nearby interior point in that outward direction. -/
theorem eventually_fderiv_neg_of_hessian_pos {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hnonneg : ∀ y ∈ closedBall (0 : ℝ^n) 1, 0 ≤ u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {x e : ℝ^n} (hx : ‖x‖ = 1) (he : ‖e‖ = 1) (hxe : 0 < ⟪x, e⟫)
    (hsecond : 0 < fderiv ℝ (fderiv ℝ u) x e e) :
    ∀ᶠ y in 𝓝 x, y ∈ ball (0 : ℝ^n) 1 → fderiv ℝ u y e < 0 := by
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hH : Continuous (fun z ↦ fderiv ℝ (fderiv ℝ u) z e e) :=
    ((hDu.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply
      continuous_const
  have hnear : ∀ᶠ z in 𝓝 x,
      0 < fderiv ℝ (fderiv ℝ u) z e e ∧ 0 < ⟪z, e⟫ :=
    (hH.continuousAt.eventually_const_lt hsecond).and
      ((continuous_id.inner continuous_const).continuousAt.eventually_const_lt hxe)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  filter_upwards [eventually_exit_segment_mem_ball he hx hxe.le hr] with y hy hyinside
  have hyn : ‖y‖ < 1 := by simpa using hyinside
  let τ := unitBallExitTime e y
  have hτ : 0 < τ := unitBallExitTime_pos e hyn
  let p : ℝ → ℝ^n := fun t ↦ y + t • e
  have hp (t : ℝ) : HasDerivAt p e t := by
    simpa [p] using ((hasDerivAt_id t).smul_const e).const_add y
  have hg (t : ℝ) : HasDerivAt (fun s ↦ fderiv ℝ u (p s) e)
      (fderiv ℝ (fderiv ℝ u) (p t) e e) t := by
    have h := (hDu.differentiable one_ne_zero (p t)).hasFDerivAt.comp_hasDerivAt t (hp t)
    simpa only [map_zero, add_zero] using! h.clm_apply (hasDerivAt_const t e)
  have hmono : StrictMonoOn (fun t ↦ fderiv ℝ u (p t) e) (Icc 0 τ) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t _ ↦ (hg t).continuousAt.continuousWithinAt) (by
        intro t ht
        rw [(hg t).deriv]
        exact (hball (hy t (interior_subset ht))).1)
  have hlt := hmono (left_mem_Icc.mpr hτ.le) (right_mem_Icc.mpr hτ.le) hτ
  have hnorm : ‖p τ‖ = 1 := norm_add_unitBallExitTime_smul he hyn
  have hend : fderiv ℝ u (p τ) e ≤ 0 := by
    rw [← inner_gradient_left,
      gradient_eq_radial_smul_of_zero_on_sphere
        (hu.differentiable (by norm_num)) hzero hnorm, real_inner_smul_left]
    exact mul_nonpos_of_nonpos_of_nonneg
      (inner_gradient_radial_nonpos (hu.differentiable (by norm_num))
        hnonneg hzero hnorm)
      (hball (hy τ (right_mem_Icc.mpr hτ.le))).2.le
  simpa [p] using hlt.trans_le hend

end SobolevSpace.Trace.C1
