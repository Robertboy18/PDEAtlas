/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.UnitBall.Directional
public import PDE.Elliptic.Classical.MaximumPrinciple.Hopf.Laplacian
public import PDE.FDeriv.Laplacian.Continuity

/-!
# Boundary neighborhoods for moving planes in a ball

Let `u` be `C²` on `ℝ^n`, positive in the unit ball and zero on the sphere, with `-Δu = f(u)` in the
ball for a Lipschitz `f`. If `x` lies on the sphere and the unit vector `e` points outward at `x`,
`⟪x, e⟫ > 0`, then `u` has negative derivative in the direction `e` at all points of the ball near
`x` (`eventually_fderiv_neg`). No sign of `f(0)` is assumed.

This is Evans's §9.5.2, Lemma 2 (Boundary estimates), with the direction `e` in place of the last
coordinate direction. The radial symmetry theorem
`Elliptic.Semilinear.exists_strictAntiOn_radial_profile_of_lipschitz` obtains the `C²` function on
`ℝ^n` from a solution that is `C²` up to the boundary.

## How it works

Zero boundary values make the gradient at `x` a nonpositive multiple of `x`
(`gradient_eq_radial_smul_of_zero_on_sphere`, `inner_gradient_radial_nonpos`). If the multiple is
negative, the derivative in the direction `e` is negative at `x`, and continuity gives the
neighborhood. Otherwise `Du(x) = 0`. If `f(0) ≥ 0`, the bound `f(s) ≥ f(0) - L s` for `s ≥ 0` gives
`-Δu + L u ≥ 0` in the ball, and Hopf's lemma
(`EllipticMaximum.hopf_fderiv_neg_of_pos_of_neg_laplacian_add_mul_nonneg`) contradicts `Du(x) = 0`;
Evans uses his Lemma 1 at this point, which allows a zeroth-order coefficient of either sign. So
`f(0) < 0` and `Δu(x) = -f(0) > 0`, and the Hessian at `x` is `Δu(x) ⟪x, ·⟫ ⟪x, ·⟫`
(`hessian_eq_laplacian_mul_inner_mul_inner`), as in Evans's (12). A positive second derivative in
the direction `e` then gives the neighborhood
(`SobolevSpace.Trace.C1.eventually_fderiv_neg_of_hessian_pos`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.5.2 (Radial symmetry), (2)-(3), pp. 555-556, Lemma 1 (A
  refinement of Hopf's Lemma), p. 556, and Lemma 2 (Boundary estimates) and its proof, (7)-(14),
  pp. 557-558.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace Elliptic.Semilinear.MovingPlanes

open Set Metric Filter SobolevSpace.Trace.C1
open scoped Topology RealInnerProductSpace NNReal Gradient

variable {n : ℕ} [Fact (0 < n)]
variable [SobolevSpace.Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1)]

/-- A Lipschitz semilinear solution with positive interior and zero spherical data has
strictly negative directional derivative at all nearby interior points whenever the
direction points outward at the given sphere point. No sign of `f(0)` is assumed. This is
Evans's §9.5.2, Lemma 2, for the direction `e`. -/
theorem eventually_fderiv_neg {u : ℝ^n → ℝ} {f : ℝ → ℝ} {L : ℝ≥0}
    (hu : ContDiff ℝ 2 u) (hf : LipschitzWith L f)
    (hpde : ∀ y ∈ ball (0 : ℝ^n) 1, -laplacian u y = f (u y))
    (hpos : ∀ y ∈ ball (0 : ℝ^n) 1, 0 < u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {x e : ℝ^n} (hx : ‖x‖ = 1) (he : ‖e‖ = 1) (hxe : 0 < ⟪x, e⟫) :
    ∀ᶠ y in 𝓝 x, y ∈ ball (0 : ℝ^n) 1 → fderiv ℝ u y e < 0 := by
  have hnonneg : ∀ y ∈ closedBall (0 : ℝ^n) 1, 0 ≤ u y := by
    intro y hy
    have hyn : ‖y‖ ≤ 1 := by simpa using hy
    rcases lt_or_eq_of_le hyn with hlt | heq
    · exact (hpos y (by simpa using hlt)).le
    · rw [hzero y (by simp [heq])]
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hn := inner_gradient_radial_nonpos hd hnonneg hzero hx
  rcases lt_or_eq_of_le hn with hn | hn
  · have hdir : fderiv ℝ u x e < 0 := by
      rw [← inner_gradient_left,
        gradient_eq_radial_smul_of_zero_on_sphere hd hzero hx, real_inner_smul_left]
      exact mul_neg_of_neg_of_pos hn hxe
    exact ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousAt
      |>.eventually_lt_const hdir |>.mono fun _ h _ ↦ h
  · have hcrit : ∇ u x = 0 := by
      rw [gradient_eq_radial_smul_of_zero_on_sphere hd hzero hx, hn, zero_smul]
    have hfzero : f 0 < 0 := by
      by_contra hnot
      have hf0 : 0 ≤ f 0 := le_of_not_gt hnot
      have hsuper : ∀ y ∈ ball (0 : ℝ^n) 1,
          0 ≤ -laplacian u y + (L : ℝ) * u y := by
        intro y hy
        rw [hpde y hy]
        have h := hf.le_add_mul 0 (u y)
        simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (hpos y hy)] at h
        exact hf0.trans h
      have hh := EllipticMaximum.hopf_fderiv_neg_of_pos_of_neg_laplacian_add_mul_nonneg
        zero_lt_one L.coe_nonneg (by simpa using hx)
        (hzero x (by simp [hx])) hu.continuous.continuousOn
        (fun _ _ ↦ hu.contDiffAt) hpos hsuper (hd x)
      have hh' : fderiv ℝ u x x < 0 := by simpa using hh
      rw [← inner_gradient_left, hcrit, inner_zero_left] at hh'
      exact lt_irrefl _ hh'
    have hclosed : EqOn (fun y ↦ -laplacian u y) (fun y ↦ f (u y))
        (closedBall (0 : ℝ^n) 1) := by
      simpa only [closure_ball _ one_ne_zero] using
        (show EqOn (fun y ↦ -laplacian u y) (fun y ↦ f (u y))
          (ball (0 : ℝ^n) 1) from fun y hy ↦ hpde y hy).closure
          hu.continuous_coordinate_laplacian.neg
          (hf.continuous.comp hu.continuous)
    have hlap : 0 < laplacian u x := by
      have h := hclosed (x := x) (by simp [hx])
      change -laplacian u x = f (u x) at h
      rw [hzero x (by simp [hx])] at h
      linarith
    apply eventually_fderiv_neg_of_hessian_pos hu hnonneg hzero hx he hxe
    rw [hessian_eq_laplacian_mul_inner_mul_inner hu hnonneg hzero hx hcrit e e]
    exact mul_pos (mul_pos hlap hxe) hxe

end Elliptic.Semilinear.MovingPlanes
