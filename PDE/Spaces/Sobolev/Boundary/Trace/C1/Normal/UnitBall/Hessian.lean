/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.UnitBall
public import PDE.Analysis.Calculus.Gradient
public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Hessian at a critical point of zero spherical boundary data

A nonnegative function with zero boundary values has nonpositive outward
normal derivative. At a boundary critical point this normal coefficient has
a maximum on the sphere. Differentiating the normal-gradient identity
along sphere curves therefore annihilates all tangent directions of the Hessian.
Only two derivatives of the original function are used.
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace SobolevSpace.Trace.C1

open Set Metric Filter
open scoped Topology RealInnerProductSpace Gradient

variable {n : ℕ} [Fact (0 < n)]
variable [Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1)]

/-- The boundary gradient of zero spherical data is radial. -/
theorem gradient_eq_radial_smul_of_zero_on_sphere {u : ℝ^n → ℝ}
    (hu : Differentiable ℝ u)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {x : ℝ^n} (hx : ‖x‖ = 1) :
    ∇ u x = ⟪∇ u x, x⟫ • x := by
  have hxb : x ∈ frontier (ball (0 : ℝ^n) 1) := by
    simp [frontier_ball _ one_ne_zero, hx]
  have h := gradient_eq_normal_smul_of_vanishing_on_frontier hxb
    (hu x).hasFDerivAt (Filter.Eventually.of_forall fun y hy ↦ by
      apply hzero y
      simpa only [frontier_ball _ one_ne_zero] using hy)
  simpa only [outwardUnitNormal_unitBall hxb, gradient] using h

omit [Fact (0 < n)] [Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1)] in
/-- Nonnegative data vanishing on the sphere have nonpositive outward derivative. -/
theorem inner_gradient_radial_nonpos {u : ℝ^n → ℝ}
    (hu : Differentiable ℝ u)
    (hnonneg : ∀ y ∈ closedBall (0 : ℝ^n) 1, 0 ≤ u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {x : ℝ^n} (hx : ‖x‖ = 1) :
    ⟪∇ u x, x⟫ ≤ 0 := by
  have hxs : x ∈ sphere (0 : ℝ^n) 1 := by simp [hx]
  have hmin : IsMinOn u (closedBall (0 : ℝ^n) 1) x := by
    intro y hy
    rw [hzero x hxs]
    exact hnonneg y hy
  have ht : -x ∈ posTangentConeAt (closedBall (0 : ℝ^n) 1) x := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset
      ((convex_closedBall (0 : ℝ^n) 1).segment_subset
        (sphere_subset_closedBall hxs) (by simp : (0 : ℝ^n) ∈ closedBall 0 1))
  have h := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
    (hu x).hasFDerivAt.hasFDerivWithinAt ht
  simpa only [map_neg, neg_nonneg, inner_gradient_left] using h

/-- At a boundary critical point, the Hessian kills every tangent direction.
The normal coefficient reaches its spherical maximum zero, so its derivative
along a sphere curve vanishes by Fermat's theorem. -/
theorem fderiv_gradient_tangent_eq_zero {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hnonneg : ∀ y ∈ closedBall (0 : ℝ^n) 1, 0 ≤ u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {x v : ℝ^n} (hx : ‖x‖ = 1) (hcrit : ∇ u x = 0)
    (hv : ⟪x, v⟫ = 0) :
    fderiv ℝ (∇ u) x v = 0 := by
  let p : ℝ → ℝ^n := fun t ↦ x + t • v
  let γ : ℝ → ℝ^n := fun t ↦ ‖p t‖⁻¹ • p t
  have hp : HasDerivAt p v 0 := by
    simpa [p] using ((hasDerivAt_id (x := (0 : ℝ))).smul_const v).const_add x
  have hpne (t : ℝ) : p t ≠ 0 := by
    intro hz
    have h := congrArg (fun y ↦ ⟪x, y⟫) hz
    simp [p, inner_add_right, real_inner_smul_right, hv, hx] at h
  have hγ0 : γ 0 = x := by simp [γ, p, hx]
  have hγnorm (t : ℝ) : ‖γ t‖ = 1 := by
    simp [γ, norm_smul, norm_inv,
      norm_ne_zero_iff.mpr (hpne t)]
  have hnorm : HasDerivAt (fun t ↦ ‖p t‖) 0 0 := by
    simpa [p, hv, Real.sqrt_sq (norm_nonneg _)] using
      hp.norm_sq.sqrt (by simp [p, hx])
  have hγ : HasDerivAt γ v 0 := by
    simpa only [Pi.smul_apply, Pi.inv_apply, p, zero_smul, add_zero, hx,
      neg_zero, zero_div, inv_one, one_smul] using!
      (hnorm.inv (by simp [p, hx])).smul hp
  have hg : ContDiff ℝ 1 (∇ u) :=
    contDiff_iff_contDiffAt.mpr fun _ ↦
      PDE.Analysis.contDiffAt_gradient (m := 1) hu.contDiffAt
  have hG : HasDerivAt (fun t ↦ ∇ u (γ t))
      (fderiv ℝ (∇ u) x v) 0 := by
    simpa only [Function.comp_def, hγ0] using!
      ((hg.differentiable one_ne_zero (γ 0)).hasFDerivAt.comp_hasDerivAt 0 hγ)
  let a : ℝ → ℝ := fun t ↦ ⟪∇ u (γ t), γ t⟫
  have ha0 : a 0 = 0 := by
    change ⟪∇ u (γ 0), γ 0⟫ = 0
    rw [hγ0, hcrit, inner_zero_left]
  have ha : HasDerivAt a ⟪fderiv ℝ (∇ u) x v, x⟫ 0 := by
    simpa only [hγ0, hcrit, inner_zero_left, zero_add] using hG.inner ℝ hγ
  have hmax : IsLocalMax a 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [ha0]
    exact inner_gradient_radial_nonpos (hu.differentiable (by norm_num))
      hnonneg hzero (hγnorm t)
  have hda : ⟪fderiv ℝ (∇ u) x v, x⟫ = 0 :=
    hmax.hasDerivAt_eq_zero ha
  have hr : HasDerivAt (fun t ↦ a t • γ t) 0 0 := by
    simpa only [ha0, hda, zero_smul, add_zero, Pi.smul_apply] using! ha.smul hγ
  have heq : (fun t ↦ a t • γ t) = fun t ↦ ∇ u (γ t) := by
    funext t
    exact (gradient_eq_radial_smul_of_zero_on_sphere
      (hu.differentiable (by norm_num)) hzero (hγnorm t)).symm
  rw [heq] at hr
  exact hG.unique hr

/-- The Hessian at a critical point of nonnegative zero spherical data is
the normal rank-one form with coefficient equal to the Laplacian. -/
theorem hessian_eq_laplacian_mul_inner_mul_inner {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hnonneg : ∀ y ∈ closedBall (0 : ℝ^n) 1, 0 ≤ u y)
    (hzero : ∀ y ∈ sphere (0 : ℝ^n) 1, u y = 0)
    {x : ℝ^n} (hx : ‖x‖ = 1) (hcrit : ∇ u x = 0) (v w : ℝ^n) :
    fderiv ℝ (fderiv ℝ u) x v w = laplacian u x * ⟪x, v⟫ * ⟪x, w⟫ := by
  have hsplit (z : ℝ^n) :
      fderiv ℝ (∇ u) x z =
        ⟪x, z⟫ • fderiv ℝ (∇ u) x x := by
    have htan : ⟪x, z - ⟪x, z⟫ • x⟫ = 0 := by
      simp [inner_sub_right, real_inner_smul_right, hx]
    have h := fderiv_gradient_tangent_eq_zero hu hnonneg hzero hx hcrit htan
    simpa only [map_sub, map_smul, sub_eq_zero] using h
  have hb (z q : ℝ^n) :
      fderiv ℝ (fderiv ℝ u) x z q =
        fderiv ℝ (fderiv ℝ u) x x x * ⟪x, z⟫ * ⟪x, q⟫ := by
    rw [← PDE.Analysis.inner_fderiv_gradient_at hu.contDiffAt, hsplit z,
      real_inner_smul_left, PDE.Analysis.inner_fderiv_gradient_at hu.contDiffAt]
    rw [(hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq x q]
    rw [← PDE.Analysis.inner_fderiv_gradient_at hu.contDiffAt, hsplit q,
      real_inner_smul_left, PDE.Analysis.inner_fderiv_gradient_at hu.contDiffAt]
    ring
  have htrace : laplacian u x = fderiv ℝ (fderiv ℝ u) x x x := by
    calc
      laplacian u x =
          ∑ i : Fin n, fderiv ℝ (fderiv ℝ u) x x x * (x i) ^ 2 := by
        unfold laplacian
        apply Finset.sum_congr rfl
        intro i _
        rw [PDE.secondPartialDeriv_eq_fderiv i i
          ((hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt_one), hb]
        simp [EuclideanSpace.inner_single_right, pow_two, mul_assoc]
      _ = fderiv ℝ (fderiv ℝ u) x x x * ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
      _ = fderiv ℝ (fderiv ℝ u) x x x := by rw [hx]; simp
  rw [htrace]
  exact hb v w

end SobolevSpace.Trace.C1
