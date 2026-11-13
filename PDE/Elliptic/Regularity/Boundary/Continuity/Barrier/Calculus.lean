/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.RealPower
public import PDE.FDeriv.Calculus
public import PDE.FDeriv.Laplacian.Product

/-!
# Angular power barriers

A boundary which has a tangent hyperplane lies locally in a slightly enlarged half-space.
The profile `r^a (2 + t - t²/4)`, where `t = ⟪N,x⟫/r`, is positive and strictly superharmonic
in a sufficiently small enlargement when `a` is small. The polynomial expression below avoids
division by the radius in the definition. All differential identities concern nonzero points.

The angular quadratic is useful in dimension two as well: a small radial power alone would
be subharmonic there.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.BoundaryContinuity

open PDE.Analysis.Radial
open scoped InnerProductSpace

variable {n : ℕ}

/-- A radial power times a quadratic angular profile. Its value at the vertex is totalized. -/
def angularPowerBarrier (a : ℝ) (N x : ℝ^n) : ℝ :=
  2 * ‖x‖ ^ a + inner ℝ N x * ‖x‖ ^ (a - 1) -
    inner ℝ N x ^ 2 * ‖x‖ ^ (a - 2) / 4

private theorem partialDeriv_linear (N : ℝ^n) (i : Fin n) (x : ℝ^n) :
    (∂[i] (fun y ↦ inner ℝ N y)) x = N i := by
  have hN : HasFDerivAt (fun y ↦ inner ℝ N y) (innerSL ℝ N) x :=
    (innerSL ℝ N).hasFDerivAt
  unfold partialDeriv
  rw [hN.fderiv]
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]

private theorem laplacian_linear (N x : ℝ^n) :
    laplacian (fun y ↦ inner ℝ N y) x = 0 := by
  unfold laplacian
  simp_rw [partialDeriv_linear]
  simp

private theorem partialDeriv_linear_sq (N : ℝ^n) (i : Fin n) (x : ℝ^n) :
    (∂[i] (fun y ↦ inner ℝ N y ^ 2)) x = 2 * inner ℝ N x * N i := by
  have hN : DifferentiableAt ℝ (fun y ↦ inner ℝ N y) x :=
    (innerSL ℝ N).differentiableAt
  rw [show (fun y : ℝ^n ↦ inner ℝ N y ^ 2) =
    (fun y ↦ inner ℝ N y * inner ℝ N y) by funext y; ring,
    partialDeriv_mul hN hN, partialDeriv_linear]
  ring

private theorem laplacian_linear_sq (N x : ℝ^n) :
    laplacian (fun y ↦ inner ℝ N y ^ 2) x = 2 * ‖N‖ ^ 2 := by
  have hN : ContDiffAt ℝ 2 (fun y ↦ inner ℝ N y) x :=
    (innerSL ℝ N).contDiff.contDiffAt
  simpa [← pow_two, laplacian_linear, partialDeriv_linear,
    ← EuclideanSpace.real_norm_sq_eq] using laplacian_mul hN hN

private theorem inner_rpow_derivative_sum (N : ℝ^n) (a : ℝ) {x : ℝ^n} (hx : x ≠ 0) :
    (∑ i, N i * (∂[i] (fun y : ℝ^n ↦ ‖y‖ ^ a)) x) =
      a * ‖x‖ ^ (a - 2) * inner ℝ N x := by
  simp_rw [partialDeriv_norm_rpow a _ hx]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

private theorem laplacian_linear_mul_rpow (N : ℝ^n) (a : ℝ)
    {x : ℝ^n} (hx : x ≠ 0) :
    laplacian (fun y ↦ inner ℝ N y * ‖y‖ ^ a) x =
      a * (a + (n : ℝ)) * inner ℝ N x * ‖x‖ ^ (a - 2) := by
  have hN : ContDiffAt ℝ 2 (fun y ↦ inner ℝ N y) x :=
    (innerSL ℝ N).contDiff.contDiffAt
  rw [laplacian_mul hN
    (contDiffAt_norm_rpow a hx), laplacian_linear]
  simp_rw [partialDeriv_linear]
  rw [inner_rpow_derivative_sum N a hx, laplacian_norm_rpow a hx]
  ring

private theorem laplacian_linear_sq_mul_rpow (N : ℝ^n) (a : ℝ)
    {x : ℝ^n} (hx : x ≠ 0) :
    laplacian (fun y ↦ inner ℝ N y ^ 2 * ‖y‖ ^ a) x =
      2 * ‖N‖ ^ 2 * ‖x‖ ^ a +
        a * (a + (n : ℝ) + 2) * inner ℝ N x ^ 2 * ‖x‖ ^ (a - 2) := by
  have hN : ContDiffAt ℝ 2 (fun y ↦ inner ℝ N y) x :=
    (innerSL ℝ N).contDiff.contDiffAt
  rw [laplacian_mul (hN.pow 2)
    (contDiffAt_norm_rpow a hx), laplacian_linear_sq]
  simp_rw [partialDeriv_linear_sq]
  have hsum : (∑ i, 2 * inner ℝ N x * N i *
      (∂[i] (fun y : ℝ^n ↦ ‖y‖ ^ a)) x) =
      2 * inner ℝ N x * (a * ‖x‖ ^ (a - 2) * inner ℝ N x) := by
    rw [← inner_rpow_derivative_sum N a hx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsum, laplacian_norm_rpow a hx]
  ring

/-- Smoothness of the angular barrier away from its vertex. -/
theorem angularPowerBarrier_contDiffAt (a : ℝ) (N : ℝ^n) {x : ℝ^n} (hx : x ≠ 0)
    {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (angularPowerBarrier a N) x := by
  have hN : ContDiffAt ℝ k (fun y ↦ inner ℝ N y) x :=
    (innerSL ℝ N).contDiff.contDiffAt
  exact ((contDiffAt_const.mul (contDiffAt_norm_rpow a hx)).add
    (hN.mul (contDiffAt_norm_rpow (a - 1) hx))).sub
      ((hN.pow 2).mul
        (contDiffAt_norm_rpow (a - 2) hx) |>.div_const 4)

/-- The full coordinate Laplacian of the angular barrier, before angular normalization. -/
theorem laplacian_angularPowerBarrier (a : ℝ) (N : ℝ^n) {x : ℝ^n} (hx : x ≠ 0) :
    laplacian (angularPowerBarrier a N) x =
      2 * a * (a + (n : ℝ) - 2) * ‖x‖ ^ (a - 2) +
        (a - 1) * (a + (n : ℝ) - 1) * inner ℝ N x * ‖x‖ ^ (a - 3) -
        (2 * ‖N‖ ^ 2 * ‖x‖ ^ (a - 2) +
          (a - 2) * (a + (n : ℝ)) * inner ℝ N x ^ 2 * ‖x‖ ^ (a - 4)) / 4 := by
  have hN : ContDiffAt ℝ 2 (fun y ↦ inner ℝ N y) x :=
    (innerSL ℝ N).contDiff.contDiffAt
  have hfirst : ContDiffAt ℝ 2 (fun y : ℝ^n ↦ 2 * ‖y‖ ^ a) x :=
    contDiffAt_const.mul (contDiffAt_norm_rpow a hx)
  have hsecond := hN.mul (contDiffAt_norm_rpow (a - 1) hx)
  have hthird := (hN.pow 2).mul (contDiffAt_norm_rpow (a - 2) hx) |>.div_const 4
  unfold angularPowerBarrier
  rw [laplacian_sub _ _ x (hfirst.add hsecond) hthird,
    laplacian_add _ _ x hfirst hsecond]
  simp only [div_eq_mul_inv]
  rw [show (fun y : ℝ^n ↦ inner ℝ N y ^ 2 * ‖y‖ ^ (a - 2) * (4 : ℝ)⁻¹) =
    (fun y ↦ (4 : ℝ)⁻¹ * (inner ℝ N y ^ 2 * ‖y‖ ^ (a - 2))) by
      funext y; simp [mul_comm]]
  rw [laplacian_const_smul, laplacian_const_smul,
    laplacian_norm_rpow a hx, laplacian_linear_mul_rpow N (a - 1) hx,
    laplacian_linear_sq_mul_rpow N (a - 2) hx]
  simp only [show a - 1 - 2 = a - 3 by ring,
    show a - 2 - 2 = a - 4 by ring]
  ring

end PDE.Elliptic.BoundaryContinuity
