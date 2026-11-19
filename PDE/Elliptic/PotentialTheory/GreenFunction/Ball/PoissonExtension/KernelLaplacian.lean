/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.KernelLaplacian.SphereIntegral
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep
import PDE.FDeriv.Calculus
import PDE.FDeriv.Laplacian.Product
import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.InteriorRegularity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Laplacian of the ball Poisson extension

The Poisson kernel of the ball `B(0, r)`,

`K(x, y) = (r² - ‖x‖²) / (n α(n) r ‖x - y‖ⁿ)`,

is harmonic in `x` for each fixed `y` on the sphere `‖y‖ = r`. We prove the integrated form of
that statement: for boundary data `g` continuous on the sphere, the Poisson extension
`u = poissonBallExtension r g` has vanishing coordinate Laplacian at every interior point, which
is part (ii) of Evans's §2.2.4(c), Theorem 15.

## Main results

* `laplacian_poissonBallExtension_eq_zero`: for `0 < r`, `g` continuous on the boundary sphere,
  and `x ∈ B(0, r)`,
  `Δ (poissonBallExtension r g) x = 0`.

## How it works

Evans obtains the harmonicity of the half-space kernel in step 1 of his proof of Theorem 14 from
the symmetry of Green's function and leaves the ball case as an exercise; we compute directly.
Write `u = A · B` with `A(x) = (r² - ‖x‖²) / (n α(n) r)` and
`B(x) = ∫_{∂B(0,r)} g(y) ‖x - y‖⁻ⁿ dS(y)`. The Leibniz rule gives
`Δu = (ΔA) B + 2 ∇A · ∇B + A ΔB`, and the derivatives of `B` are computed under the integral sign
in `KernelLaplacian.ScalarDerivatives` and `KernelLaplacian.SphereIntegral`. Collecting the three
terms inside a single sphere integral, the integrand is

`-2n / dⁿ + 4n x · (x - y) / dⁿ⁺² + 2n (r² - ‖x‖²) / dⁿ⁺²`, with `d = ‖x - y‖`,

which vanishes identically once `‖y‖² = r²` is substituted into `d² = ‖x‖² - 2 x · y + ‖y‖²`. The
cancellation is pointwise on the sphere, so no further integration identity is needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), step 1 of the proof of Theorem 14, p. 38;
  §2.2.4(c), Poisson's kernel for `B(0, r)` and Theorem 15 (Poisson's formula for ball), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/
@[expose] public section

open PDE (partialDeriv laplacian)

namespace GreenFunction

open scoped BigOperators

open MeasureTheory
open PDE.Analysis
open PotentialTheory

variable {n : ℕ}

open KernelLaplacian

private theorem sum_coord_partial_sphereIntegral
    {r : ℝ} (hr : 0 < r) {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
      (∑ i : Fin n, x i * (∂[i]
          (fun z : ℝ^n ↦ sphereIntegral n (fun y ↦ g y / dist z y ^ n) 0 r)) x) =
        (|r| ^ (n - 1) : ℝ) *
          ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
            g (r • (ω : ℝ^n)) * EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n)) x
            ∂((volume : Measure ℝ^n).toSphere) := by
  let B : ℝ^n → ℝ := fun z ↦ sphereIntegral n (fun y ↦ g y / dist z y ^ n) 0 r
  have hHas : HasFDerivAt B ((|r| ^ (n - 1) : ℝ) • (∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
      (g (r • (ω : ℝ^n))) • EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n))
        ∂((volume : Measure ℝ^n).toSphere))) x := by
    simpa [B] using hasFDerivAt_sphereIntegral_div_distance_pow (n := n) (r := r) hr hg (x₀ := x) hx
  have hInt := integrable_smul_invDistPowFDeriv (n := n) (r := r) hr hg (x := x) hx n
  calc (∑ i : Fin n, x i * (∂[i] B) x) = fderiv ℝ B x x := by
        simpa [mul_comm] using (PDE.fderiv_apply_eq_sum_partialDeriv_mul (n := n) B x x).symm
    _ = _ := by simp [hHas.fderiv, ContinuousLinearMap.integral_apply hInt, smul_eq_mul]


/-- Cancellation of the three product-rule terms for the ball kernel. -/
private theorem poisson_kernel_leibniz_cancel
    (r C q : ℝ) {x y : ℝ^n} (hxy : x ≠ y) (hy : ‖y‖ = r) :
    (-(2 / C) * n) * (q / dist x y ^ n) +
        (-(4 / C)) * (q * EuclideanDistance.invDistPowFDerivFormula n x y x) +
        ((r ^ 2 - ‖x‖ ^ 2) / C) * (q * (2 * n / dist x y ^ (n + 2))) = 0 := by
  have hd : dist x y ≠ 0 := dist_ne_zero.mpr hxy
  have hdiv : q / dist x y ^ n = q * dist x y ^ 2 / dist x y ^ (n + 2) := by
    rw [pow_add]
    exact (mul_div_mul_right q _ (pow_ne_zero 2 hd)).symm
  have hnum : -(dist x y ^ 2) + 2 * (innerSL ℝ x) (x - y) +
      (r ^ 2 - ‖x‖ ^ 2) = 0 := by
    simp only [dist_eq_norm, norm_sub_sq_real, innerSL_apply_apply,
      inner_sub_right, real_inner_self_eq_norm_sq, hy]
    ring
  rw [hdiv, EuclideanDistance.invDistPowFDerivFormula_apply_eq_of_ne n hxy]
  calc
    _ = q * (2 * n / C) *
        ((-(dist x y ^ 2) + 2 * (innerSL ℝ x) (x - y) +
          (r ^ 2 - ‖x‖ ^ 2)) / dist x y ^ (n + 2)) := by ring
    _ = 0 := by rw [hnum]; simp

/-- The Poisson extension has zero coordinate Laplacian at every interior
point of a positive-radius ball. -/
theorem laplacian_poissonBallExtension_eq_zero {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
    laplacian (n := n) (poissonBallExtension (n := n) r g) x = 0 := by
  classical
  let C : ℝ := (n : ℝ) * (unitBallVolume n * r)
  let A : ℝ^n → ℝ := fun z ↦ C⁻¹ * (r ^ 2 - ‖z‖ ^ 2)
  let B : ℝ^n → ℝ := fun z ↦ sphereIntegral n (fun y ↦ g y / dist z y ^ n) 0 r
  have hu : poissonBallExtension (n := n) r g = fun z ↦ A z * B z := by
    funext z
    simp only [poissonBallExtension, A, B, C, div_eq_mul_inv]
    ring
  have hA : ContDiff ℝ 2 A := contDiff_const.mul
    (contDiff_const.sub (contDiff_norm_sq ℝ))
  have hB : ContDiffAt ℝ 2 B x :=
    contDiffAt_sphereIntegral_div_distance_pow hr hg hx
  have hpdA (i : Fin n) : (∂[i] A) x = -(2 / C) * x i := by
    have hscale := PDE.partialDeriv_const_smul (n := n) (E := ℝ) C⁻¹
      (i := i) (f := fun z : ℝ^n ↦ r ^ 2 - ‖z‖ ^ 2) (x := x)
    rw [PDE.partialDeriv_sub (differentiableAt_const (r ^ 2))
      (hasStrictFDerivAt_norm_sq (F := ℝ^n) x).hasFDerivAt.differentiableAt,
      EuclideanLaplacian.partialDeriv_norm_sq] at hscale
    simpa [A, smul_eq_mul, partialDeriv, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using hscale
  have hlapA : laplacian A x = -(2 / C) * n := by
    rw [PDE.laplacian_const_smul, PDE.laplacian_sub _ _ _ contDiffAt_const
      (contDiff_norm_sq ℝ).contDiffAt, PDE.laplacian_const, EuclideanLaplacian.laplacian_norm_sq]
    simp only [div_eq_mul_inv, zero_sub]
    ring
  have hLap : laplacian (fun z ↦ A z * B z) x =
      (-(2 / C) * n) * B x +
        (-(4 / C)) * (∑ i : Fin n, x i * (∂[i] B) x) +
        A x * laplacian B x := by
    rw [PDE.laplacian_mul hA.contDiffAt hB, hlapA]
    simp_rw [hpdA, mul_assoc, ← Finset.mul_sum]
    ring
  let Y := Metric.sphere (0 : ℝ^n) 1
  let μ : Measure Y := (volume : Measure ℝ^n).toSphere
  let yOf : Y → ℝ^n := fun ω ↦ r • (ω : ℝ^n)
  let f0 : Y → ℝ := fun ω ↦ g (yOf ω) / dist x (yOf ω) ^ n
  let f1 : Y → ℝ := fun ω ↦
    g (yOf ω) * EuclideanDistance.invDistPowFDerivFormula n x (yOf ω) x
  let f2 : Y → ℝ := fun ω ↦ g (yOf ω) * (2 * n / dist x (yOf ω) ^ (n + 2))
  have hy (ω : Y) : yOf ω ∈ Metric.sphere (0 : ℝ^n) r :=
    smul_unitSphere_mem_sphere hr.le ω
  have hf0 : Integrable f0 μ := integrable_poissonBall_integrand hr hg hx
  have hf1 : Integrable f1 μ := by
    have hφ := integrable_smul_invDistPowFDeriv hr hg hx n
    simpa [f1, yOf, μ, Y, smul_eq_mul] using
      (ContinuousLinearMap.apply ℝ ℝ x).integrable_comp hφ
  have hf2 : Integrable f2 μ := by
    have hc : Continuous f2 := (hg.comp_continuous
      (continuous_sphere_smul r) (smul_unitSphere_mem_sphere hr.le)).mul
      (continuous_const.div ((continuous_const.dist (continuous_sphere_smul r)).pow _)
        (fun ω ↦ pow_ne_zero _ (distance_ne_zero_of_mem_ball_mem_sphere hx (hy ω))))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hB0 : B x = |r| ^ (n - 1) * ∫ ω, f0 ω ∂μ := by
    simp [B, f0, μ, yOf, Y, sphereIntegral]
  have hB1 : (∑ i : Fin n, x i * (∂[i] B) x) =
      |r| ^ (n - 1) * ∫ ω, f1 ω ∂μ := sum_coord_partial_sphereIntegral hr hg hx
  have hB2 : laplacian B x = |r| ^ (n - 1) * ∫ ω, f2 ω ∂μ :=
    laplacian_sphereIntegral_div_distance_pow_scalar hr hg hx
  rw [hu, hLap, hB0, hB1, hB2]
  have hzero (ω : Y) : (-(2 / C) * n) * f0 ω + (-(4 / C)) * f1 ω + A x * f2 ω = 0 := by
    simpa [f0, f1, f2, A, div_eq_mul_inv, mul_comm] using poisson_kernel_leibniz_cancel r C
      (g (yOf ω)) (dist_ne_zero.mp (distance_ne_zero_of_mem_ball_mem_sphere hx (hy ω)))
      (by simpa [Metric.mem_sphere, dist_zero_right] using hy ω)
  have h := integral_congr_ae (μ := μ) (.of_forall hzero)
  rw [integral_add (f := fun ω ↦ (-(2 / C) * n) * f0 ω + (-(4 / C)) * f1 ω)
      (g := fun ω ↦ A x * f2 ω) ((hf0.const_mul _).add (hf1.const_mul _)) (hf2.const_mul _),
    integral_add (hf0.const_mul _) (hf1.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_zero] at h
  linear_combination |r| ^ (n - 1) * h

end GreenFunction
