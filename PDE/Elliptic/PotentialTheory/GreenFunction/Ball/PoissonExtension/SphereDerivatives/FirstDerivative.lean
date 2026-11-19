/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Euclidean.Distance
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Definitions
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep
import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.SphereDerivatives.Continuity

/-!
# First derivatives of the ball Poisson extension

For `0 < r`, data `g` continuous on the sphere, and `x₀` inside `B(0, r)`, the integral

`B(x) = ∫_{∂B(0,r)} g(y) / ‖x - y‖ⁿ dS(y)`

is Fréchet differentiable at `x₀`, with derivative obtained by differentiating the kernel
`‖x - y‖⁻ⁿ` under the integral sign. The justification is Mathlib's dominated-differentiation
theorem `hasFDerivAt_integral_of_dominated_of_fderiv_le`: on a small ball around `x₀` that stays
away from the sphere (`exists_ball_away_from_sphere`), the derivative of the kernel is bounded
uniformly in `y`, and `g` is bounded on the compact sphere.

The Poisson extension is `A · B` with the explicit quadratic prefactor
`A(x) = (r² - ‖x‖²) / (n α(n) r)`, so the product rule then yields its derivative and its
differentiability on the open ball.

## Main results

* `hasFDerivAt_sphereIntegral_div_distance_pow`: the Fréchet derivative of `B` at an interior
  point, as `|r|ⁿ⁻¹` times the sphere integral of `g(r • ω) • D(‖· - y‖⁻ⁿ)(x₀)`.
* `differentiableAt_sphereIntegral_div_distance_pow`: differentiability of `B` at interior
  points.
* `hasFDerivAt_poissonBallExtension`: the derivative of the Poisson extension by the product rule,
  `A(x₀) • B'(x₀) + B(x₀) • (-(2/C) • ⟪x₀, ·⟫)`.
* `integrable_smul_invDistPowFDeriv`: integrability over the unit sphere of the weighted
  derivative integrand `g(r • ω) • D(‖x - ·‖⁻ᵏ)(r • ω)`, for any inverse-distance power `k`;
  the interior-regularity and kernel-Laplacian modules both use it.

## Implementation notes

The derivative of the inverse-distance power is taken from
`EuclideanDistance.invDistPowFDerivFormula` in `PDE.FDeriv.Euclidean.Distance`. The factor
`|r|ⁿ⁻¹` is the Jacobian of the parametrisation `ω ↦ r • ω` built into `sphereIntegral`.
-/

@[expose] public section

namespace GreenFunction

open scoped BigOperators

open MeasureTheory
open PDE.Analysis
open PotentialTheory

variable {n : ℕ}

section SphereIntegralFirstDerivative

open scoped Topology

/-- Fréchet derivative under the sphere integral sign at an interior point. -/
theorem hasFDerivAt_sphereIntegral_div_distance_pow {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ Metric.ball (0 : ℝ^n) r) :
    HasFDerivAt
      (fun x : ℝ^n ↦ PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist x y ^ n) 0 r)
      ((|r| ^ (n - 1) : ℝ) •
        (∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          (g (r • (ω : ℝ^n))) • EuclideanDistance.invDistPowFDerivFormula n x₀ (r • (ω : ℝ^n))
            ∂((volume : Measure ℝ^n).toSphere))) x₀ := by
  classical
  unfold PDE.Analysis.sphereIntegral
  have hy (ω : ↑(Metric.sphere (0 : ℝ^n) 1)) := smul_unitSphere_mem_sphere (n := n) hr.le ω
  have hgc : Continuous fun ω : ↑(Metric.sphere (0 : ℝ^n) 1) ↦ g (r • (ω : ℝ^n)) :=
    hg.comp_continuous (continuous_sphere_smul r) hy
  obtain ⟨δ, hδpos, hδ⟩ := exists_ball_away_from_sphere hx₀
  have hI := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := (volume : Measure ℝ^n).toSphere)
    (F := fun x ω ↦ g (r • (ω : ℝ^n)) / dist x (r • (ω : ℝ^n)) ^ n)
    (F' := fun x ω ↦
      g (r • (ω : ℝ^n)) • EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n)))
    (bound := fun ω ↦ (n : ℝ) / δ ^ (n + 1) * |g (r • (ω : ℝ^n))|)
    (Metric.ball_mem_nhds x₀ hδpos)
    (.of_forall fun x ↦ (hgc.measurable.div ((continuous_const.dist
      (continuous_sphere_smul r)).measurable.pow_const n)).aestronglyMeasurable)
    (integrable_poissonBall_integrand hr hg hx₀)
    (hgc.smul (EuclideanDistance.continuous_invDistPowFDerivFormula n continuous_const
      (continuous_sphere_smul r) fun ω ↦ dist_ne_zero.mp
        (distance_ne_zero_of_mem_ball_mem_sphere hx₀ (hy ω)))).aestronglyMeasurable
    (.of_forall fun ω x hx ↦ by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      gcongr
      simpa [div_eq_mul_inv] using EuclideanDistance.norm_invDistPowFDerivFormula_le_of_le_dist
        n hδpos (le_dist_smul_of_mem_ball_away hr.le hδ hx ω))
    (integrable_const_mul_abs_sphere_comp hr hg _)
    (.of_forall fun ω x hx ↦ EuclideanDistance.hasFDerivAt_const_div_dist_pow
      (dist_pos.1 (hδpos.trans_le (le_dist_smul_of_mem_ball_away hr.le hδ hx ω))) _)
  simpa [mul_assoc, smul_eq_mul] using hI.const_mul (|r| ^ (n - 1) : ℝ)

/-- Differentiability of the sphere integral
`x ↦ ∮_{∂B(0,r)} g(y)/|x-y|^n dS(y)` at an interior point, proved by
differentiating under the integral sign on the unit-sphere parameterization. -/
theorem differentiableAt_sphereIntegral_div_distance_pow {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ Metric.ball (0 : ℝ^n) r) :
    DifferentiableAt ℝ
      (fun x : ℝ^n ↦
        PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist x y ^ n) 0 r) x₀ := by
  exact (hasFDerivAt_sphereIntegral_div_distance_pow (n := n) hr hg (x₀ := x₀) hx₀).differentiableAt

/-- The Fréchet derivative of the Poisson extension at an interior point `x₀`, by the product rule
for `u = A · B`: `A(x₀)` times the derivative of the sphere integral (differentiated under the
integral sign) plus `B(x₀)` times the derivative `-(2/C) ⟪x₀, ·⟫` of the quadratic prefactor
`A(z) = (r² - ‖z‖²) / C`, where `C = n α(n) r`. -/
theorem hasFDerivAt_poissonBallExtension {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ Metric.ball (0 : ℝ^n) r) :
    HasFDerivAt (poissonBallExtension (n := n) r g)
      (let C : ℝ := (n : ℝ) * (unitBallVolume n * r)
       let Bderiv : ℝ^n →L[ℝ] ℝ :=
          (|r| ^ (n - 1) : ℝ) •
            (∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
              (g (r • (ω : ℝ^n))) • EuclideanDistance.invDistPowFDerivFormula n x₀ (r • (ω : ℝ^n))
                ∂((volume : Measure ℝ^n).toSphere))
       let A : ℝ^n → ℝ := fun z ↦ (1 / C) * (r ^ 2 - ‖z‖ ^ 2)
       let B : ℝ^n → ℝ :=
          fun z ↦ PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist z y ^ n) 0 r
       A x₀ • Bderiv + B x₀ • (-(2 / C) • innerSL ℝ x₀)) x₀ := by
  let C : ℝ := (n : ℝ) * (unitBallVolume n * r)
  have hEq : poissonBallExtension (n := n) r g = fun z ↦ (1 / C) * (r ^ 2 - ‖z‖ ^ 2) *
      PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist z y ^ n) 0 r := by
    funext z
    simp only [poissonBallExtension, C, div_eq_mul_inv]
    ring
  have hA : HasFDerivAt (fun z : ℝ^n ↦ (1 / C) * (r ^ 2 - ‖z‖ ^ 2))
      (-(2 / C) • innerSL ℝ x₀) x₀ := by
    convert ((hasFDerivAt_const (r ^ 2) x₀).sub
      (hasStrictFDerivAt_norm_sq x₀).hasFDerivAt).const_mul (1 / C) using 1
    ext v
    simp only [smul_apply, sub_apply, zero_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    ring
  rw [hEq]
  exact hA.fun_mul (hasFDerivAt_sphereIntegral_div_distance_pow hr hg hx₀)

/-- The continuous-linear-map-valued derivative integrand for the Poisson
extension is integrable on the unit sphere. -/
theorem integrable_smul_invDistPowFDeriv {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) (k : ℕ) :
    let Y : Type := ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ))
    let μ : Measure Y := (volume : Measure ℝ^n).toSphere
    Integrable (fun ω : Y ↦
      (g (r • (ω : ℝ^n))) • EuclideanDistance.invDistPowFDerivFormula k x (r • (ω : ℝ^n))) μ := by
  intro Y μ
  have hy (ω : Y) := smul_unitSphere_mem_sphere (n := n) hr.le ω
  exact integrableOn_univ.1 (((hg.comp_continuous (continuous_sphere_smul r) hy).smul
    (EuclideanDistance.continuous_invDistPowFDerivFormula k continuous_const
      (continuous_sphere_smul r) fun ω ↦ dist_ne_zero.mp
        (distance_ne_zero_of_mem_ball_mem_sphere hx (hy ω)))).continuousOn.integrableOn_compact
    isCompact_univ)

end SphereIntegralFirstDerivative

end GreenFunction
