/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep

/-!
# Poisson kernel definitions for balls

We define the Poisson extension `poissonBallExtension r g` of data `g` on the sphere
`∂B(0, r)` and the Poisson kernel `ballPoissonKernel r x y = (r² - ‖x‖²) / (n α(n) r ‖x - y‖ⁿ)`,
Evans's Poisson formula (45) and Poisson's kernel for the ball `B(0, r)` in §2.2.4(c), and we
rewrite the extension as the sphere integral of the kernel against `g`
(`poissonBallExtension_eq_sphereIntegral_ballPoissonKernel`). Balls and spheres are Mathlib's
`Metric.ball` and `Metric.sphere`. Both functions are total; the analytic theorems in the
`PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension` modules carry the geometric
hypotheses, such as `0 < r` and interior or boundary points.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(c), Poisson's formula (45) and Poisson's kernel for
  `B(0, r)`, p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open PDE.Analysis
open PotentialTheory

/-- The Poisson extension for a ball of radius `r`, given by Evans's Poisson formula (45).

As a Lean function this is total in `r`; the continuity, differentiability, and harmonicity
theorems in the `PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension` modules assume
`0 < r`. -/
noncomputable def poissonBallExtension {n : ℕ} (r : ℝ)
    (g : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  (r ^ 2 - ‖x‖ ^ 2) / (n * unitBallVolume n * r) *
    PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist x y ^ n) 0 r

/-- Poisson kernel for a ball of radius `r`.

The PDE interpretation is for `0 < n`, `0 < r`, an interior point `‖x‖ < r`, and a boundary
point `‖y‖ = r`. The definition is total, allowing algebraic rewrites without side conditions. -/
noncomputable def ballPoissonKernel {n : ℕ} (r : ℝ)
    (x : ℝ^n) (y : ℝ^n) : ℝ :=
  (r ^ 2 - ‖x‖ ^ 2) / (n * unitBallVolume n * r * dist x y ^ n)

/-- Algebraic rewrite of the ball Poisson extension as a sphere integral against the kernel.

Harmonicity and boundary convergence, under `0 < r` and continuity of the boundary data, are in
the `PoissonExtension` modules. -/
theorem poissonBallExtension_eq_sphereIntegral_ballPoissonKernel {n : ℕ}
    (r : ℝ) (g : ℝ^n → ℝ) (x : ℝ^n) :
    poissonBallExtension (n := n) r g x =
      PDE.Analysis.sphereIntegral n
        (fun y ↦ ballPoissonKernel (n := n) r x y * g y) 0 r := by
  classical
  -- Constant multiplication commutes with the total integral, including degenerate radii.
  unfold poissonBallExtension ballPoissonKernel PDE.Analysis.sphereIntegral
  simp only [div_eq_mul_inv, mul_inv_rev, zero_add]
  have hi : (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
      (r ^ 2 - ‖x‖ ^ 2) * ((dist x (r • (ω : ℝ^n)) ^ n)⁻¹ *
        (r⁻¹ * ((unitBallVolume n)⁻¹ * (n : ℝ)⁻¹))) * g (r • (ω : ℝ^n))) =
      fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        ((r ^ 2 - ‖x‖ ^ 2) * (r⁻¹ * ((unitBallVolume n)⁻¹ * (n : ℝ)⁻¹))) *
        (g (r • (ω : ℝ^n)) * (dist x (r • (ω : ℝ^n)) ^ n)⁻¹) := by
    funext ω
    ring
  rw [hi, MeasureTheory.integral_const_mul]
  ring

/-- The Poisson extension depends only on the values of its data on the boundary sphere. -/
theorem poissonBallExtension_congr {n : ℕ} {r : ℝ} (hr : 0 < r)
    {g h : ℝ^n → ℝ} (hgh : Set.EqOn g h (Metric.sphere (0 : ℝ^n) r)) :
    poissonBallExtension r g = poissonBallExtension r h := by
  funext x
  unfold poissonBallExtension
  congr 1
  apply sphereIntegral_congr_on_sphere hr
  intro y hy
  exact congrArg (fun z : ℝ ↦ z / dist x y ^ n) (hgh hy)

end GreenFunction
