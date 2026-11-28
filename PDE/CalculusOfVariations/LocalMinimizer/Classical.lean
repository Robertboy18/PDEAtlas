/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.LocalMinimizer.Analytic
import PDE.Analysis.Calculus.Gradient.HessianBounds
import PDE.Analysis.Calculus.Gradient.HessianNorm
import PDE.CalculusOfVariations.LocalMinimizer.Convex
import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev

/-!
# Classical solutions of the Euler–Lagrange equation of an analytic gradient energy

## Motivation

Let `F` be real-analytic with `θ |ξ|² ≤ D²F(p)(ξ, ξ) ≤ Λ |ξ|²` and `θ > 0`. The analyticity
theorem for `∫ F(∇u)` is stated for local minimizers in `W^{1,2}_loc`. Is a classical solution
of the Euler–Lagrange equation `div(∇F(∇v)) = 0`, a function with two continuous derivatives,
real-analytic?

## The idea

Yes. The bounds make `F` convex, and for a convex `F` a `C²` solution of the equation is a
local minimizer (`isLocalMinimizerOn_of_contDiffOn_two`). It is in `W^{1,2}_loc` because it is
`C¹`. It is continuous, so it is itself the analytic representative of the minimizer
(`analyticOnNhd_of_isLocalMinimizerOn_of_continuousOn`).

## Main results

* `analyticOnNhd_of_contDiffOn_two` (all dimensions, all open sets, all such `F`, all `C²`
  solutions): a function of class `C²` on `Ω` that solves `div(∇F(∇v)) = 0` at every point of
  `Ω` is real-analytic on `Ω`.

## Relations

* The theorem is `analyticOnNhd_of_isLocalMinimizerOn_of_continuousOn` applied to the local
  minimizer of `isLocalMinimizerOn_of_contDiffOn_two`.
* `isLocalMinimizerOn_iff_exists_analytic` is the statement for functions in `W^{1,2}_loc`:
  the local minimizers are the functions with an analytic representative that solves the
  equation.
* `PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_gradientDensity` is the statement for
  smooth solutions, with pointwise hypotheses on `F`.

## What stays open

Integrands that depend on `x` or `u`, and integrands without a uniform lower and upper bound
on the second derivative.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal Sobolev Gradient

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)} {F : ℝ^n → ℝ} {θ Λ : ℝ}

/-- **A classical solution of the Euler–Lagrange equation is analytic.** Let `Ω ⊆ ℝⁿ` be open
and let `F` be real-analytic on `ℝⁿ` with `θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and
`ξ`, where `θ > 0`. Every function `v` of class `C²` on `Ω` that satisfies
`div(∇F(∇v)) = 0` at every point of `Ω` is real-analytic on `Ω`.

The function `v` is a local minimizer by `isLocalMinimizerOn_of_contDiffOn_two`, and a
continuous local minimizer is analytic by
`analyticOnNhd_of_isLocalMinimizerOn_of_continuousOn`. -/
theorem analyticOnNhd_of_contDiffOn_two (hΩ : IsOpen Ω) (hF : AnalyticOnNhd ℝ F univ)
    (hθ : 0 < θ) (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2)
    {v : ℝ^n → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (hdiv : ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0) :
    AnalyticOnNhd ℝ v Ω := by
  have hF2 : ContDiff ℝ 2 F := hF.contDiff
  have hnorm (p : ℝ^n) : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ.toNNReal :=
    norm_hessian_le_of_quadratic_le hF2.contDiffAt hθ.le (hell p) (hbound p)
  -- a classical solution of the equation of a convex integrand is a local minimizer
  have hmin : IsLocalMinimizerOn F Ω v :=
    isLocalMinimizerOn_of_contDiffOn_two hΩ
      ((strongConvexOn_of_hessian_bound hF2 hell).strictConvexOn hθ).convexOn hF2 hnorm hv hdiv
  have hloc : IsLocallyWkpOn 1 2 Ω v :=
    isLocallyWkpOn_of_contDiffOn hΩ (hv.of_le (by norm_num)) 2
  exact (analyticOnNhd_of_isLocalMinimizerOn_of_continuousOn hΩ hF hθ hell hbound hloc hmin
    hv.continuousOn Filter.EventuallyEq.rfl).1

end PDE.CalculusOfVariations
