/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.LocalMinimizer.Basic
public import PDE.FDeriv.Operators
import PDE.Analysis.Calculus.Gradient.HessianNorm
import PDE.CalculusOfVariations.LocalMinimizer.Convex
import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.SmoothSolution
import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev

/-!
# Smooth local minimizers of smooth uniformly convex gradient energies

## Motivation

Is a local minimizer of `∫ F(∇u)` in `W^{1,2}_loc(Ω)` smooth when `F` is
smooth and `θ |ξ|² ≤ D²F(p)(ξ, ξ) ≤ Λ |ξ|²` with `θ > 0`?

## The idea

A local minimizer is a weak solution of `div(∇F(∇u)) = 0` on small balls
(`IsLocalMinimizerOn.exists_ball_weakSolution`). On a ball the interior theory for weak
solutions on bounded open sets applies. Difference quotients give second weak derivatives.
Each first derivative of `u` then solves a linear equation with the measurable coefficients
`D²F(∇u)`, and De Giorgi's theorem makes it Hölder continuous. The coefficients are now
Hölder continuous, and Schauder estimates give one more derivative of `u` for each further
derivative of `F`. This produces a regular representative on each ball. Two continuous
functions that agree almost everywhere on an open set agree everywhere on it, so the
representatives on balls are restrictions of one function on `Ω`. The equation is local as
well: on a ball, a `C²` representative of `u` is the `C²` representative of the weak
solution there, and integration by parts against test functions gives the equation at each
point. In dimension zero the space is a point and every statement is trivial, so the
theorems carry no hypothesis on the dimension.

## Main results

* `exists_smooth_of_isLocalMinimizerOn` (all dimensions `n`, all open `Ω ⊆ ℝⁿ`, all `C^∞`
  densities with the two bounds, all local minimizers in `W^{1,2}_loc(Ω)`): a `C^∞`
  representative on `Ω` that satisfies `div(∇F(∇v)) = 0` at every point of `Ω`.
* `exists_classical_of_isLocalMinimizerOn` (same scope, for `C³` densities): a `C²`
  representative with the same pointwise equation.
* `IsLocalMinimizerOn.divergence_eq_zero` (all open `Ω`, all `C²` densities with bounded
  Hessian, convex or not, all local minimizers): every `C²` representative solves the equation
  at every point.
* `IsLocalMinimizerOn.exists_contDiffOn_divergence_eq_zero` (family, every order `k ≥ 2`):
  the common form of the first two results. A regularity theorem for weak solutions on
  balls in positive dimension is its hypothesis.
* `contDiffOn_of_isLocalMinimizerOn_of_continuousOn` (scope of the first result): every
  continuous representative is smooth and solves the equation. A continuous local minimizer
  is therefore smooth as it stands.
* `isLocalMinimizerOn_iff_exists_smooth` (scope of the first result, all functions `u`):
  `u` is in `W^{1,2}_loc(Ω)` and is a local minimizer if and only if it has a `C^∞`
  representative on `Ω` that solves the equation at every point.

## Relations

* `exists_smooth_solution_of_gradientDensity`,
  `exists_contDiffOn_two_representative_of_gradientDensity` and
  `neg_divergence_gradientDensity_eq_zero_of_representative` are the inputs. They treat an
  `H¹` weak solution on a bounded open set in positive dimension. Here the set is any open
  set, the function is only locally in `W^{1,2}`, and the dimension is arbitrary.
* `PDE.Analysis.norm_hessian_le_of_quadratic_le` turns the two quadratic-form bounds into the
  Hessian norm bound of those theorems.
* `exists_holder_gradient_of_isLocalMinimizerOn` in
  `PDE.CalculusOfVariations.LocalMinimizer.Holder` is the result for `C²` densities, and
  `exists_holder_exponent_gradient_of_isLocalMinimizerOn` there applies to the
  representatives constructed here.
* `isLocalMinimizerOn_of_contDiffOn_two` in `PDE.CalculusOfVariations.LocalMinimizer.Convex`
  is the converse used in `isLocalMinimizerOn_iff_exists_smooth`, and
  `isLocalMinimizerOn_affine_of_quadratic_bounds` there gives functions that satisfy the
  hypotheses. `PDE.CalculusOfVariations.LocalMinimizer.Dirichlet` gives more of them.
* `exists_analytic_of_isLocalMinimizerOn` in `PDE.CalculusOfVariations.LocalMinimizer.Analytic`
  is the theorem for real-analytic densities: the smooth representative constructed here is
  real-analytic.

## What stays open

No estimate of the derivatives of the representative is stated. Densities that depend on `x`
or `u`, systems, and regularity up to the boundary are not covered.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.3, for the regularity of minimizers: second
  derivative estimates in §8.3.1 and the passage to smoothness in §8.3.2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.CalculusOfVariations

open PDE.Elliptic.Regularity.Quasilinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {F : ℝ^n → ℝ} {u : ℝ^n → ℝ}

/-- **Every `C²` representative solves the Euler–Lagrange equation.** Let `Ω` be open, let
`F` be `C²` with bounded Hessian, and let `u` be a local minimizer of `∫ F(∇u)`. If `v` is
`C²` on `Ω` and equals `u` almost everywhere on `Ω`, then `div(∇F(∇v)) = 0` at every point
of `Ω`.

No convexity is needed, and `u` is in `W^{1,2}_loc(Ω)` because `v` is. Near the point, `v`
represents a weak solution on a ball, and
`neg_divergence_gradientDensity_eq_zero_of_representative` integrates by parts there. -/
theorem IsLocalMinimizerOn.divergence_eq_zero (hmin : IsLocalMinimizerOn F Ω u)
    (hΩ : IsOpen Ω) (hF : ContDiff ℝ 2 F) {Λ : ℝ≥0}
    (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ)
    {v : ℝ^n → ℝ} (hv : ContDiffOn ℝ 2 v Ω) (hvu : v =ᵐ[volume.restrict Ω] u)
    {x : ℝ^n} (hx : x ∈ Ω) :
    PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  have hu : IsLocallyWkpOn 1 2 Ω u :=
    (isLocallyWkpOn_of_contDiffOn hΩ (hv.of_le (by norm_num)) 2).congr_ae hvu
  obtain ⟨r, hr, hrΩ, U, hU, hweak⟩ := hmin.exists_ball_weakSolution hΩ
    (hF.differentiable (by norm_num)) (lipschitzWith_gradient_of_hessian_bound hF hbound) hu hx
  have hva : v =ᵐ[domainMeasure n (ball x r)] wkpBaseCoordinateCLM U :=
    Filter.EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset hrΩ hvu) hU.symm
  exact neg_eq_zero.mp ((neg_divergence_gradientDensity_eq_zero_of_representative isOpen_ball
    isBounded_ball hF hbound U hweak (hv.mono hrΩ) hva).2 x (mem_ball_self hr))

/-- **Regular representative and pointwise equation, from regularity on balls.** Let `Ω` be
open, let `F` be `C²` with bounded Hessian, and let `u` in `W^{1,2}_loc(Ω)` be a local
minimizer. Fix an order `k ≥ 2`. Suppose that, in positive dimension, every weak solution
on a ball has a `C^k` representative on that ball. Then `u` has a `C^k` representative on
`Ω`, and it satisfies `div(∇F(∇v)) = 0` at every point of `Ω`.

This is the one proof behind the `C²` and the `C^∞` theorems below. Every order `k ≥ 2` is
allowed, the analytic order `ω` included. In dimension zero `u` itself is the
representative. -/
theorem IsLocalMinimizerOn.exists_contDiffOn_divergence_eq_zero {k : WithTop ℕ∞}
    (hk : 2 ≤ k) (hmin : IsLocalMinimizerOn F Ω u) (hΩ : IsOpen Ω) (hF : ContDiff ℝ 2 F)
    {Λ : ℝ≥0} (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ) (hu : IsLocallyWkpOn 1 2 Ω u)
    (hreg : 0 < n → ∀ (x : ℝ^n) (r : ℝ), 0 < r → ∀ U : H¹(ball x r),
      (∀ w : H¹₀(ball x r),
        (∫ y, ⟪∇ F (∇ U y), ∇ (w : H¹(ball x r)) y⟫ ∂domainMeasure n (ball x r)) = 0) →
      ∃ v : ℝ^n → ℝ, ContDiffOn ℝ k v (ball x r) ∧
        v =ᵐ[volume.restrict (ball x r)] baseRepresentative U) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ k v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
      ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i₀⟩⟩
  · -- `ℝ^0` is a point: `u` is constant, and the divergence is an empty sum.
    exact ⟨u, (contDiffOn_const (c := u 0)).congr fun x _ ↦ congrArg u (Subsingleton.elim x 0),
      .rfl, fun x _ ↦ by simp [PDE.divergence]⟩
  · obtain ⟨v, hv, hvu⟩ := hmin.exists_contDiffOn_ae_eq hΩ (hF.differentiable (by norm_num))
      (lipschitzWith_gradient_of_hessian_bound hF hbound) hu fun x r hr U hU ↦ by
        obtain ⟨v, hv, hvU⟩ := hreg i₀.pos x r hr U hU
        exact ⟨ball x r, isOpen_ball, mem_ball_self hr, Subset.rfl, v, hv, hvU⟩
    exact ⟨v, hv, hvu, fun x hx ↦
      hmin.divergence_eq_zero hΩ hF hbound (hv.of_le hk) hvu hx⟩

variable {θ Λ : ℝ}

/-- **Classical regularity of local minimizers.** Let `Ω ⊆ ℝⁿ` be open, in any dimension,
and let `F` be `C³` with `θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and `ξ`, where
`θ > 0`. Every local minimizer of `∫ F(∇u)` in `W^{1,2}_loc(Ω)` has a representative that
is `C²` on `Ω` and satisfies `div(∇F(∇v)) = 0` at every point of `Ω`.

So the representative is a classical solution of the Euler–Lagrange equation. The proof applies
`exists_contDiffOn_two_representative_of_gradientDensity` on balls and glues. -/
theorem exists_classical_of_isLocalMinimizerOn (hΩ : IsOpen Ω) (hF : ContDiff ℝ 3 F)
    (hθ : 0 < θ) (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2)
    (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn F Ω u) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ 2 v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
      ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hnorm (p : ℝ^n) : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ.toNNReal :=
    norm_hessian_le_of_quadratic_le hF2.contDiffAt hθ.le (hell p) (hbound p)
  refine hmin.exists_contDiffOn_divergence_eq_zero le_rfl hΩ hF2 hnorm hu
    fun hn x r hr U hU ↦ ?_
  have : Fact (0 < n) := ⟨hn⟩
  obtain ⟨q, hq2, hq⟩ := exists_auxiliary_exponent (n := n)
  exact exists_contDiffOn_two_representative_of_gradientDensity hq2 hq isOpen_ball
    isBounded_ball hF hnorm hθ hell U hU

/-- **Smoothness of local minimizers.** Let `Ω ⊆ ℝⁿ` be open, in any dimension, and let `F`
be `C^∞` with `θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and `ξ`, where `θ > 0`. Every
local minimizer of `∫ F(∇u)` in `W^{1,2}_loc(Ω)` has a representative that is `C^∞` on `Ω` and
satisfies `div(∇F(∇v)) = 0` at every point of `Ω`.

Nothing is assumed about `u` beyond local square integrability of `u` and `∇u`, and `Ω`
need not be bounded. The proof applies `exists_smooth_solution_of_gradientDensity` on balls
and glues the representatives, which agree on overlaps. -/
theorem exists_smooth_of_isLocalMinimizerOn (hΩ : IsOpen Ω) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hθ : 0 < θ) (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2)
    (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn F Ω u) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
      ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  have hnorm (p : ℝ^n) : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ.toNNReal :=
    norm_hessian_le_of_quadratic_le hF2.contDiffAt hθ.le (hell p) (hbound p)
  refine hmin.exists_contDiffOn_divergence_eq_zero (by simp) hΩ hF2 hnorm hu
    fun hn x r hr U hU ↦ ?_
  have : Fact (0 < n) := ⟨hn⟩
  obtain ⟨v, hv, hvU, -, -⟩ := exists_smooth_solution_of_gradientDensity isOpen_ball
    isBounded_ball hF hnorm hθ hell U hU
  exact ⟨v, hv, hvU⟩

/-- **A continuous representative is the smooth one.** In the setting of
`exists_smooth_of_isLocalMinimizerOn`, every function `w` that is continuous on `Ω` and
equal to `u` almost everywhere on `Ω` is `C^∞` on `Ω` and satisfies `div(∇F(∇w)) = 0` at
every point of `Ω`. With `w = u` this says that a continuous local minimizer is smooth.

Two continuous functions that agree almost everywhere on an open set agree on it, so `w`
is the representative of `exists_smooth_of_isLocalMinimizerOn`. -/
theorem contDiffOn_of_isLocalMinimizerOn_of_continuousOn (hΩ : IsOpen Ω)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hθ : 0 < θ)
    (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2)
    (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn F Ω u)
    {w : ℝ^n → ℝ} (hw : ContinuousOn w Ω) (hwu : w =ᵐ[volume.restrict Ω] u) :
    ContDiffOn ℝ (⊤ : ℕ∞) w Ω ∧ ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ w y)) x = 0 := by
  obtain ⟨v, hv, hvu, -⟩ := exists_smooth_of_isLocalMinimizerOn hΩ hF hθ hell hbound hu hmin
  have hwv : EqOn w v Ω :=
    Measure.eqOn_open_of_ae_eq (hwu.trans hvu.symm) hΩ hw hv.continuousOn
  have hws : ContDiffOn ℝ (⊤ : ℕ∞) w Ω := hv.congr hwv
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  exact ⟨hws, fun x hx ↦ hmin.divergence_eq_zero hΩ hF2
    (fun p ↦ norm_hessian_le_of_quadratic_le hF2.contDiffAt hθ.le (hell p) (hbound p))
    (hws.of_le (by simp)) hwu hx⟩

/-- **Local minimizers are exactly the smooth solutions.** Let `Ω ⊆ ℝⁿ` be open and let
`F` be `C^∞` with `θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and `ξ`, where `θ > 0`. A
function `u` is in `W^{1,2}_loc(Ω)` and is a local minimizer of `∫ F(∇u)` on `Ω` if and only
if it agrees almost everywhere on `Ω` with a function that is `C^∞` on `Ω` and satisfies
`div(∇F(∇v)) = 0` at every point of `Ω`.

One direction is `exists_smooth_of_isLocalMinimizerOn`. The other is
`isLocalMinimizerOn_of_contDiffOn_two`: `F` is convex, so a classical solution minimizes. -/
theorem isLocalMinimizerOn_iff_exists_smooth (hΩ : IsOpen Ω) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hθ : 0 < θ) (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2) :
    IsLocallyWkpOn 1 2 Ω u ∧ IsLocalMinimizerOn F Ω u ↔
      ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
        ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  refine ⟨fun h ↦ exists_smooth_of_isLocalMinimizerOn hΩ hF hθ hell hbound h.1 h.2, ?_⟩
  rintro ⟨v, hv, hvu, hdiv⟩
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  exact ⟨(isLocallyWkpOn_of_contDiffOn hΩ (hv.of_le (by simp)) 2).congr_ae hvu,
    (isLocalMinimizerOn_of_contDiffOn_two hΩ
      ((strongConvexOn_of_hessian_bound hF2 hell).strictConvexOn hθ).convexOn hF2
      (fun p ↦ norm_hessian_le_of_quadratic_le hF2.contDiffAt hθ.le (hell p) (hbound p))
      (hv.of_le (by simp)) hdiv).congr_ae hvu⟩

end PDE.CalculusOfVariations
