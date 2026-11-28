/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.LocalMinimizer.Dirichlet
public import PDE.CalculusOfVariations.LocalMinimizer.Smooth
public import PDE.Elliptic.Regularity.Analytic.GradientDensity

/-!
# Analytic local minimizers of analytic uniformly convex gradient energies

## Motivation

Is a local minimizer of `∫ F(∇u)` in `W^{1,2}_loc(Ω)` real-analytic when `F` is real-analytic
and `θ |ξ|² ≤ D²F(p)(ξ, ξ) ≤ Λ |ξ|²` with `θ > 0`?

## The idea

Yes. The smooth case gives a `C^∞` representative `v` with `div(∇F(∇v)) = 0` at every point of
`Ω` (`exists_smooth_of_isLocalMinimizerOn`). The gradient of a smooth solution solves an
elliptic system whose coefficients `∂ⱼ∂ᵢF` are analytic functions of the gradient. For such a
system the derivatives of order `i` of the solution are at most `i! M Kⁱ` near each point, by a
maximum-principle argument (`PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_gradientDensity`).
So the Taylor series of `v` converges to `v` near each point of `Ω`.

## Main results

* `exists_analytic_of_isLocalMinimizerOn` (all dimensions `n`, all open `Ω ⊆ ℝⁿ`, all densities
  that are real-analytic on `ℝⁿ` with the two bounds, all local minimizers in
  `W^{1,2}_loc(Ω)`): a representative that is real-analytic on `Ω` and satisfies
  `div(∇F(∇v)) = 0` at every point of `Ω`.
* `analyticOnNhd_of_isLocalMinimizerOn_of_continuousOn` (same scope): every continuous
  representative is real-analytic. A continuous local minimizer is analytic as it stands.
* `isLocalMinimizerOn_iff_exists_analytic` (same scope, all functions `u`): `u` is in
  `W^{1,2}_loc(Ω)` and is a local minimizer if and only if it has a real-analytic
  representative on `Ω` that solves the equation at every point.
* `exists_analytic_minimizer_prescribed_boundary` (all bounded open `Ω`, all boundary data in
  `H¹(Ω)`): the energy has a minimizer with the given boundary values, and it has a
  representative that is real-analytic in `Ω`.

## Relations

* `exists_smooth_of_isLocalMinimizerOn` is the same theorem for `C^∞` densities, with a `C^∞`
  representative, and `exists_holder_gradient_of_isLocalMinimizerOn` is the theorem for `C²`
  densities, with a `C^{1,γ}` representative. `exists_analytic_of_isLocalMinimizerOn` is
  `exists_smooth_of_isLocalMinimizerOn` followed by
  `PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_gradientDensity`.
* `isLocalMinimizerOn_iff_exists_analytic` and `isLocalMinimizerOn_iff_exists_smooth` have the
  same left side. For an analytic density of this class, a smooth representative that solves
  the equation is therefore analytic.
* `exists_analytic_minimizer_prescribed_boundary` is
  `exists_smooth_minimizer_prescribed_boundary` with the analytic conclusion. Together with
  `isLocalMinimizerOn_affine_of_quadratic_bounds` it shows that the hypotheses on `u` hold for
  many functions, for every density of the class.
* `PDE.Examples.CalculusOfVariations.exists_analytic_density` gives a density of the class
  whose Hessian is not constant, in every positive dimension.
  `PDE.Examples.CalculusOfVariations.exists_analytic_of_isLocalMinimizerOn_cosineDensity` is
  the theorem for the family of densities it belongs to.

## What stays open

Densities that depend on `x` or `u`, vector-valued `u`, and regularity up to the boundary are
not covered. The radius of convergence of the Taylor series is not estimated.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali multipli
  regolari*, Mem. Accad. Sci. Torino, P. I., III. Ser. 3 (1957), 25–43, and J. Nash,
  *Continuity of solutions of parabolic and elliptic equations*, Amer. J. Math. 80 (1958),
  931–954, <https://doi.org/10.2307/2372841>: Hölder continuity of the first derivatives, the
  step used in `exists_holder_gradient_of_isLocalMinimizerOn`. Cited for the attribution of the
  theorem (see the references of `PDE.CalculusOfVariations.LocalMinimizer.Holder`). The two
  papers were not consulted for the proofs here.
* S. Bernstein, *Sur la nature analytique des solutions des équations aux dérivées partielles du
  second ordre*, Math. Ann. 59 (1904), 20–76, <https://doi.org/10.1007/BF01444746>, and
  C. B. Morrey, *On the analyticity of the solutions of analytic non-linear elliptic systems of
  partial differential equations. I*, Amer. J. Math. 80 (1958), 198–218,
  <https://doi.org/10.2307/2372830>: analyticity of sufficiently regular solutions. Cited for
  the attribution, as in the introduction of Blatt's paper below. The two papers were not
  consulted, and the proof here is a different one (see
  `PDE.Elliptic.Regularity.Analytic.System`).
* S. Blatt, *On the analyticity of solutions to non-linear elliptic partial differential
  equations*, arXiv:2009.08762v2, 2024. <https://arxiv.org/abs/2009.08762>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.CalculusOfVariations

open PDE.Elliptic.Regularity.Analytic

variable {n : ℕ} {Ω : Set (ℝ^n)} {F : ℝ^n → ℝ} {u : ℝ^n → ℝ} {θ Λ : ℝ}

/-- **Analyticity of local minimizers.** Let `Ω ⊆ ℝⁿ` be open, in any dimension, and let `F`
be real-analytic on `ℝⁿ` with `θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and `ξ`, where
`θ > 0`. Every local minimizer of `∫ F(∇u)` in `W^{1,2}_loc(Ω)` has a representative that is
real-analytic on `Ω` and satisfies `div(∇F(∇v)) = 0` at every point of `Ω`.

Nothing is assumed about `u` beyond local square integrability of `u` and `∇u`, and `Ω` need
not be bounded. The representative is the smooth one of `exists_smooth_of_isLocalMinimizerOn`;
it is analytic because its gradient solves an elliptic system with analytic coefficients
(`PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_gradientDensity`). -/
theorem exists_analytic_of_isLocalMinimizerOn (hΩ : IsOpen Ω) (hF : AnalyticOnNhd ℝ F univ)
    (hθ : 0 < θ) (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2)
    (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn F Ω u) :
    ∃ v : ℝ^n → ℝ, AnalyticOnNhd ℝ v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
      ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  obtain ⟨v, hv, hvu, hdiv⟩ :=
    exists_smooth_of_isLocalMinimizerOn hΩ hF.contDiff hθ hell hbound hu hmin
  exact ⟨v, analyticOnNhd_of_gradientDensity hΩ hv (fun _ _ ↦ hF _ (mem_univ _))
    (fun _ _ ↦ ⟨θ, hθ, hell _⟩) hdiv, hvu, hdiv⟩

/-- **A continuous representative is the analytic one.** In the setting of
`exists_analytic_of_isLocalMinimizerOn`, every function `w` that is continuous on `Ω` and equal
to `u` almost everywhere on `Ω` is real-analytic on `Ω` and satisfies `div(∇F(∇w)) = 0` at
every point of `Ω`. With `w = u` this says that a continuous local minimizer is analytic.

The function `w` is smooth and solves the equation by
`contDiffOn_of_isLocalMinimizerOn_of_continuousOn`. -/
theorem analyticOnNhd_of_isLocalMinimizerOn_of_continuousOn (hΩ : IsOpen Ω)
    (hF : AnalyticOnNhd ℝ F univ) (hθ : 0 < θ)
    (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2)
    (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn F Ω u)
    {w : ℝ^n → ℝ} (hw : ContinuousOn w Ω) (hwu : w =ᵐ[volume.restrict Ω] u) :
    AnalyticOnNhd ℝ w Ω ∧ ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ w y)) x = 0 := by
  obtain ⟨hws, hdiv⟩ := contDiffOn_of_isLocalMinimizerOn_of_continuousOn hΩ hF.contDiff hθ hell
    hbound hu hmin hw hwu
  exact ⟨analyticOnNhd_of_gradientDensity hΩ hws (fun _ _ ↦ hF _ (mem_univ _))
    (fun _ _ ↦ ⟨θ, hθ, hell _⟩) hdiv, hdiv⟩

/-- **Local minimizers are exactly the analytic solutions.** Let `Ω ⊆ ℝⁿ` be open and let `F`
be real-analytic on `ℝⁿ` with `θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and `ξ`, where
`θ > 0`. A function `u` is in `W^{1,2}_loc(Ω)` and is a local minimizer of `∫ F(∇u)` on `Ω` if
and only if it agrees almost everywhere on `Ω` with a function that is real-analytic on `Ω`
and satisfies `div(∇F(∇v)) = 0` at every point of `Ω`.

One direction is `exists_analytic_of_isLocalMinimizerOn`. The other is
`isLocalMinimizerOn_iff_exists_smooth`, since an analytic function is smooth. -/
theorem isLocalMinimizerOn_iff_exists_analytic (hΩ : IsOpen Ω) (hF : AnalyticOnNhd ℝ F univ)
    (hθ : 0 < θ) (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2) :
    IsLocallyWkpOn 1 2 Ω u ∧ IsLocalMinimizerOn F Ω u ↔
      ∃ v : ℝ^n → ℝ, AnalyticOnNhd ℝ v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
        ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  refine ⟨fun h ↦ exists_analytic_of_isLocalMinimizerOn hΩ hF hθ hell hbound h.1 h.2, ?_⟩
  rintro ⟨v, hv, hvu, hdiv⟩
  exact (isLocalMinimizerOn_iff_exists_smooth hΩ hF.contDiff hθ hell hbound).mpr
    ⟨v, hv.contDiffOn hΩ.uniqueDiffOn, hvu, hdiv⟩

/-- **Minimizers with prescribed boundary values are analytic inside.** Let `Ω ⊆ ℝⁿ` be bounded
and open, and let `F` be real-analytic on `ℝⁿ` with `θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all
`p` and `ξ`, where `θ > 0`. For every `g` in `H¹(Ω)` there is a minimizer `U` of `∫ F(∇U)`
among the functions of `H¹(Ω)` with `U - g ∈ H¹₀(Ω)`, and `U` has a representative that is
real-analytic on `Ω` and satisfies `div(∇F(∇v)) = 0` at every point of `Ω`.

So the analyticity theorem applies to a function for every boundary datum. The minimizer and
its smooth representative come from `exists_smooth_minimizer_prescribed_boundary`. -/
theorem exists_analytic_minimizer_prescribed_boundary (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hF : AnalyticOnNhd ℝ F univ) (hθ : 0 < θ)
    (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2) (g : H¹(Ω)) :
    ∃ U : H¹(Ω), U - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) ∧
      (∀ W : H¹(Ω), W - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) →
        (∫ x, F (∇ U x) ∂domainMeasure n Ω) ≤ ∫ x, F (∇ W x) ∂domainMeasure n Ω) ∧
      ∃ v : ℝ^n → ℝ, AnalyticOnNhd ℝ v Ω ∧
        v =ᵐ[volume.restrict Ω] baseRepresentative U ∧
        ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  obtain ⟨U, hUg, hmin, v, hv, hvU, hdiv⟩ :=
    exists_smooth_minimizer_prescribed_boundary hΩ hb hF.contDiff hθ hell hbound g
  exact ⟨U, hUg, hmin, v, analyticOnNhd_of_gradientDensity hΩ hv (fun _ _ ↦ hF _ (mem_univ _))
    (fun _ _ ↦ ⟨θ, hθ, hell _⟩) hdiv, hvU, hdiv⟩

end PDE.CalculusOfVariations
