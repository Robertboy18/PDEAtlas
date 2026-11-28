/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.LocalMinimizer.Analytic
public import PDE.Examples.CalculusOfVariations.AnalyticDensity
public import PDE.Examples.CalculusOfVariations.LocalMinimizer

/-!
# Analytic local minimizers for two analytic densities

## Motivation

To which densities and to which functions does the analyticity theorem for local minimizers
apply, in every dimension?

## The idea

The density `F(p) = |p|² / 2 + (1 - cos (ℓ p)) / 2` with `‖ℓ‖ ≤ 1` is real-analytic and
`|ξ|² / 2 ≤ D²F(p)(ξ, ξ) ≤ 3 |ξ|² / 2`, so the theorem applies with `θ = 1 / 2` and
`Λ = 3 / 2`. Its Hessian is not constant when `ℓ ≠ 0`. Affine functions are local minimizers on
every set, and on a bounded open set every boundary datum in `H¹` has a minimizer, so the
theorem applies to many functions. For the Dirichlet density `|p|² / 2` the equation is
Laplace's equation, and the theorem says that a local minimizer of the Dirichlet integral has
an analytic harmonic representative.

## Main results

* `exists_analytic_of_isLocalMinimizerOn_cosineDensity` (one family of densities, all
  dimensions, all open sets, all local minimizers in `W^{1,2}_loc`): an analytic
  representative that solves the Euler–Lagrange equation.
* `isLocalMinimizerOn_cosineDensity_affine` (all affine functions, all sets): the hypotheses
  on the function hold.
* `exists_analytic_minimizer_cosineDensity` (all bounded open sets, all boundary data in
  `H¹`): a minimizer with these boundary values that is analytic inside.
* `exists_analytic_harmonic_of_isLocalMinimizerOn` (one density, all dimensions, all open
  sets): local minimizers of the Dirichlet integral have an analytic harmonic representative.

## Relations

The first three results are `exists_analytic_of_isLocalMinimizerOn`,
`isLocalMinimizerOn_affine_of_quadratic_bounds` and
`exists_analytic_minimizer_prescribed_boundary` for the density `cosineDensity ℓ`, with the
bounds `cosineDensity_hessian_lower` and `cosineDensity_hessian_le`. The Dirichlet density is
the member `ℓ = 0` of the family (`cosineDensity_zero`). The last result is
`exists_smooth_harmonic_of_isLocalMinimizerOn` together with
`analyticOnNhd_of_isLocalMinimizerOn_of_continuousOn`. Its conclusion names Laplace's equation,
which the first result for `ℓ = 0` states as `div(∇F(∇v)) = 0`.

## What stays open

Nothing specific to these examples.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.Examples.CalculusOfVariations

open PDE.CalculusOfVariations PDE.Examples.LocalMinimizer

variable {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ} {ℓ : ℝ^n →L[ℝ] ℝ}

/-- **Local minimizers for the cosine density are analytic.** Let `‖ℓ‖ ≤ 1` and let `Ω ⊆ ℝⁿ` be
open. Every local minimizer of `∫ F(∇u)` in `W^{1,2}_loc(Ω)`, for the density
`F(p) = ‖p‖² / 2 + (1 - cos (ℓ p)) / 2`, has a representative that is real-analytic on `Ω` and
solves `div(∇F(∇v)) = 0` there. This is `exists_analytic_of_isLocalMinimizerOn` with
`θ = 1 / 2` and `Λ = 3 / 2`. -/
theorem exists_analytic_of_isLocalMinimizerOn_cosineDensity (hℓ : ‖ℓ‖ ≤ 1) (hΩ : IsOpen Ω)
    (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn (cosineDensity ℓ) Ω u) :
    ∃ v : ℝ^n → ℝ, AnalyticOnNhd ℝ v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
      ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ (cosineDensity ℓ) (∇ v y)) x = 0 :=
  exists_analytic_of_isLocalMinimizerOn hΩ (analyticOnNhd_cosineDensity ℓ) (by norm_num)
    (cosineDensity_hessian_lower hℓ) (cosineDensity_hessian_le hℓ) hu hmin

/-- For `‖ℓ‖ ≤ 1`, every affine function is in `W^{1,2}_loc(Ω)` and is a local minimizer of the
energy of the cosine density on every set `Ω`. So the hypotheses on `u` in
`exists_analytic_of_isLocalMinimizerOn_cosineDensity` hold for these functions. -/
theorem isLocalMinimizerOn_cosineDensity_affine (hℓ : ‖ℓ‖ ≤ 1) (a : ℝ^n) (c : ℝ)
    (Ω : Set (ℝ^n)) :
    IsLocallyWkpOn 1 2 Ω (fun x ↦ ⟪a, x⟫ + c) ∧
      IsLocalMinimizerOn (cosineDensity ℓ) Ω (fun x ↦ ⟪a, x⟫ + c) :=
  isLocalMinimizerOn_affine_of_quadratic_bounds (contDiff_cosineDensity ℓ) (by norm_num)
    (cosineDensity_hessian_lower hℓ) (cosineDensity_hessian_le hℓ) a c Ω

/-- For `‖ℓ‖ ≤ 1`, a bounded open `Ω ⊆ ℝⁿ` and every `g` in `H¹(Ω)`, the energy of the cosine
density has a minimizer among the functions with the boundary values of `g`, and the minimizer
has a representative that is real-analytic on `Ω`. This is
`exists_analytic_minimizer_prescribed_boundary` for this density. -/
theorem exists_analytic_minimizer_cosineDensity (hℓ : ‖ℓ‖ ≤ 1) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (g : H¹(Ω)) :
    ∃ U : H¹(Ω), U - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) ∧
      (∀ W : H¹(Ω), W - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) →
        (∫ x, cosineDensity ℓ (∇ U x) ∂domainMeasure n Ω) ≤
          ∫ x, cosineDensity ℓ (∇ W x) ∂domainMeasure n Ω) ∧
      ∃ v : ℝ^n → ℝ, AnalyticOnNhd ℝ v Ω ∧
        v =ᵐ[volume.restrict Ω] baseRepresentative U ∧
        ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ (cosineDensity ℓ) (∇ v y)) x = 0 :=
  exists_analytic_minimizer_prescribed_boundary hΩ hb (analyticOnNhd_cosineDensity ℓ)
    (by norm_num) (cosineDensity_hessian_lower hℓ) (cosineDensity_hessian_le hℓ) g

/-- The Dirichlet density is the cosine density of the zero functional. -/
theorem cosineDensity_zero : cosineDensity (0 : ℝ^n →L[ℝ] ℝ) = dirichletDensity n := by
  funext p
  simp [cosineDensity, dirichletDensity]

/-- The Dirichlet density `‖p‖² / 2` is real-analytic on `ℝⁿ`: it is the cosine density of the
zero functional. -/
theorem analyticOnNhd_dirichletDensity : AnalyticOnNhd ℝ (dirichletDensity n) univ :=
  cosineDensity_zero (n := n) ▸ analyticOnNhd_cosineDensity 0

/-- **Local minimizers of the Dirichlet integral are analytic and harmonic.** Let `Ω ⊆ ℝⁿ` be
open, in any dimension. Every local minimizer of `∫ |∇u|² / 2` in `W^{1,2}_loc(Ω)` has a
representative that is real-analytic on `Ω` with `Δv = 0` at every point of `Ω`. The smooth
harmonic representative of `exists_smooth_harmonic_of_isLocalMinimizerOn` is continuous, so it
is analytic by `analyticOnNhd_of_isLocalMinimizerOn_of_continuousOn`. -/
theorem exists_analytic_harmonic_of_isLocalMinimizerOn (hΩ : IsOpen Ω)
    (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn (dirichletDensity n) Ω u) :
    ∃ v : ℝ^n → ℝ, AnalyticOnNhd ℝ v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
      ∀ x ∈ Ω, PDE.laplacian v x = 0 := by
  obtain ⟨v, hv, hvu, hharm⟩ := exists_smooth_harmonic_of_isLocalMinimizerOn hΩ hu hmin
  exact ⟨v, (analyticOnNhd_of_isLocalMinimizerOn_of_continuousOn hΩ analyticOnNhd_dirichletDensity
    one_pos (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).ge)
    (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).le) hu hmin hv.continuousOn hvu).1,
    hvu, hharm⟩

end PDE.Examples.CalculusOfVariations
