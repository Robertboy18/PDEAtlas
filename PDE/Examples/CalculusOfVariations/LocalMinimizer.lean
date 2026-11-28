/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.LocalMinimizer.Convex
public import PDE.CalculusOfVariations.LocalMinimizer.Holder
public import PDE.CalculusOfVariations.LocalMinimizer.Smooth
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Local minimizers of the Dirichlet integral

## Motivation

Is there, in every dimension, a smooth density with
`θ |ξ|² ≤ D²F(p)(ξ, ξ) ≤ Λ |ξ|²` and `θ > 0`, as the regularity theorems for local minimizers
ask, and what do these theorems say for the simplest one?

## The idea

The Dirichlet density `F(p) = |p|² / 2` has gradient `∇F(p) = p` and Hessian
`D²F(p)(ξ, η) = ⟨ξ, η⟩`, so both bounds hold with `θ = Λ = 1`. Its Euler–Lagrange equation
`div(∇F(∇v)) = 0` is Laplace's equation. The regularity theorem therefore says that a
local minimizer of the Dirichlet integral has a smooth harmonic representative, and the
characterization says that the local minimizers are exactly the functions with such a
representative. Affine functions give explicit instances on every set.

## Main results

* `dirichletDensity` (one example in each dimension `n`): the density `p ↦ ‖p‖² / 2`, with
  `gradient_dirichletDensity` and `fderiv_fderiv_dirichletDensity`.
* `exists_smooth_harmonic_of_isLocalMinimizerOn` (all `n`, all open `Ω`): every local
  minimizer of the Dirichlet integral in `W^{1,2}_loc(Ω)` has a `C^∞` representative with
  `Δv = 0` at every point of `Ω`.
* `isLocalMinimizerOn_dirichletDensity_iff` (all `n`, all open `Ω`, all `u`): `u` is in
  `W^{1,2}_loc(Ω)` and a local minimizer if and only if it has a `C^∞` representative that
  is harmonic on `Ω`.
* `isLocalMinimizerOn_dirichletDensity_affine` (all `n`, all sets `Ω`, all affine
  functions): the hypotheses of the two results hold for affine functions.
* `exists_holder_gradient_dirichletDensity` (all `n`): the Hölder gradient theorem for
  this density.

## Relations

These are `exists_smooth_of_isLocalMinimizerOn`, `isLocalMinimizerOn_iff_exists_smooth`,
`isLocalMinimizerOn_affine_of_quadratic_bounds` and
`exists_holder_gradient_of_isLocalMinimizerOn` for one density. They show that the
hypotheses of those theorems are satisfiable in every dimension and on every open set.

## What stays open

Nothing specific to this example. The analytic representative is
`PDE.Examples.CalculusOfVariations.exists_analytic_harmonic_of_isLocalMinimizerOn`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.2, for the Dirichlet integral and its
  Euler–Lagrange equation, and §8.3 for the regularity of minimizers.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.Examples.LocalMinimizer

open PDE.CalculusOfVariations

variable {n : ℕ}

/-- The Dirichlet density `F(p) = ‖p‖² / 2` on `ℝⁿ`. Its energy `∫ F(∇u)` is the Dirichlet
integral. -/
def dirichletDensity (n : ℕ) (p : ℝ^n) : ℝ :=
  ‖p‖ ^ 2 / 2

/-- The Dirichlet density is continuously differentiable of every order `m`, the analytic order
`ω` included. -/
theorem contDiff_dirichletDensity {m : WithTop ℕ∞} : ContDiff ℝ m (dirichletDensity n) :=
  (contDiff_norm_sq ℝ).div_const 2

/-- The gradient of the Dirichlet density at `p` is `p`. -/
theorem hasGradientAt_dirichletDensity (p : ℝ^n) : HasGradientAt (dirichletDensity n) p p := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_mul (2⁻¹ : ℝ)
  convert h using 1
  · funext q
    simp only [dirichletDensity]
    ring
  · ext v
    simp

/-- The gradient of the Dirichlet density is the identity: `∇F(p) = p`. -/
@[simp]
theorem gradient_dirichletDensity (p : ℝ^n) : ∇ (dirichletDensity n) p = p :=
  (hasGradientAt_dirichletDensity p).gradient

/-- The Hessian of the Dirichlet density is the inner product: `D²F(p)(ξ, η) = ⟨ξ, η⟩`. -/
theorem fderiv_fderiv_dirichletDensity (p ξ η : ℝ^n) :
    fderiv ℝ (fderiv ℝ (dirichletDensity n)) p ξ η = ⟪ξ, η⟫ := by
  rw [← inner_fderiv_gradient_at contDiff_dirichletDensity.contDiffAt,
    show ∇ (dirichletDensity n) = fun q ↦ q from funext gradient_dirichletDensity]
  simp

/-- The Hessian of the Dirichlet density satisfies both ellipticity bounds with constant
one: `D²F(p)(ξ, ξ) = 1 · ‖ξ‖²`. -/
theorem fderiv_fderiv_dirichletDensity_self (p ξ : ℝ^n) :
    fderiv ℝ (fderiv ℝ (dirichletDensity n)) p ξ ξ = 1 * ‖ξ‖ ^ 2 := by
  rw [fderiv_fderiv_dirichletDensity, real_inner_self_eq_norm_sq, one_mul]

variable {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ}

/-- **Local minimizers of the Dirichlet integral are smooth and harmonic.** Let `Ω ⊆ ℝⁿ`
be open, in any dimension. Every local minimizer of `∫ |∇u|² / 2` in `W^{1,2}_loc(Ω)` has
a representative that is `C^∞` on `Ω` with `Δv = 0` at every point of `Ω`. This is
`exists_smooth_of_isLocalMinimizerOn` with `θ = Λ = 1`. -/
theorem exists_smooth_harmonic_of_isLocalMinimizerOn (hΩ : IsOpen Ω)
    (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn (dirichletDensity n) Ω u) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
      ∀ x ∈ Ω, PDE.laplacian v x = 0 := by
  obtain ⟨v, hv, hvu, heq⟩ := exists_smooth_of_isLocalMinimizerOn hΩ contDiff_dirichletDensity
    one_pos (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).ge)
    (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).le) hu hmin
  refine ⟨v, hv, hvu, fun x hx ↦ ?_⟩
  simpa only [PDE.divergence, PDE.laplacian, gradient_dirichletDensity,
    gradient_apply_eq_partialDeriv] using heq x hx

/-- **Dirichlet's principle, local form.** Let `Ω ⊆ ℝⁿ` be open. A function `u` is in
`W^{1,2}_loc(Ω)` and is a local minimizer of the Dirichlet integral on `Ω` if and only if
it agrees almost everywhere on `Ω` with a function that is `C^∞` and harmonic on `Ω`. This
is `isLocalMinimizerOn_iff_exists_smooth` with `θ = Λ = 1`. -/
theorem isLocalMinimizerOn_dirichletDensity_iff (hΩ : IsOpen Ω) :
    IsLocallyWkpOn 1 2 Ω u ∧ IsLocalMinimizerOn (dirichletDensity n) Ω u ↔
      ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
        ∀ x ∈ Ω, PDE.laplacian v x = 0 := by
  rw [isLocalMinimizerOn_iff_exists_smooth hΩ contDiff_dirichletDensity one_pos
    (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).ge)
    (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).le)]
  simp only [PDE.divergence, gradient_dirichletDensity, gradient_apply_eq_partialDeriv,
    PDE.laplacian]

/-- Affine functions are local minimizers of the Dirichlet integral on every set, and they
are in `W^{1,2}_loc`. So the hypotheses of the theorems of this file are satisfiable. -/
theorem isLocalMinimizerOn_dirichletDensity_affine (a : ℝ^n) (c : ℝ) (Ω : Set (ℝ^n)) :
    IsLocallyWkpOn 1 2 Ω (fun x ↦ ⟪a, x⟫ + c) ∧
      IsLocalMinimizerOn (dirichletDensity n) Ω (fun x ↦ ⟪a, x⟫ + c) :=
  isLocalMinimizerOn_affine_of_quadratic_bounds contDiff_dirichletDensity
    one_pos (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).ge)
    (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).le) a c Ω

/-- The Hölder gradient theorem for the Dirichlet integral: there is an exponent `γ` in
`(0, 1)`, depending on the dimension only, such that every local minimizer in
`W^{1,2}_loc(Ω)` on an open set `Ω` has a `C¹` representative whose gradient is Hölder
continuous with exponent `γ` near each point. This is
`exists_holder_gradient_of_isLocalMinimizerOn` with `θ = Λ = 1`. -/
theorem exists_holder_gradient_dirichletDensity (n : ℕ) :
    ∃ γ : ℝ≥0, 0 < γ ∧ γ < 1 ∧ ∀ (Ω : Set (ℝ^n)), IsOpen Ω → ∀ u : ℝ^n → ℝ,
      IsLocallyWkpOn 1 2 Ω u → IsLocalMinimizerOn (dirichletDensity n) Ω u →
        ∃ v : ℝ^n → ℝ, ContDiffOn ℝ 1 v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
          ∀ x ∈ Ω, ∃ r > 0, ∃ C : ℝ≥0,
            HolderOnWith C γ (fun y ↦ ∇ v y) (Metric.ball x r) := by
  obtain ⟨γ, hγ0, hγ1, h⟩ :=
    exists_holder_gradient_of_isLocalMinimizerOn n (θ := 1) (Λ := 1) one_pos
  exact ⟨γ, hγ0, hγ1, fun Ω hΩ u hu hmin ↦ h Ω hΩ (dirichletDensity n)
    contDiff_dirichletDensity
    (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).ge)
    (fun p ξ ↦ (fderiv_fderiv_dirichletDensity_self p ξ).le) u hu hmin⟩

end PDE.Examples.LocalMinimizer
