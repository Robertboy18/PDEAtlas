/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.WeakEquations

/-!
# The weak eigenvalue density of a sum

Hou, Wang and Yang write their exact eigenpair as `(λ̄ + λ, v̄ + v)` and state the equation (1.18)
of the perturbation `(λ, v)`. Passing between that equation and the equation of the sum needs the
expansions of this module: how the density of the weak eigenvalue equation changes when the
eigenfunction or the eigenvalue is replaced by a sum. The change under a sum of profiles is
`weakEigenDensity_add_representative`, and the profile density of a sum is
`weakProfileDensity_add`.

## Main results

* `NavierStokes.Stationary.gradientRepresentative_add_ae`: in every dimension, each entry of the
  chosen representative of the weak gradient of a sum is the sum of the entries, almost
  everywhere. It is the companion of `Stationary.representative_add_ae`.
* `weakEigenDensity_add_ae`: for all `v`, `w` in `H¹`, the eigenvalue density is additive in the
  eigenfunction, almost everywhere.
* `weakEigenDensity_add_eigenvalue`: at every point, the eigenvalue density for `μ + ν` is that
  for `μ` plus `ν v·φ`.

## How it works

The density is a polynomial in the pointwise values of the fields, so the expansions are algebra
at each point. It is linear in the eigenfunction only almost everywhere, because the chosen
representatives of a sum in `H¹` are the sums of the representatives only almost everywhere. It
is affine in the eigenvalue.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, (1.18).
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

/-- Each entry of the chosen representative of the weak gradient is additive, almost
everywhere. -/
theorem gradientRepresentative_add_ae (v w : H) (i j : Fin n) :
    (fun x ↦ gradientRepresentative (v + w) x i j) =ᵐ[volume]
      fun x ↦ gradientRepresentative v x i j + gradientRepresentative w x i j := by
  have h := Lp.coeFn_add (gradientCLM v i j) (gradientCLM w i j)
  simp only [domainMeasure, Measure.restrict_univ] at h
  simp only [gradientRepresentative, map_add, PiLp.add_apply]
  exact h

end NavierStokes.Stationary

namespace NavierStokes.Nonuniqueness

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- **The eigenvalue density is additive in the eigenfunction**, almost everywhere. -/
theorem weakEigenDensity_add_ae (U : ℝ^3 → ℝ^3) (μ : ℝ) (v w : H) (φ : ℝ^3 → ℝ^3) :
    weakEigenDensity U μ (v + w) φ =ᵐ[volume]
      fun x ↦ weakEigenDensity U μ v φ x + weakEigenDensity U μ w φ x := by
  have hg : ∀ᵐ x ∂volume, ∀ i j : Fin 3, Stationary.gradientRepresentative (v + w) x i j =
      Stationary.gradientRepresentative v x i j + Stationary.gradientRepresentative w x i j :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
      Stationary.gradientRepresentative_add_ae v w i j
  filter_upwards [Stationary.representative_add_ae v w, hg] with x hx hgx
  simp only [weakEigenDensity, hx, hgx, Pi.add_apply, inner_add_left, map_add, inner_add_right,
    Fin.sum_univ_three]
  ring

/-- **A shift of the eigenvalue.** At every point, the eigenvalue density for `μ + ν` is that
for `μ` plus `ν v·φ`. -/
theorem weakEigenDensity_add_eigenvalue (U : ℝ^3 → ℝ^3) (μ ν : ℝ) (v : H) (φ : ℝ^3 → ℝ^3)
    (x : ℝ^3) :
    weakEigenDensity U (μ + ν) v φ x =
      weakEigenDensity U μ v φ x + ν * ⟪Stationary.representative v x, φ x⟫ := by
  simp only [weakEigenDensity]
  ring

end NavierStokes.Nonuniqueness
