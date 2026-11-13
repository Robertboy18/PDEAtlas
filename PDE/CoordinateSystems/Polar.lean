/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import PDE.CoordinateSystems.Radial
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The planar Laplacian in polar coordinates

We define the planar polar Laplacian, the differential expression

`uᵣᵣ + r⁻¹ uᵣ + r⁻² uββ`,

and compute it on homogeneous angular modes `rᵐ f(β)`. Multiplying by a radial cutoff `χ(r)`
adds the usual radial product terms (`planarPolarLaplacian_radial_mul`); for a cut-off mode
the two extra terms are the exact cutoff commutator (`planarPolarLaplacian_cutoff_rpow_mul`).
The operator is a total real-valued definition; the coordinate-change identities require
`r ≠ 0`, and standard polar coordinates use `r > 0`.

The coordinate-change results are proved in `PDE.FDeriv.Polar.Laplacian`.
`EuclideanLaplacian.planarPolarLaplacianParam_comp_planarPolarMap` identifies this
expression on a `C²` Cartesian field's pullback with its Euclidean Laplacian.
`EuclideanLaplacian.laplacian_eq_planarPolarLaplacian_of_pullback` handles profiles
that agree with the pullback near the point in question.

On functions of `r` alone the expression is the radial formula `Δu = v'' + (n - 1)/r v'` of
Evans, §2.2.1(a), with `n = 2`; the angular term does not occur there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(a), p. 22.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.CoordinateSystems

attribute [local instance 2000] WithLp.instAddCommGroup WithLp.instModule

/-- The Cartesian point parametrized by signed radius `r` and angle `β`.

For standard polar coordinates one restricts to `r ≥ 0`; allowing every real `r` makes this a
total smooth parametrization on the parameter plane. -/
def planarPolarPoint (r β : ℝ) : ℝ^2 :=
  WithLp.toLp 2 ![r * Real.cos β, r * Real.sin β]

/-- The planar polar parametrization, with signed radius in coordinate zero and angle in
coordinate one. -/
def planarPolarMap (p : ℝ^2) : ℝ^2 :=
  planarPolarPoint (p 0) (p 1)

/-- First Cartesian coordinate of the polar point: `r cos β`. -/
@[simp]
theorem planarPolarPoint_zero (r β : ℝ) :
    planarPolarPoint r β 0 = r * Real.cos β := by
  simp [planarPolarPoint]

/-- Second Cartesian coordinate of the polar point: `r sin β`. -/
@[simp]
theorem planarPolarPoint_one (r β : ℝ) :
    planarPolarPoint r β 1 = r * Real.sin β := by
  simp [planarPolarPoint]

/-- First coordinate of `planarPolarMap p`, reading the signed radius from `p 0` and the angle
from `p 1`. -/
@[simp]
theorem planarPolarMap_zero (p : ℝ^2) :
    planarPolarMap p 0 = p 0 * Real.cos (p 1) := by
  simp [planarPolarMap]

/-- Second coordinate of `planarPolarMap p`, reading the signed radius from `p 0` and the angle
from `p 1`. -/
@[simp]
theorem planarPolarMap_one (p : ℝ^2) :
    planarPolarMap p 1 = p 0 * Real.sin (p 1) := by
  simp [planarPolarMap]

/-- The planar polar-coordinate map is smooth. -/
theorem contDiff_planarPolarMap :
    ContDiff ℝ (⊤ : ℕ∞) planarPolarMap := by
  apply contDiff_piLp' 2
  intro i
  fin_cases i
  · change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ^2 ↦ p 0 * Real.cos (p 1))
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ^2 ↦ p 0 * Real.sin (p 1))
    fun_prop

/-- The two-dimensional Laplacian written in polar variables `(r, β)`.

At a positive radius this is `uᵣᵣ + r⁻¹ uᵣ + r⁻² uββ`. Division on `ℝ` is
total, so the definition also has a value at `r = 0`, but that value has no coordinate
meaning. -/
def planarPolarLaplacian (u : ℝ → ℝ → ℝ) (r β : ℝ) : ℝ :=
  radialLaplacian 2 (fun s ↦ u s β) r +
    (1 / r ^ 2) * deriv (deriv (u r)) β

/-- Multiplying a polar profile by a radial cutoff produces the usual radial product terms. -/
theorem planarPolarLaplacian_radial_mul
    (χ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (r β : ℝ)
    (hχ : ContDiffAt ℝ 2 χ r)
    (hu : ContDiffAt ℝ 2 (fun s ↦ u s β) r) :
    planarPolarLaplacian (fun s θ ↦ χ s * u s θ) r β =
      χ r * planarPolarLaplacian u r β +
        u r β * radialLaplacian 2 χ r +
          2 * deriv χ r * deriv (fun s ↦ u s β) r := by
  rw [planarPolarLaplacian, planarPolarLaplacian]
  rw [radialLaplacian_mul 2 χ (fun s ↦ u s β) r hχ hu]
  simp only [deriv_const_mul_field']
  ring

/-- Polar Laplacian of the homogeneous mode `rᵐ f(β)` at a positive radius. -/
theorem planarPolarLaplacian_rpow_mul (f : ℝ → ℝ) (m r β : ℝ) (hr : 0 < r) :
    planarPolarLaplacian (fun s θ ↦ s ^ m * f θ) r β =
      r ^ (m - 2) * (m ^ 2 * f β + deriv (deriv f) β) := by
  have hradial :
      radialLaplacian 2 (fun s ↦ s ^ m * f β) r =
        r ^ (m - 2) * (m ^ 2 * f β) := by
    rw [show (fun s : ℝ ↦ s ^ m * f β) = fun s ↦ f β * s ^ m by
      funext s
      ring]
    rw [radialLaplacian_const_mul, radialLaplacian_rpow 2 r hr m]
    norm_num
    ring
  have hangular :
      deriv (deriv ((fun s θ ↦ s ^ m * f θ) r)) β =
        r ^ m * deriv (deriv f) β := by
    simp only [deriv_const_mul_field']
  have hshift : r ^ (m - 2) = r ^ m / r ^ 2 := by
    rw [Real.rpow_sub hr m 2, Real.rpow_two]
  rw [planarPolarLaplacian, hradial, hangular]
  rw [show (1 / r ^ 2) * (r ^ m * deriv (deriv f) β) =
      (r ^ m / r ^ 2) * deriv (deriv f) β by ring, ← hshift]
  ring

/-- Polar Laplacian of a radially cut off homogeneous angular mode. The final two terms are the
cutoff commutator. -/
theorem planarPolarLaplacian_cutoff_rpow_mul
    (χ f : ℝ → ℝ) (m r β : ℝ) (hr : 0 < r)
    (hχ : ContDiffAt ℝ 2 χ r) :
    planarPolarLaplacian (fun s θ ↦ χ s * (s ^ m * f θ)) r β =
      χ r * (r ^ (m - 2) * (m ^ 2 * f β + deriv (deriv f) β)) +
        r ^ m * f β * radialLaplacian 2 χ r +
          2 * m * r ^ (m - 1) * deriv χ r * f β := by
  have hpower : ContDiffAt ℝ 2 (fun s : ℝ ↦ s ^ m) r :=
    Real.contDiffAt_rpow_const_of_ne hr.ne'
  have hradial : ContDiffAt ℝ 2 (fun s : ℝ ↦ s ^ m * f β) r :=
    hpower.mul contDiffAt_const
  have hderiv :
      deriv (fun s : ℝ ↦ s ^ m * f β) r =
        m * r ^ (m - 1) * f β := by
    cas using hr
  rw [planarPolarLaplacian_radial_mul χ (fun s θ ↦ s ^ m * f θ) r β hχ
      hradial]
  rw [planarPolarLaplacian_rpow_mul f m r β hr, hderiv]
  ring

/-- The negative polar Laplacian of `r²⁺ᵃ f(β)` is the angular operator
`-∂β² - (2 + α)²`, multiplied by `rᵃ`. -/
theorem neg_planarPolarLaplacian_rpow_add_two_mul
    (f : ℝ → ℝ) (α r β : ℝ) (hr : 0 < r) :
    -planarPolarLaplacian (fun s θ ↦ s ^ (2 + α) * f θ) r β =
      r ^ α * (-deriv (deriv f) β - (2 + α) ^ 2 * f β) := by
  rw [planarPolarLaplacian_rpow_mul f (2 + α) r β hr]
  have hexponent : 2 + α - 2 = α := by ring
  rw [hexponent]
  ring

/-- An angular solution of `(-∂β² - (2 + α)²)f = g` produces the homogeneous
source `rᵃ g(β)` under the negative polar Laplacian. -/
theorem neg_planarPolarLaplacian_rpow_add_two_mul_eq
    (f g : ℝ → ℝ) (α r β : ℝ) (hr : 0 < r)
    (hangular : -deriv (deriv f) β - (2 + α) ^ 2 * f β = g β) :
    -planarPolarLaplacian (fun s θ ↦ s ^ (2 + α) * f θ) r β =
      r ^ α * g β := by
  rw [neg_planarPolarLaplacian_rpow_add_two_mul f α r β hr, hangular]

/-- If the angular mode solves `(-∂β² - m²)f = g`, then cutting it off produces the
desired homogeneous source plus an explicit radial commutator. -/
theorem neg_planarPolarLaplacian_cutoff_rpow_mul_eq
    (χ f g : ℝ → ℝ) (m r β : ℝ) (hr : 0 < r)
    (hχ : ContDiffAt ℝ 2 χ r)
    (hangular : -deriv (deriv f) β - m ^ 2 * f β = g β) :
    -planarPolarLaplacian (fun s θ ↦ χ s * (s ^ m * f θ)) r β =
      χ r * r ^ (m - 2) * g β -
        r ^ m * f β * radialLaplacian 2 χ r -
          2 * m * r ^ (m - 1) * deriv χ r * f β := by
  rw [planarPolarLaplacian_cutoff_rpow_mul χ f m r β hr hχ]
  rw [show m ^ 2 * f β + deriv (deriv f) β = -g β by linarith]
  ring

end PDE.CoordinateSystems

end
