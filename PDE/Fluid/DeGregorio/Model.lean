/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair

/-!
# The generalized De Gregorio equation on the real line

The equation is `ω_t + a u ω_x = u_x ω`, with `u_x = Hω`. The family in `a` is that of Okamoto,
Sakajo and Wunsch; `a = 1` is De Gregorio's original model and `a = 0` the Constantin–Lax–Majda
model (Chen, Hou and Huang, Section 1.1, give this history). Fields take the spatial variable
before time.

`IsHilbertPair` uses the Fourier multiplier `−i sgn ξ` on complex `L²`, with value zero at `ξ = 0`.
Both real functions must represent the corresponding complex `L²` classes. This avoids
evaluating an arbitrary representative of an `L²` class at a point. The transport equation
is pointwise, and `HasClassicalRegularityOn` makes the fields differentiable, so the
`deriv` terms are true derivatives. `IsClassicalSolutionOn` requires both transport and Biot–Savart.

For a.e. differentiable real `L¹ ∩ L²` input `ω`, this transform agrees almost everywhere
with `(1/π) p.v. ∫ ω(x - t)/t dt`, as proved by
`hilbertPV_eq_hilbertTransform_ae_of_ae_differentiableAt` in
`PDE.Analysis.Fourier.HilbertTransform.SpectralL2`, which fixes the sign convention.

## References

* P. Constantin, P. D. Lax, and A. Majda, "A simple one-dimensional model for the three-dimensional
  vorticity equation", *Comm. Pure Appl. Math.* 38 (1985), no. 6, 715-724.
  <https://doi.org/10.1002/cpa.3160380605>
* S. De Gregorio, "On a one-dimensional model for the three-dimensional vorticity equation",
  *J. Stat. Phys.* 59 (1990), no. 5-6, 1251-1263.
  <https://doi.org/10.1007/BF01334750>
* H. Okamoto, T. Sakajo, and M. Wunsch, "On a generalization of the Constantin–Lax–Majda equation",
  *Nonlinearity* 21 (2008), no. 10, 2447-2461.
  <https://doi.org/10.1088/0951-7715/21/10/013>
* J. Chen, T. Y. Hou, and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), no. 6, 1282-1350; numbering of
  arXiv:1905.06387v3, Section 1.1, (1.3), p. 1.
  <https://doi.org/10.1002/cpa.21991>
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

namespace DeGregorio

open MeasureTheory
open PDE.Analysis

noncomputable section

/-- Real vorticity and velocity, with arguments ordered as space then time. -/
structure Fields where
  /-- Scalar vorticity. -/
  vorticity : ℝ → ℝ → ℝ
  /-- Scalar velocity. -/
  velocity : ℝ → ℝ → ℝ

/-- Differentiability required by the classical equation and its spacetime chain rule.
At time endpoints these are derivatives of the specified total extensions. -/
structure HasClassicalRegularityOn (fields : Fields) (times : Set ℝ) : Prop where
  /-- Joint differentiability of vorticity at every admitted spacetime point. -/
  vorticity_differentiableAt {x t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (Function.uncurry fields.vorticity) (x, t)
  /-- Spatial differentiability of velocity at every admitted spacetime point. -/
  velocity_differentiableAt {x t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (fun y ↦ fields.velocity y t) x

/-- Joint vorticity regularity supplies its spatial derivative. -/
theorem HasClassicalRegularityOn.vorticity_spatial_differentiableAt
    {fields : Fields} {times : Set ℝ}
    (h : HasClassicalRegularityOn fields times) {x t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (fun y ↦ fields.vorticity y t) x := by
  have hcomp := (h.vorticity_differentiableAt (x := x) ht).comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t).differentiableAt
  exact hcomp

/-- Joint vorticity regularity supplies its time derivative. -/
theorem HasClassicalRegularityOn.vorticity_time_differentiableAt
    {fields : Fields} {times : Set ℝ}
    (h : HasClassicalRegularityOn fields times) {x t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (fields.vorticity x) t := by
  have hcomp := (h.vorticity_differentiableAt (x := x) ht).comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t).differentiableAt
  exact hcomp

/-- The physical transport residual, with the stretching term subtracted. -/
def transportResidual (a : ℝ) (fields : Fields) (x t : ℝ) : ℝ :=
  deriv (fields.vorticity x) t +
    a * fields.velocity x t * deriv (fun y ↦ fields.vorticity y t) x -
      deriv (fun y ↦ fields.velocity y t) x * fields.vorticity x t

/-- The generalized vorticity transport equation. The Biot–Savart relation is the separate
predicate `SatisfiesBiotSavartOn`. -/
def SatisfiesTransportEquationOn (a : ℝ) (fields : Fields) (times : Set ℝ) : Prop :=
  ∀ ⦃x t : ℝ⦄, t ∈ times →
    deriv (fields.vorticity x) t +
        a * fields.velocity x t * deriv (fun y ↦ fields.vorticity y t) x =
      deriv (fun y ↦ fields.velocity y t) x * fields.vorticity x t

/-- The real velocity derivative represents `Hω`, with multiplier `−i sgn ξ`,
at each admitted time. -/
def SatisfiesBiotSavartOn (fields : Fields) (times : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ times →
    IsHilbertPair (fun x ↦ fields.vorticity x t) (deriv (fun x ↦ fields.velocity x t))

/-- A classical solution of the generalized De Gregorio equation in the real-line `L²`
formulation. Biot–Savart determines the velocity only up to a function of time; a
normalization such as `u(0, t) = 0` is a separate hypothesis. -/
structure IsClassicalSolutionOn (a : ℝ) (fields : Fields) (times : Set ℝ) : Prop where
  /-- The fields are differentiable where required. -/
  regularity : HasClassicalRegularityOn fields times
  /-- Vorticity evolves by transport and stretching. -/
  transport : SatisfiesTransportEquationOn a fields times
  /-- The velocity derivative is the Hilbert transform of vorticity. -/
  biotSavart : SatisfiesBiotSavartOn fields times

/-- Vanishing of the physical residual is precisely the transport equation. -/
theorem satisfiesTransportEquationOn_iff (a : ℝ) (fields : Fields) (times : Set ℝ) :
    SatisfiesTransportEquationOn a fields times ↔
      ∀ ⦃x t : ℝ⦄, t ∈ times → transportResidual a fields x t = 0 := by
  simp only [SatisfiesTransportEquationOn, transportResidual, sub_eq_zero]

end

end DeGregorio
