/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators

/-!
# The Two-Dimensional Inviscid Boussinesq Model

A real-valued, two-dimensional inviscid Boussinesq model in the common
Eulerian form

```text
div u = 0,
u_t + (u · ∇)u + ∇p = θ e₂,
θ_t + (u · ∇)θ = 0.
```

`BoussinesqFields` records the physical unknowns, and `IsClassicalSolutionOn`
bundles joint `C¹` regularity with the three equations on a set of times. The
whole-space predicate carries no boundary condition.

The sign in this primitive-variable model is upward buoyancy.
`VorticityStream.PrimitiveBridge` shows that the clockwise-vorticity equation of Chen–Hou, with
source `partialDeriv 0 theta`, corresponds to coefficient `-1` in the primitive momentum equation
under LeanPDE's clockwise curl convention, using
`SatisfiesMomentumEquationWithBuoyancyCoefficientOn`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2, (2.3a)-(2.3c).
  <https://arxiv.org/abs/2210.07191v4>
-/

open scoped Gradient

@[expose] public section

open PDE (divergence advectiveDerivative)

namespace Boussinesq

/-- Unknowns for the two-dimensional Boussinesq system.

The velocity is vector-valued, while temperature and pressure are scalar fields depending on
space and time. -/
structure BoussinesqFields where
  /-- Fluid velocity as a function of space and time. -/
  velocity : ℝ^2 → ℝ → ℝ^2
  /-- Advected temperature as a function of space and time. -/
  temperature : ℝ^2 → ℝ → ℝ
  /-- Pressure as a function of space and time. -/
  pressure : ℝ^2 → ℝ → ℝ

/-- The zero Boussinesq fields. -/
def zeroFields : BoussinesqFields where
  velocity := fun _ _ ↦ 0
  temperature := fun _ _ ↦ 0
  pressure := fun _ _ ↦ 0

/-- Vertical buoyancy force `theta e₂` in the chosen coordinate convention. -/
def buoyancyForce (theta : ℝ) : ℝ^2 :=
  WithLp.toLp 2 fun i ↦ if i = 1 then theta else 0

/-- The first component of the vertical buoyancy force vanishes. -/
@[simp]
theorem buoyancyForce_apply_zero (theta : ℝ) :
    buoyancyForce theta 0 = 0 := by
  simp [buoyancyForce]

/-- The second component of the vertical buoyancy force is the temperature. -/
@[simp]
theorem buoyancyForce_apply_one (theta : ℝ) :
    buoyancyForce theta 1 = theta := by
  simp [buoyancyForce]

/-- Buoyancy depends linearly on temperature. -/
theorem buoyancyForce_smul (a theta : ℝ) :
    buoyancyForce (a * theta) = a • buoyancyForce theta := by
  ext i
  fin_cases i <;> simp [buoyancyForce]

/-- Buoyancy force with an explicit orientation coefficient. The choices
`κ = 1` and `κ = -1` give upward and downward buoyancy, respectively. -/
def buoyancyForceWithCoefficient (κ theta : ℝ) : ℝ^2 :=
  κ • buoyancyForce theta

/-- The horizontal component of a signed vertical buoyancy force vanishes. -/
@[simp]
theorem buoyancyForceWithCoefficient_apply_zero (κ theta : ℝ) :
    buoyancyForceWithCoefficient κ theta 0 = 0 := by
  simp [buoyancyForceWithCoefficient]

/-- The vertical component of a signed buoyancy force is `κ * theta`. -/
@[simp]
theorem buoyancyForceWithCoefficient_apply_one (κ theta : ℝ) :
    buoyancyForceWithCoefficient κ theta 1 = κ * theta := by
  simp [buoyancyForceWithCoefficient, smul_eq_mul]

/-- Exact pointwise momentum balance with an explicit buoyancy coefficient on
a spatial domain and a set of times.

For clockwise planar vorticity, this force contributes
`-κ * partialDeriv 0 theta` to the vorticity equation. -/
def SatisfiesMomentumEquationWithBuoyancyCoefficientOn
    (eq : BoussinesqFields) (κ : ℝ)
    (spatialDomain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ spatialDomain → t ∈ times →
    deriv (fun s ↦ eq.velocity x s) t +
        advectiveDerivative
          (fun y ↦ eq.velocity y t) (fun y ↦ eq.velocity y t) x +
        ∇ (fun y ↦ eq.pressure y t) x =
      buoyancyForceWithCoefficient κ (eq.temperature x t)

/-- The inviscid Boussinesq equations on a prescribed set of times, with classical regularity
side conditions.

The buoyancy force is `θ e₂`, encoded as the vector with second component `temperature` and first
component `0`.  The differentiability hypotheses are bundled because Lean's derivative operators
are total outside the classical regime; the joint spacetime `C¹` hypotheses keep the predicate
from being only a family of unrelated time and space slices. Spatial `C¹` regularity follows from
the joint hypotheses (`IsClassicalSolutionOn.velocity_spatial_contDiff` and its analogues). -/
structure IsClassicalSolutionOn (eq : BoussinesqFields) (times : Set ℝ) : Prop where
  /-- Joint spacetime `C¹` regularity of velocity on the prescribed times. -/
  velocity_contDiffOn :
    ContDiffOn ℝ 1 (fun xt : ℝ^2 × ℝ ↦ eq.velocity xt.1 xt.2) (Set.univ ×ˢ times)
  /-- Joint spacetime `C¹` regularity of temperature on the prescribed times. -/
  temperature_contDiffOn :
    ContDiffOn ℝ 1 (fun xt : ℝ^2 × ℝ ↦ eq.temperature xt.1 xt.2) (Set.univ ×ˢ times)
  /-- Joint spacetime `C¹` regularity of pressure on the prescribed times. -/
  pressure_contDiffOn :
    ContDiffOn ℝ 1 (fun xt : ℝ^2 × ℝ ↦ eq.pressure xt.1 xt.2) (Set.univ ×ˢ times)
  /-- Differentiability of every admitted velocity time slice. -/
  velocity_differentiableAt_time {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (fun s ↦ eq.velocity x s) t
  /-- Differentiability of every admitted temperature time slice. -/
  temperature_differentiableAt_time {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (fun s ↦ eq.temperature x s) t
  /-- Incompressibility on the prescribed time set. -/
  divergence_eq_zero {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    ∇· (fun y ↦ eq.velocity y t) x = 0
  /-- Momentum balance on the prescribed time set. -/
  momentum_eq {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    deriv (fun s ↦ eq.velocity x s) t +
      advectiveDerivative (fun y ↦ eq.velocity y t) (fun y ↦ eq.velocity y t) x +
      ∇ (fun y ↦ eq.pressure y t) x =
        buoyancyForce (eq.temperature x t)
  /-- Temperature transport on the prescribed time set. -/
  temperature_transport_eq {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    deriv (fun s ↦ eq.temperature x s) t +
      advectiveDerivative (fun y ↦ eq.velocity y t) (fun y ↦ eq.temperature y t) x = 0

/-- Every admitted velocity slice is globally `C¹` in space. -/
theorem IsClassicalSolutionOn.velocity_spatial_contDiff
    {eq : BoussinesqFields} {times : Set ℝ}
    (hsolution : IsClassicalSolutionOn eq times)
    {t : ℝ} (ht : t ∈ times) :
    ContDiff ℝ 1 (fun x ↦ eq.velocity x t) := by
  simpa only [Function.comp_def] using
    hsolution.velocity_contDiffOn.comp_contDiff
      (contDiff_prodMk_left t) (fun x ↦ ⟨Set.mem_univ x, ht⟩)

/-- Every admitted temperature slice is globally `C¹` in space. -/
theorem IsClassicalSolutionOn.temperature_spatial_contDiff
    {eq : BoussinesqFields} {times : Set ℝ}
    (hsolution : IsClassicalSolutionOn eq times)
    {t : ℝ} (ht : t ∈ times) :
    ContDiff ℝ 1 (fun x ↦ eq.temperature x t) := by
  simpa only [Function.comp_def] using
    hsolution.temperature_contDiffOn.comp_contDiff
      (contDiff_prodMk_left t) (fun x ↦ ⟨Set.mem_univ x, ht⟩)

/-- Every admitted pressure slice is globally `C¹` in space. -/
theorem IsClassicalSolutionOn.pressure_spatial_contDiff
    {eq : BoussinesqFields} {times : Set ℝ}
    (hsolution : IsClassicalSolutionOn eq times)
    {t : ℝ} (ht : t ∈ times) :
    ContDiff ℝ 1 (fun x ↦ eq.pressure x t) := by
  simpa only [Function.comp_def] using
    hsolution.pressure_contDiffOn.comp_contDiff
      (contDiff_prodMk_left t) (fun x ↦ ⟨Set.mem_univ x, ht⟩)

/-- The standard upward-buoyancy momentum equation is the coefficient-one
instance of the signed momentum equation. -/
theorem IsClassicalSolutionOn.satisfiesMomentumEquationWithCoefficient_one
    {eq : BoussinesqFields} {times : Set ℝ}
    (hsolution : IsClassicalSolutionOn eq times) :
    SatisfiesMomentumEquationWithBuoyancyCoefficientOn eq 1 Set.univ times := by
  intro x t hx ht
  simpa [buoyancyForceWithCoefficient] using hsolution.momentum_eq ht

/-- The zero fields solve the Boussinesq system on every prescribed time set. -/
theorem zeroFields_isClassicalSolutionOn (times : Set ℝ) :
    IsClassicalSolutionOn zeroFields times := by
  refine
    { velocity_contDiffOn := by fun_prop
      temperature_contDiffOn := by fun_prop
      pressure_contDiffOn := by fun_prop
      velocity_differentiableAt_time := by
        intro x t ht
        fun_prop
      temperature_differentiableAt_time := by
        intro x t ht
        fun_prop
      divergence_eq_zero := by
        intro x t ht
        simp [zeroFields, divergence, PDE.partialDeriv_const]
      momentum_eq := by
        intro x t ht
        ext i
        simp [zeroFields, advectiveDerivative, gradient, buoyancyForce]
      temperature_transport_eq := by
        intro x t ht
        simp [zeroFields, advectiveDerivative] }

end Boussinesq
