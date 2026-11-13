/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Euler
public import PDE.Fluid.Incompressible.Stress
public import PDE.Fluid.NavierStokes.Operators

/-!
# Incompressible flow model hierarchy

The Stokes and Navier–Stokes momentum residuals, and their relations to the Euler
residual and to the Newtonian Cauchy momentum residual.

Spacetime is `ℝ^(n + 1)`, coordinate `0` is time, and coordinate `i.succ`
is the `i`-th spatial coordinate. The residuals use the sign convention

```text
time derivative + convection + pressure - viscosity - force.
```

A residual equal to zero is equivalent to the corresponding momentum equation, and
the comparison theorems make precise which term is removed when passing between models.

The Euler and Navier–Stokes equations are those of Majda and Bertozzi, Chapter 1.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

open PDE (spatialGradient)

namespace IncompressibleFlow

open EuclideanSpace

set_option linter.missingDocs true

noncomputable section

/-- Stokes momentum residual `∂ₜu + ∇p - νΔu - f`. -/
def stokesMomentumResidual (n : ℕ) (ν : ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (f : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ^n :=
  timeDerivative n u x + spatialGradient p x -
    NavierStokes.viscousTerm n ν u x - f x

/-- Navier–Stokes momentum residual `Dₜu + ∇p - νΔu - f`. -/
def navierStokesMomentumResidual (n : ℕ) (ν : ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (f : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ^n :=
  materialDerivative n u u x + spatialGradient p x -
    NavierStokes.viscousTerm n ν u x - f x

private theorem sub_sub_eq_zero_iff_eq_add
    {G : Type*} [AddCommGroup G] (a b c d : G) :
    a + b - c - d = 0 ↔ a + b = c + d := by
  rw [sub_eq_zero, sub_eq_iff_eq_add, add_comm d c]

/-- A zero Stokes residual is exactly the pointwise Stokes momentum equation. -/
theorem stokesMomentumResidual_eq_zero_iff
    (n : ℕ) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    stokesMomentumResidual n ν u p f x = 0 ↔
      timeDerivative n u x + spatialGradient p x =
        NavierStokes.viscousTerm n ν u x + f x := by
  unfold stokesMomentumResidual
  exact sub_sub_eq_zero_iff_eq_add _ _ _ _

/-- A zero Navier–Stokes residual is exactly its pointwise momentum equation. -/
theorem navierStokesMomentumResidual_eq_zero_iff
    (n : ℕ) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    navierStokesMomentumResidual n ν u p f x = 0 ↔
      materialDerivative n u u x + spatialGradient p x =
          NavierStokes.viscousTerm n ν u x + f x := by
  unfold navierStokesMomentumResidual
  exact sub_sub_eq_zero_iff_eq_add _ _ _ _

/-- Navier–Stokes is the Euler residual with the viscous term subtracted. -/
theorem navierStokesMomentumResidual_eq_eulerMomentumResidual_sub_viscousTerm
    (n : ℕ) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    navierStokesMomentumResidual n ν u p f x =
      eulerMomentumResidual n u p f x -
        NavierStokes.viscousTerm n ν u x := by
  simp only [navierStokesMomentumResidual, eulerMomentumResidual]
  abel

/-- At zero viscosity, the Navier–Stokes residual is the Euler residual. -/
theorem navierStokesMomentumResidual_zero_viscosity
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    navierStokesMomentumResidual n 0 u p f x =
      eulerMomentumResidual n u p f x := by
  rw [navierStokesMomentumResidual_eq_eulerMomentumResidual_sub_viscousTerm]
  ext i
  simp [NavierStokes.viscousTerm]

/-- Navier–Stokes is the Stokes residual plus nonlinear convection. -/
theorem navierStokesMomentumResidual_eq_stokesMomentumResidual_add_convection
    (n : ℕ) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    navierStokesMomentumResidual n ν u p f x =
      stokesMomentumResidual n ν u p f x +
        convectiveDerivative n u u x := by
  rw [navierStokesMomentumResidual, stokesMomentumResidual,
    materialDerivative_eq_timeDerivative_add_convectiveDerivative]
  abel

/-- If convection vanishes at a point, the Navier–Stokes and Stokes residuals agree there. -/
theorem navierStokesMomentumResidual_eq_stokesMomentumResidual_of_convection_eq_zero
    (n : ℕ) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (hconv : convectiveDerivative n u u x = 0) :
    navierStokesMomentumResidual n ν u p f x =
      stokesMomentumResidual n ν u p f x := by
  rw [navierStokesMomentumResidual_eq_stokesMomentumResidual_add_convection,
    hconv, add_zero]

/-- For a Newtonian fluid of unit density that is divergence-free near the
evaluation point, the Cauchy momentum residual is exactly the Navier–Stokes
momentum residual. -/
theorem newtonianCauchyMomentumResidual_eq_navierStokesMomentumResidual_of_eventually
    (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hp : DifferentiableAt ℝ p x)
    (hu : ∀ k : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y k) x)
    (hdiv : ∀ᶠ y in nhds x, IncompressibleFlow.DivergenceFreeAt u y) :
    newtonianCauchyMomentumResidual n dynamicViscosity p u f x =
      navierStokesMomentumResidual n dynamicViscosity u p f x := by
  rw [newtonianCauchyMomentumResidual,
    newtonianCauchyStressDivergence_eq_of_eventually_divergenceFreeAt
      n dynamicViscosity p u x hp hu hdiv,
    navierStokesMomentumResidual, NavierStokes.viscousTerm]
  abel

/-- For a globally divergence-free Newtonian fluid of unit density, the
Cauchy momentum residual is exactly the Navier–Stokes momentum residual. -/
theorem newtonianCauchyMomentumResidual_eq_navierStokesMomentumResidual
    (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hp : DifferentiableAt ℝ p x)
    (hu : ∀ k : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y k) x)
    (hdiv : IncompressibleFlow.DivergenceFree u) :
    newtonianCauchyMomentumResidual n dynamicViscosity p u f x =
      navierStokesMomentumResidual n dynamicViscosity u p f x := by
  apply
    newtonianCauchyMomentumResidual_eq_navierStokesMomentumResidual_of_eventually
      n dynamicViscosity p u f x hp hu
  exact Filter.Eventually.of_forall fun y ↦ hdiv.at y

end

end IncompressibleFlow
