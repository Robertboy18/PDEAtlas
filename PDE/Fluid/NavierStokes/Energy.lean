/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Restriction
public import PDE.Analysis.Integration.InnerProductByParts
public import PDE.Analysis.Variational.ValidatedNonlinear
public import PDE.Elliptic.Variational.LowerOrderForm
public import PDE.Fluid.Incompressible.Convection
public import PDE.Fluid.Incompressible.EnergyIdentities
public import PDE.Fluid.Incompressible.Solenoidal
public import PDE.Fluid.NavierStokes.Problem
public import PDE.Spaces.Sobolev.Calculus.Divergence.ZeroBoundary

/-!
# Energy and dissipation for Navier-Stokes velocity fields

Kinetic energy, enstrophy, and the classical and weak spatial-gradient dissipation quantities
used by the Navier-Stokes solution interfaces, each with its pointwise density. The density
definitions make the integrability obligations visible independently of Lean's totalized
integral.

Fefferman's bounded-energy condition (7) asks for a bound on `∫ |u(x,t)|² dx` uniform in `t ≥ 0`;
`kineticEnergy` is half of this integral.

## References

* C. L. Fefferman, "Existence and smoothness of the Navier–Stokes equation", official problem
  description of the Clay Mathematics Institute, condition (7), p. 1.
  <https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf>
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory Order
open scoped InnerProductSpace

set_option linter.missingDocs true

/-- Kinetic-energy density `|u(t,x)|^2 / 2`. -/
noncomputable def kineticEnergyDensity {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  IncompressibleFlow.specificKineticEnergy u
    (PDE.Common.timeSpaceCons t x)

/-- Coordinate formula for kinetic-energy density. -/
theorem kineticEnergyDensity_eq_sum {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) :
    kineticEnergyDensity u t x =
      (1 / 2 : ℝ) *
        ∑ i : Fin n, (u (PDE.Common.timeSpaceCons t x) i) ^ 2 :=
  IncompressibleFlow.specificKineticEnergy_eq_sum_sq u
    (PDE.Common.timeSpaceCons t x)

/-- Formal kinetic energy `1 / 2 ∫ |u(t,x)|² dx`.

For weak or Leray-Hopf solutions this should be used together with the integrability hypotheses
in the corresponding structure. -/
noncomputable def kineticEnergy {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) : ℝ :=
  ∫ x : ℝ^n, kineticEnergyDensity u t x

/-- An `L²` velocity slice has integrable kinetic-energy density. -/
theorem integrable_kineticEnergyDensity_of_memLp {n : ℕ}
    {u : ℝ^(n + 1) → ℝ^n} {t : ℝ}
    (hu : MemLp (IncompressibleFlow.velocitySlice u t) 2
      (MeasureTheory.volume : Measure (ℝ^n))) :
    Integrable (kineticEnergyDensity u t) := by
  change Integrable (fun x : ℝ^n ↦
    (1 / 2 : ℝ) * ‖IncompressibleFlow.velocitySlice u t x‖ ^ 2)
  have hnorm := hu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  exact hnorm.const_mul (1 / 2)

/-- Kinetic-energy density of the prescribed initial velocity. -/
noncomputable def initialKineticEnergyDensity {n : ℕ}
    (nse : Problem n) (x : ℝ^n) : ℝ :=
  IncompressibleFlow.specificKineticEnergy nse.initialVelocity x

/-- Coordinate formula for the kinetic-energy density of the initial velocity. -/
theorem initialKineticEnergyDensity_eq_sum {n : ℕ}
    (nse : Problem n) (x : ℝ^n) :
    initialKineticEnergyDensity nse x =
      (1 / 2 : ℝ) * ∑ i : Fin n, (nse.initialVelocity x i) ^ 2 := by
  simpa [initialKineticEnergyDensity] using
    IncompressibleFlow.specificKineticEnergy_eq_sum_sq
      nse.initialVelocity x

/-- Kinetic energy of the prescribed initial velocity. This is the datum-side quantity used in the
Leray-Hopf energy inequality, rather than the value of an arbitrary spacetime representative at the
single time `t = 0`. -/
noncomputable def initialKineticEnergy {n : ℕ} (nse : Problem n) : ℝ :=
  ∫ x : ℝ^n, initialKineticEnergyDensity nse x

/-- An `L²` initial velocity has integrable initial kinetic-energy density. -/
theorem integrable_initialKineticEnergyDensity_of_memLp {n : ℕ} {nse : Problem n}
    (hu₀ : MemLp nse.initialVelocity 2
      (MeasureTheory.volume : Measure (ℝ^n))) :
    Integrable (initialKineticEnergyDensity nse) := by
  change Integrable (fun x : ℝ^n ↦
    (1 / 2 : ℝ) * ‖nse.initialVelocity x‖ ^ 2)
  have hnorm := hu₀.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  exact hnorm.const_mul (1 / 2)

/-- Power density supplied by the external force to a velocity field. -/
noncomputable def forcePowerDensity {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  inner ℝ
    (nse.forcing (PDE.Common.timeSpaceCons t x))
    (IncompressibleFlow.velocitySlice u t x)

/-- Coordinate formula for the external-force power density. -/
theorem forcePowerDensity_eq_sum {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) :
    forcePowerDensity nse u t x =
      ∑ i : Fin n, nse.forcing (PDE.Common.timeSpaceCons t x) i *
        u (PDE.Common.timeSpaceCons t x) i := by
  simp [forcePowerDensity, IncompressibleFlow.velocitySlice,
    PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Two `L²` spatial slices have integrable external-force power density. -/
theorem integrable_forcePowerDensity_of_memLp {n : ℕ}
    {nse : Problem n} {u : ℝ^(n + 1) → ℝ^n} {t : ℝ}
    (hforce : MemLp
      (fun x : ℝ^n ↦ nse.forcing (PDE.Common.timeSpaceCons t x)) 2
      (MeasureTheory.volume : Measure (ℝ^n)))
    (hvelocity : MemLp (IncompressibleFlow.velocitySlice u t) 2
      (MeasureTheory.volume : Measure (ℝ^n))) :
    Integrable (forcePowerDensity nse u t) := by
  let forceL2 : MeasureTheory.Lp (ℝ^n) 2
      (MeasureTheory.volume : Measure (ℝ^n)) :=
    hforce.toLp
      (fun x : ℝ^n ↦ nse.forcing (PDE.Common.timeSpaceCons t x))
  let velocityL2 : MeasureTheory.Lp (ℝ^n) 2
      (MeasureTheory.volume : Measure (ℝ^n)) :=
    hvelocity.toLp (IncompressibleFlow.velocitySlice u t)
  have hinner :=
    MeasureTheory.L2.integrable_inner (𝕜 := ℝ) forceL2 velocityL2
  apply hinner.congr
  filter_upwards [hforce.coeFn_toLp, hvelocity.coeFn_toLp] with x hfx hux
  rw [show forceL2 x =
      nse.forcing (PDE.Common.timeSpaceCons t x) by exact hfx]
  rw [show velocityL2 x =
      IncompressibleFlow.velocitySlice u t x by exact hux]
  rfl

/-- Enstrophy density `|Ω(u)|² / 2`. In three dimensions this equals
`|curl u|²`. -/
noncomputable def enstrophyDensity {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  (1 / 2 : ℝ) *
    ‖IncompressibleFlow.vorticityTensor n u
      (PDE.Common.timeSpaceCons t x)‖ ^ 2

/-- Coordinate formula for enstrophy density. -/
theorem enstrophyDensity_eq_sum {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) :
    enstrophyDensity u t x =
      (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
        IncompressibleFlow.vorticityTensor n u
          (PDE.Common.timeSpaceCons t x) (i, j) ^ 2 := by
  simp [enstrophyDensity, EuclideanSpace.real_norm_sq_eq,
    Fintype.sum_prod_type]

/-- Enstrophy: the integral of half the squared Frobenius norm of the vorticity tensor.
In `ℝ^3` this is the integral of `|curl u|²`.
The factor `1/2` compensates for counting both antisymmetric matrix entries. -/
noncomputable def enstrophy {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) : ℝ :=
  ∫ x : ℝ^n, enstrophyDensity u t x

/-- Classical squared-gradient density `|∇u(t,x)|²`, computed with
totalized Fréchet derivatives. -/
noncomputable def classicalVelocityGradientDissipationDensity {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  ‖IncompressibleFlow.classicalVelocityGradientSlice u t x‖ ^ 2

/-- Coordinate formula for classical squared-gradient density. -/
theorem classicalVelocityGradientDissipationDensity_eq_sum {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) :
    classicalVelocityGradientDissipationDensity u t x =
      ∑ i : Fin n, ∑ j : Fin n,
        (∂[j.succ] (fun y ↦ u y i))
          (PDE.Common.timeSpaceCons t x) ^ 2 := by
  simp [classicalVelocityGradientDissipationDensity,
    IncompressibleFlow.classicalVelocityGradientSlice,
    EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]

/-- Classical viscous dissipation `∫ |∇u(t)|²`, computed with totalized
Fréchet derivatives.

This operator belongs to the smooth pointwise layer. Weak solutions instead carry an explicit
distributional gradient witness and use `weakGradientDissipation`. -/
noncomputable def classicalVelocityGradientDissipation {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) : ℝ :=
  ∫ x : ℝ^n, classicalVelocityGradientDissipationDensity u t x

/-- Squared-gradient density `|Du(t,x)|²` for an explicit weak-gradient witness. -/
noncomputable def weakGradientDissipationDensity {n : ℕ}
    (Du : IncompressibleFlow.SpatialGradientField n) (t : ℝ) (x : ℝ^n) : ℝ :=
  ‖IncompressibleFlow.spatialGradientSlice Du t x‖ ^ 2

/-- Coordinate formula for weak squared-gradient density. -/
theorem weakGradientDissipationDensity_eq_sum {n : ℕ}
    (Du : IncompressibleFlow.SpatialGradientField n) (t : ℝ) (x : ℝ^n) :
    weakGradientDissipationDensity Du t x =
      ∑ i : Fin n, ∑ j : Fin n,
        Du (PDE.Common.timeSpaceCons t x) (i, j) ^ 2 := by
  simp [weakGradientDissipationDensity,
    IncompressibleFlow.spatialGradientSlice,
    EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]

/-- Leray-Hopf viscous dissipation `∫ |Du(t)|²` for an explicit weak-gradient witness. -/
noncomputable def weakGradientDissipation {n : ℕ}
    (Du : IncompressibleFlow.SpatialGradientField n) (t : ℝ) : ℝ :=
  ∫ x : ℝ^n, weakGradientDissipationDensity Du t x

/-- An `L²` weak-gradient slice has an integrable squared-gradient density. -/
theorem integrable_weakGradientDissipationDensity_of_memLp {n : ℕ}
    {Du : IncompressibleFlow.SpatialGradientField n} {t : ℝ}
    (hDu : MemLp (IncompressibleFlow.spatialGradientSlice Du t) 2
      (MeasureTheory.volume : Measure (ℝ^n))) :
    Integrable (weakGradientDissipationDensity Du t) := by
  exact hDu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

end NavierStokes
