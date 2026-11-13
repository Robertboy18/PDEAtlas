/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.WeakForm
public import PDE.Fluid.NavierStokes.Energy

/-!
# Weak Navier-Stokes solutions

There are two finite-time weak-solution interfaces on a closed time slab.

* `WeakSolution` is pressure-free: its momentum equation is tested only against
  solenoidal fields.
* `PressureWeakSolution` retains a pressure representative and tests against general
  vector fields. It projects to `WeakSolution` because its pressure term vanishes on
  solenoidal tests.

Neither interface asks totalized pointwise derivatives of velocity to satisfy the PDE.
Both store a distributional spatial-gradient witness and integrability hypotheses.

`PressureWeakSolution` is the weak formulation (12)-(13) of Fefferman's problem description on a
finite slab `[0,T] × ℝ^n`, with the signs of (12) as corrected in the errata there. Fefferman's
tests are compactly supported in `ℝ³ × (0,∞)`. Ours are compactly supported in spacetime and
vanish at `t = T` but not necessarily at `t = 0`, so the identity carries the initial pairing. The
viscous term is integrated by parts once, against the weak gradient `Du`, instead of twice.
Incompressibility (13) is imposed on each time slice.

`LerayHopfSolution` is a stricter layer defined separately: it adds Bochner energy
spaces, weak time continuity, an initial trace, and the energy inequality.

## References

* C. L. Fefferman, "Existence and smoothness of the Navier–Stokes equation", official problem
  description of the Clay Mathematics Institute, equations (12) and (13), p. 3, and the errata.
  <https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf>
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory Order

set_option linter.missingDocs true

/-- A weak momentum test whose spatial divergence vanishes pointwise.

The first field gives the common smoothness, compact-support, and terminal-time conditions.
The second field is the solenoidal condition that removes pressure from the weak equation. -/
def IsSolenoidalWeakMomentumTest {n : ℕ} (T : ℝ)
    (φ : ℝ^(n + 1) → ℝ^n) : Prop :=
  IncompressibleFlow.IsWeakMomentumTest T φ ∧
    ∀ t : ℝ, ∀ x : ℝ^n,
      IncompressibleFlow.DivergenceFreeAt φ
        (PDE.Common.timeSpaceCons t x)

/-- A solenoidal weak momentum test is an admissible general weak momentum test. -/
theorem IsSolenoidalWeakMomentumTest.isWeakMomentumTest {n : ℕ} {T : ℝ}
    {φ : ℝ^(n + 1) → ℝ^n} (hφ : IsSolenoidalWeakMomentumTest T φ) :
    IncompressibleFlow.IsWeakMomentumTest T φ :=
  hφ.1

/-- A solenoidal weak momentum test is divergence-free at every spacetime point on a slice. -/
theorem IsSolenoidalWeakMomentumTest.divergenceFreeAt {n : ℕ} {T : ℝ}
    {φ : ℝ^(n + 1) → ℝ^n} (hφ : IsSolenoidalWeakMomentumTest T φ)
    (t : ℝ) (x : ℝ^n) :
    IncompressibleFlow.DivergenceFreeAt φ
      (PDE.Common.timeSpaceCons t x) :=
  hφ.2 t x

/-- The spatial divergence of a solenoidal weak momentum test vanishes pointwise. -/
theorem IsSolenoidalWeakMomentumTest.spatialDivergence_eq_zero
    {n : ℕ} {T : ℝ}
    {φ : ℝ^(n + 1) → ℝ^n} (hφ : IsSolenoidalWeakMomentumTest T φ)
    (t : ℝ) (x : ℝ^n) :
    IncompressibleFlow.spatialDivergence n φ
      (PDE.Common.timeSpaceCons t x) = 0 :=
  hφ.divergenceFreeAt t x

/-- The scalar spacetime integrand in the pressure-retaining weak momentum equation.

`Du (t,x) (i,j)` is the distributional derivative `∂ⱼuᵢ`; no classical derivative of `u` occurs
in this expression. -/
noncomputable def weakMomentumIntegrand {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ) (Du : IncompressibleFlow.SpatialGradientField n)
    (φ : ℝ^(n + 1) → ℝ^n)
    (t : ℝ) (x : ℝ^n) : ℝ :=
  IncompressibleFlow.inviscidWeakMomentumIntegrand nse.forcing u p φ t x
  + nse.kinematicViscosity * inner ℝ
      (Du (PDE.Common.timeSpaceCons t x))
      (IncompressibleFlow.spatialVelocityGradient n φ
        (PDE.Common.timeSpaceCons t x))

/-- Coordinate formula for the weak Navier–Stokes momentum integrand. -/
theorem weakMomentumIntegrand_eq_sum {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (Du : IncompressibleFlow.SpatialGradientField n)
    (φ : ℝ^(n + 1) → ℝ^n)
    (t : ℝ) (x : ℝ^n) :
    weakMomentumIntegrand nse u p Du φ t x =
      -(∑ i : Fin n, u (PDE.Common.timeSpaceCons t x) i *
        (∂[0] (fun y ↦ φ y i)) (PDE.Common.timeSpaceCons t x))
      -(∑ i : Fin n, ∑ j : Fin n,
        u (PDE.Common.timeSpaceCons t x) i *
          u (PDE.Common.timeSpaceCons t x) j *
          (∂[j.succ] (fun y ↦ φ y i))
            (PDE.Common.timeSpaceCons t x))
      + nse.kinematicViscosity * (∑ i : Fin n, ∑ j : Fin n,
        Du (PDE.Common.timeSpaceCons t x) (i, j) *
          (∂[j.succ] (fun y ↦ φ y i))
            (PDE.Common.timeSpaceCons t x))
      -(∑ i : Fin n, p (PDE.Common.timeSpaceCons t x) *
        (∂[i.succ] (fun y ↦ φ y i))
          (PDE.Common.timeSpaceCons t x))
      -(∑ i : Fin n, nse.forcing (PDE.Common.timeSpaceCons t x) i *
        φ (PDE.Common.timeSpaceCons t x) i) := by
  rw [weakMomentumIntegrand, IncompressibleFlow.inviscidWeakMomentumIntegrand_eq_sum]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type,
    IncompressibleFlow.spatialVelocityGradient]
  simp [mul_comm]
  ring

/-- Spatial integral of the weak momentum integrand at one time. -/
noncomputable def weakMomentumSlice {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ) (Du : IncompressibleFlow.SpatialGradientField n)
    (φ : ℝ^(n + 1) → ℝ^n)
    (t : ℝ) : ℝ :=
  ∫ x : ℝ^n, weakMomentumIntegrand nse u p Du φ t x

/-- The integrability obligations behind the iterated weak momentum integral.

Lean's Bochner integral is totalized, so an identity between bare integral expressions would not by
itself assert that the displayed pairings are analytic integrals. This predicate records spatial
integrability at every physical time and outer time integrability. The initial boundary pairing is
integrable automatically from the stored `L²` initial datum and compact support of the test
field. -/
def WeakMomentumIntegrableOn {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ) (Du : IncompressibleFlow.SpatialGradientField n)
    (T : ℝ)
  (φ : ℝ^(n + 1) → ℝ^n) : Prop :=
  (∀ t ∈ Set.Icc 0 T,
    Integrable (fun x : ℝ^n ↦
      weakMomentumIntegrand nse u p Du φ t x)) ∧
  IntegrableOn (weakMomentumSlice nse u p Du φ) (Set.Icc 0 T)

/-- The pressure-free weak momentum integrand used with solenoidal test fields. -/
noncomputable def solenoidalWeakMomentumIntegrand {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (Du : IncompressibleFlow.SpatialGradientField n)
    (φ : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  weakMomentumIntegrand nse u (fun _ ↦ 0) Du φ t x

/-- Spatial integral of the pressure-free weak momentum integrand at one time. -/
noncomputable def solenoidalWeakMomentumSlice {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (Du : IncompressibleFlow.SpatialGradientField n)
    (φ : ℝ^(n + 1) → ℝ^n) (t : ℝ) : ℝ :=
  ∫ x : ℝ^n, solenoidalWeakMomentumIntegrand nse u Du φ t x

/-- Integrability obligations for the pressure-free weak momentum equation.

As in the pressure-retaining formulation, initial-boundary integrability follows from the stored
`L²` datum and is exposed as a derived theorem on `WeakSolution`. -/
def SolenoidalWeakMomentumIntegrableOn {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (Du : IncompressibleFlow.SpatialGradientField n)
    (T : ℝ) (φ : ℝ^(n + 1) → ℝ^n) : Prop :=
  (∀ t ∈ Set.Icc 0 T,
    Integrable (fun x : ℝ^n ↦ solenoidalWeakMomentumIntegrand nse u Du φ t x)) ∧
  IntegrableOn (solenoidalWeakMomentumSlice nse u Du φ) (Set.Icc 0 T)

/-- Pressure-free weak Navier-Stokes solution on the closed slab `[0,T]`.

The momentum equation is imposed only against smooth compactly supported solenoidal tests, so
pressure does not occur. The raw fields
retain representatives because the weak-derivative and nonlinear-pairing definitions are
representative based. In particular, the per-time `L²` hypotheses are stronger than a formulation
stated solely as equivalence classes almost everywhere in time. -/
structure WeakSolution {n : ℕ} (nse : Problem n) where
  /-- Velocity representative. -/
  u : ℝ^(n + 1) → ℝ^n

  /-- Distributional spatial-gradient representative, with component `(i,j) = ∂ⱼuᵢ`. -/
  Du : IncompressibleFlow.SpatialGradientField n

  /-- Positive finite endpoint of the time slab. -/
  T : Set.Ioi (0 : ℝ)

  /-- The prescribed initial velocity belongs to `L²(ℝ^n)`. -/
  initialVelocity_memLp :
    MemLp nse.initialVelocity 2 (MeasureTheory.volume : Measure (ℝ^n))

  /-- Velocity has an `L²` representative at each time of the closed slab. -/
  velocity_memLp_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    MemLp (IncompressibleFlow.velocitySlice u t) 2
      (MeasureTheory.volume : Measure (ℝ^n))

  /-- The weak gradient has an `L²` representative at each positive physical time.
  No spatial derivative is required of the initial `L²` datum. -/
  gradient_memLp_at : ∀ {t : ℝ}, t ∈ Set.Ioc 0 (T : ℝ) →
    MemLp (IncompressibleFlow.spatialGradientSlice Du t) 2
      (MeasureTheory.volume : Measure (ℝ^n))

  /-- `Du` is the distributional spatial derivative of `u` on every positive time slice. -/
  hasWeakSpatialDerivative : ∀ {t : ℝ}, t ∈ Set.Ioc 0 (T : ℝ) → ∀ i j : Fin n,
    SobolevSpace.HasWeakDerivativeOn (n := n) Set.univ [j]
      (fun x ↦ u (PDE.Common.timeSpaceCons t x) i)
      (fun x ↦ Du (PDE.Common.timeSpaceCons t x) (i, j))

  /-- The external force has an `L²` spatial slice at each physical time. -/
  force_memLp_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    MemLp (fun x : ℝ^n ↦ nse.forcing (PDE.Common.timeSpaceCons t x)) 2
      (MeasureTheory.volume : Measure (ℝ^n))

  /-- Every solenoidal momentum test gives integrable, non-totalized integrals. -/
  weak_momentum_integrable_on :
    ∀ φ : ℝ^(n + 1) → ℝ^n,
      IsSolenoidalWeakMomentumTest T φ →
      SolenoidalWeakMomentumIntegrableOn nse u Du T φ

  /-- The pressure-free weak momentum equation against solenoidal tests. -/
  weak_momentum_eq :
    ∀ φ : ℝ^(n + 1) → ℝ^n,
      IsSolenoidalWeakMomentumTest T φ →
      (∫ t in Set.Icc 0 (T : ℝ), solenoidalWeakMomentumSlice nse u Du φ t) =
        IncompressibleFlow.initialVelocityTestPairing nse.toInitialValueData
          (fun x ↦ φ (PDE.Common.timeSpaceCons 0 x))

  /-- Every velocity slice is incompressible in the distributional sense. -/
  distributionallyDivergenceFree_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    IncompressibleFlow.DistributionallyDivergenceFree
      (IncompressibleFlow.velocitySlice u t)

/-- Pressure-retaining weak solution to the Navier-Stokes equations on `[0,T]`.

This is a distributional solution notion in its own right, not a regularity
extension of `PointwiseResidualSolution`. The velocity carries a
distributional spatial-gradient witness. The momentum identity uses test fields
that may be nonzero at the initial time and therefore contains the prescribed
initial datum as a boundary term. This avoids identifying initial data through
an arbitrary value assigned to a representative at the measure-zero slice
`t = 0`.

This is a pressure-retaining, strong-data interface: pressure and forcing have `L²` spatial slices
at every time, while `weak_momentum_integrable_on` separately gives integrability of the summed
iterated integrand. -/
structure PressureWeakSolution {n : ℕ} (nse : Problem n) where
  /-- Velocity field unknown. -/
  u : ℝ^(n + 1) → ℝ^n

  /-- Pressure field unknown. -/
  p : ℝ^(n + 1) → ℝ

  /-- Distributional spatial-gradient representative, with component `(i,j) = ∂ⱼuᵢ`. -/
  Du : IncompressibleFlow.SpatialGradientField n

  /-- Positive time horizon for the weak solution on `[0,T]`. -/
  T : Set.Ioi (0 : ℝ)

  /-- The prescribed initial velocity belongs to `L²(ℝ^n)`. -/
  initialVelocity_memLp :
    MemLp nse.initialVelocity 2
      (MeasureTheory.volume : Measure (ℝ^n))

  /-- Velocity has an `L²` representative at each time of the closed slab. -/
  velocity_memLp_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    MemLp (IncompressibleFlow.velocitySlice u t) 2
      (MeasureTheory.volume : Measure (ℝ^n))

  /-- The weak gradient has an `L²` representative at each positive physical time.
  No spatial derivative is required of the initial `L²` datum. -/
  gradient_memLp_at : ∀ {t : ℝ}, t ∈ Set.Ioc 0 (T : ℝ) →
    MemLp (IncompressibleFlow.spatialGradientSlice Du t) 2
      (MeasureTheory.volume : Measure (ℝ^n))

  /-- `Du` is the distributional spatial derivative of `u` on every positive time slice. -/
  hasWeakSpatialDerivative : ∀ {t : ℝ}, t ∈ Set.Ioc 0 (T : ℝ) → ∀ i j : Fin n,
    SobolevSpace.HasWeakDerivativeOn (n := n) Set.univ [j]
      (fun x ↦ u (PDE.Common.timeSpaceCons t x) i)
      (fun x ↦ Du (PDE.Common.timeSpaceCons t x) (i, j))

  /-- Pressure has an `L²` slice at each time in `[0,T]`.

  The weak momentum identity `weak_momentum_eq` includes the pressure term `p div φ`; this
  field records the analytic integrability side condition for that pairing. -/
  pressure_memLp_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    MemLp (fun x : ℝ^n ↦ p (PDE.Common.timeSpaceCons t x)) 2
      (MeasureTheory.volume : Measure (ℝ^n))

  /-- The external force has an `L²` slice at each time in `[0,T]`.

  This is the side condition used to read the forcing term in the weak momentum identity as a
  space integral, rather than just a totalized Lean expression. -/
  force_memLp_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    MemLp (fun x : ℝ^n ↦ nse.forcing (PDE.Common.timeSpaceCons t x)) 2
      (MeasureTheory.volume : Measure (ℝ^n))

  /-- Every admissible momentum test gives integrable, non-totalized integrals. -/
  weak_momentum_integrable_on :
    ∀ φ : ℝ^(n + 1) → ℝ^n,
      IncompressibleFlow.IsWeakMomentumTest T φ →
      WeakMomentumIntegrableOn nse u p Du T φ

  /-- Solution satisfies the momentum equation in weak sense.

  Pressure is retained, so the test field is a general compactly supported vector field. The
  separate `distributionallyDivergenceFree_at` field records distributional
  incompressibility.
  With the sign convention
  `u_t + div(u ⊗ u) + ∇p - ν Δu - f = 0`, integrating by parts against
  terminal-time-vanishing test fields gives the displayed integrand:
  `-u · φ_t - (u ⊗ u) : ∇φ - p div φ + ν Du : ∇φ - f · φ`.

  The initial boundary term appears on the right-hand side. Consequently, the equation cannot be
  satisfied by deleting nonzero initial data immediately after `t = 0`.
  -/
  weak_momentum_eq :
    ∀ φ : ℝ^(n + 1) → ℝ^n,
      IncompressibleFlow.IsWeakMomentumTest T φ →
      (∫ t in Set.Icc 0 (T : ℝ), weakMomentumSlice nse u p Du φ t) =
        IncompressibleFlow.initialVelocityTestPairing nse.toInitialValueData
          (fun x ↦ φ (PDE.Common.timeSpaceCons 0 x))

  /-- Every velocity slice is incompressible in the distributional sense. -/
  distributionallyDivergenceFree_at :
    ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
      IncompressibleFlow.DistributionallyDivergenceFree
        (IncompressibleFlow.velocitySlice u t)

/-- On a solenoidal test, the pressure-retaining integrand equals the pressure-free integrand. -/
theorem weakMomentumIntegrand_eq_solenoidalWeakMomentumIntegrand {n : ℕ}
    (nse : Problem n) (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (Du : IncompressibleFlow.SpatialGradientField n) (φ : ℝ^(n + 1) → ℝ^n)
    {T t : ℝ} (hφ : IsSolenoidalWeakMomentumTest T φ) (x : ℝ^n) :
    weakMomentumIntegrand nse u p Du φ t x =
      solenoidalWeakMomentumIntegrand nse u Du φ t x := by
  simp only [solenoidalWeakMomentumIntegrand, weakMomentumIntegrand,
    IncompressibleFlow.inviscidWeakMomentumIntegrand]
  rw [hφ.spatialDivergence_eq_zero t x]
  simp

/-- On a solenoidal test, the pressure-retaining and pressure-free spatial slices agree. -/
theorem weakMomentumSlice_eq_solenoidalWeakMomentumSlice {n : ℕ}
    (nse : Problem n) (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (Du : IncompressibleFlow.SpatialGradientField n) (φ : ℝ^(n + 1) → ℝ^n)
    {T : ℝ} (hφ : IsSolenoidalWeakMomentumTest T φ) (t : ℝ) :
    weakMomentumSlice nse u p Du φ t = solenoidalWeakMomentumSlice nse u Du φ t := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    weakMomentumIntegrand_eq_solenoidalWeakMomentumIntegrand nse u p Du φ hφ x

/-- Forgetting pressure turns a pressure-retaining weak solution into a pressure-free one. -/
def PressureWeakSolution.toWeakSolution {n : ℕ} {nse : Problem n}
    (sol : PressureWeakSolution nse) : WeakSolution nse where
  u := sol.u
  Du := sol.Du
  T := sol.T
  initialVelocity_memLp := sol.initialVelocity_memLp
  velocity_memLp_at := sol.velocity_memLp_at
  gradient_memLp_at := sol.gradient_memLp_at
  hasWeakSpatialDerivative := sol.hasWeakSpatialDerivative
  force_memLp_at := sol.force_memLp_at
  weak_momentum_integrable_on := by
    intro φ hφ
    obtain ⟨hspace, htime⟩ :=
      sol.weak_momentum_integrable_on φ hφ.isWeakMomentumTest
    refine ⟨?_, ?_⟩
    · intro t ht
      exact (hspace t ht).congr <| Filter.Eventually.of_forall fun x ↦
        (weakMomentumIntegrand_eq_solenoidalWeakMomentumIntegrand
          nse sol.u sol.p sol.Du φ hφ x)
    · apply htime.congr
      exact Filter.Eventually.of_forall fun t ↦
        weakMomentumSlice_eq_solenoidalWeakMomentumSlice
          nse sol.u sol.p sol.Du φ hφ t
  weak_momentum_eq := by
    intro φ hφ
    simpa only [weakMomentumSlice_eq_solenoidalWeakMomentumSlice
      nse sol.u sol.p sol.Du φ hφ] using
      sol.weak_momentum_eq φ hφ.isWeakMomentumTest
  distributionallyDivergenceFree_at := sol.distributionallyDivergenceFree_at

/-- The initial boundary pairing in the pressure-free weak equation is integrable. -/
theorem WeakSolution.initialVelocityTestPairingDensity_integrable
    {n : ℕ} {nse : Problem n} (sol : WeakSolution nse)
    (φ : ℝ^(n + 1) → ℝ^n)
    (hφ : IsSolenoidalWeakMomentumTest sol.T φ) :
    Integrable (IncompressibleFlow.initialVelocityTestPairingDensity
      nse.toInitialValueData
      (fun x ↦ φ (PDE.Common.timeSpaceCons 0 x))) :=
  IncompressibleFlow.integrable_initialVelocityTestPairingDensity_of_memLp
    sol.initialVelocity_memLp hφ.isWeakMomentumTest

/-- The external-force power density is integrable at each physical time. -/
theorem WeakSolution.forcePowerDensity_integrable_at {n : ℕ}
    {nse : Problem n} (sol : WeakSolution nse)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ)) :
    Integrable (forcePowerDensity nse sol.u t) :=
  integrable_forcePowerDensity_of_memLp
    (sol.force_memLp_at ht) (sol.velocity_memLp_at ht)

/-- The kinetic-energy density is integrable at each physical time. -/
theorem WeakSolution.kineticEnergyDensity_integrable_at {n : ℕ}
    {nse : Problem n} (sol : WeakSolution nse)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ)) :
    Integrable (kineticEnergyDensity sol.u t) :=
  integrable_kineticEnergyDensity_of_memLp (sol.velocity_memLp_at ht)

/-- The prescribed initial kinetic-energy density is integrable. -/
theorem WeakSolution.initialKineticEnergyDensity_integrable {n : ℕ}
    {nse : Problem n} (sol : WeakSolution nse) :
    Integrable (initialKineticEnergyDensity nse) :=
  integrable_initialKineticEnergyDensity_of_memLp sol.initialVelocity_memLp

/-- The weak-gradient dissipation density is integrable at each positive physical time. -/
theorem WeakSolution.weakGradientDissipationDensity_integrable_at {n : ℕ}
    {nse : Problem n} (sol : WeakSolution nse)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 (sol.T : ℝ)) :
    Integrable (weakGradientDissipationDensity sol.Du t) :=
  integrable_weakGradientDissipationDensity_of_memLp (sol.gradient_memLp_at ht)

/-- The zero-extended `L²_x` velocity slice of a pressure-free weak solution. -/
noncomputable def WeakSolution.velocityL2Slice {n : ℕ} {nse : Problem n}
    (sol : WeakSolution nse) (t : ℝ) :
    MeasureTheory.Lp (ℝ^n) 2 (MeasureTheory.volume : Measure (ℝ^n)) :=
  IncompressibleFlow.velocityL2SliceOn sol.u sol.velocity_memLp_at t

/-- The `L²_x` weak-gradient slice, extended by zero outside `(0,T]`, including at `t = 0`. -/
noncomputable def WeakSolution.gradientL2Slice {n : ℕ} {nse : Problem n}
    (sol : WeakSolution nse) (t : ℝ) :
    MeasureTheory.Lp (IncompressibleFlow.SpatialMatrix n) 2
      (MeasureTheory.volume : Measure (ℝ^n)) :=
  if ht : t ∈ Set.Ioc 0 (sol.T : ℝ) then
    (sol.gradient_memLp_at ht).toLp (IncompressibleFlow.spatialGradientSlice sol.Du t)
  else 0

/-- The `L²` representative of the prescribed initial velocity. -/
noncomputable def WeakSolution.initialVelocityL2 {n : ℕ} {nse : Problem n}
    (sol : WeakSolution nse) :
    MeasureTheory.Lp (ℝ^n) 2 (MeasureTheory.volume : Measure (ℝ^n)) :=
  sol.initialVelocity_memLp.toLp nse.initialVelocity

/-- The selected `L²` class of the initial datum represents the prescribed velocity almost
everywhere. -/
theorem WeakSolution.initialVelocityL2_apply_ae {n : ℕ} {nse : Problem n}
    (sol : WeakSolution nse) :
    (sol.initialVelocityL2 : ℝ^n → ℝ^n) =ᵐ[MeasureTheory.volume] nse.initialVelocity := by
  simp [WeakSolution.initialVelocityL2, MemLp.coeFn_toLp]

/-- On the physical slab, the `L²` velocity slice represents the stored velocity almost
everywhere. -/
theorem WeakSolution.velocityL2Slice_apply_ae {n : ℕ} {nse : Problem n}
    (sol : WeakSolution nse) {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ)) :
    (sol.velocityL2Slice t : ℝ^n → ℝ^n)
      =ᵐ[MeasureTheory.volume] IncompressibleFlow.velocitySlice sol.u t :=
  IncompressibleFlow.velocityL2SliceOn_apply_ae sol.velocity_memLp_at ht

/-- At positive physical times, the `L²` gradient slice represents the stored weak gradient almost
everywhere. -/
theorem WeakSolution.gradientL2Slice_apply_ae {n : ℕ} {nse : Problem n}
    (sol : WeakSolution nse) {t : ℝ} (ht : t ∈ Set.Ioc 0 (sol.T : ℝ)) :
    (sol.gradientL2Slice t : ℝ^n → IncompressibleFlow.SpatialMatrix n)
      =ᵐ[MeasureTheory.volume] IncompressibleFlow.spatialGradientSlice sol.Du t := by
  simp [WeakSolution.gradientL2Slice, ht, MemLp.coeFn_toLp]

/-- The weak divergence pairing of every physical velocity slice vanishes. -/
theorem WeakSolution.weakDivergencePairing_eq_zero {n : ℕ} {nse : Problem n}
    (sol : WeakSolution nse) {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ))
    (ψ : ℝ^n → ℝ) (hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcompact : HasCompactSupport ψ) :
    IncompressibleFlow.weakDivergencePairing
      (IncompressibleFlow.velocitySlice sol.u t) ψ = 0 :=
  (sol.distributionallyDivergenceFree_at ht).weakDivergencePairing_eq_zero
    ψ hψsmooth hψcompact

/-- The weak divergence-pairing density of every physical velocity slice is integrable. -/
theorem WeakSolution.weakDivergencePairingDensity_integrable {n : ℕ}
    {nse : Problem n} (sol : WeakSolution nse)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ))
    (ψ : ℝ^n → ℝ) (hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcompact : HasCompactSupport ψ) :
    Integrable (IncompressibleFlow.weakDivergencePairingDensity
      (IncompressibleFlow.velocitySlice sol.u t) ψ) :=
  (sol.distributionallyDivergenceFree_at ht).weakDivergencePairingDensity_integrable
    ψ hψsmooth hψcompact

end NavierStokes
