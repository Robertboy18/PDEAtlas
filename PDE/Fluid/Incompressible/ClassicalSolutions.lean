/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Domain
public import PDE.Fluid.Incompressible.Operators

/-!
# Classical initial-value solutions for incompressible flow

Shared finite-time and global solution contracts for incompressible equations on `ℝ^n`. The
momentum law is an explicit predicate of the velocity, pressure, and spacetime point. This keeps
the analytic solution concept independent of the particular Euler or Navier–Stokes operator.

The residual structures impose the momentum predicate, incompressibility, and a representative-
level initial value, but no differentiability. The classical structures add the regularity needed
to interpret totalized differential operators as classical derivatives and to make the initial
value a one-sided trace.

A spacetime point of `ℝ^(n + 1)` has time in coordinate `0`. The equations hold on the open sets
`finiteTimeDomain n T = (0, T) × ℝ^n` and `PDE.Common.positiveTimeDomain = (0, ∞) × ℝ^n`. Because
the fields are total functions on all of `ℝ^(n + 1)`, regularity at the initial surface is stated
relative to the closed physical half-space `globalDomain n = [0, ∞) × ℝ^n`, so that smoothness up
to `t = 0` is a one-sided condition and the initial datum is recovered as the trace `u(0, ·)`.

The smooth-solution contract mirrors Fefferman's formulation of the Navier–Stokes problem, where
`u` and `p` are required to be `C^∞` on `ℝ^3 × [0, ∞)` (his condition (6)); Majda and Bertozzi
use the same notion of classical solution for the Euler equations (Chapter 3).

## Main definitions

* `FiniteTimeResidualSolution`, `GlobalResidualSolution`: velocity `u`, pressure `p`, the momentum
  predicate on the open domain, pointwise incompressibility, and the exact initial value.
* `FiniteTimeClassicalSolution`, `GlobalClassicalSolution`: the residual data together with
  ambient smoothness at positive times, respectively smoothness relative to the closed
  half-space, and continuity of `u` at the initial surface (`tendsto_initial`).
* `GlobalResidualSolution.toFiniteTime`, `GlobalClassicalSolution.toFiniteTime`: restriction of
  a global solution to a finite horizon `(0, T)`.

## References

* C. L. Fefferman, "Existence and smoothness of the Navier–Stokes equation", official problem
  description of the Clay Mathematics Institute, condition (6), p. 1.
  <https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf>
* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 3.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

namespace IncompressibleFlow

open EuclideanSpace
open scoped Topology

set_option linter.missingDocs true

/-- A finite-time incompressible residual solution for a prescribed momentum predicate.

The predicate `momentum u p x` is expected to express the equation-specific momentum law at `x`.
This structure contains no regularity or integrability assumptions. -/
structure FiniteTimeResidualSolution {n : ℕ}
    (initialVelocity : ℝ^n → ℝ^n)
    (momentum : (ℝ^(n + 1) → ℝ^n) → (ℝ^(n + 1) → ℝ) → ℝ^(n + 1) → Prop) where
  /-- Candidate velocity field. -/
  u : ℝ^(n + 1) → ℝ^n
  /-- Candidate pressure field. -/
  p : ℝ^(n + 1) → ℝ
  /-- Positive finite endpoint of the time interval. -/
  T : Set.Ioi (0 : ℝ)
  /-- The equation-specific momentum law on `(0,T) × ℝ^n`. -/
  momentum_at : ∀ {x : ℝ^(n + 1)}, x ∈ finiteTimeDomain n T → momentum u p x
  /-- Pointwise incompressibility on `(0,T) × ℝ^n`. -/
  divergenceFreeOn : DivergenceFreeOn u (finiteTimeDomain n T)
  /-- Exact representative-level value at time zero. -/
  initial_eq :
    ∀ x : ℝ^n, u (PDE.Common.timeSpaceCons 0 x) = initialVelocity x

namespace FiniteTimeResidualSolution

/-- The momentum law holds near every interior point of the finite-time domain. -/
theorem eventually_momentum_at {n : ℕ} {initialVelocity : ℝ^n → ℝ^n} {momentum}
    (sol : FiniteTimeResidualSolution initialVelocity momentum)
    {x : ℝ^(n + 1)} (hx : x ∈ finiteTimeDomain n sol.T) :
    ∀ᶠ y in nhds x, momentum sol.u sol.p y := by
  filter_upwards [(isOpen_finiteTimeDomain n sol.T).mem_nhds hx] with y hy
  exact sol.momentum_at hy

/-- Projection to pointwise incompressibility. -/
theorem incompressible_at {n : ℕ} {initialVelocity : ℝ^n → ℝ^n} {momentum}
    (sol : FiniteTimeResidualSolution initialVelocity momentum)
    {x : ℝ^(n + 1)} (hx : x ∈ finiteTimeDomain n sol.T) :
    DivergenceFreeAt sol.u x :=
  sol.divergenceFreeOn.at hx

/-- Incompressibility holds near every interior point of the finite-time domain. -/
theorem eventually_incompressible_at {n : ℕ} {initialVelocity : ℝ^n → ℝ^n}
    {momentum} (sol : FiniteTimeResidualSolution initialVelocity momentum)
    {x : ℝ^(n + 1)} (hx : x ∈ finiteTimeDomain n sol.T) :
    ∀ᶠ y in nhds x, DivergenceFreeAt sol.u y :=
  sol.divergenceFreeOn.eventually (isOpen_finiteTimeDomain n sol.T) hx

end FiniteTimeResidualSolution

/-- A finite-time classical solution for a prescribed momentum predicate.

Velocity and pressure are ambient-smooth at positive-time points. Relative continuity of velocity
at the initial surface makes the stored initial value a one-sided trace. -/
structure FiniteTimeClassicalSolution {n : ℕ}
    (initialVelocity : ℝ^n → ℝ^n)
    (momentum : (ℝ^(n + 1) → ℝ^n) → (ℝ^(n + 1) → ℝ) → ℝ^(n + 1) → Prop)
    extends FiniteTimeResidualSolution initialVelocity momentum where
  /-- Ambient smoothness of velocity at every positive-time domain point. -/
  velocity_contDiffAt :
    ∀ {x : ℝ^(n + 1)}, x ∈ finiteTimeDomain n T → ContDiffAt ℝ (⊤ : ℕ∞) u x
  /-- Ambient smoothness of pressure at every positive-time domain point. -/
  pressure_contDiffAt :
    ∀ {x : ℝ^(n + 1)}, x ∈ finiteTimeDomain n T → ContDiffAt ℝ (⊤ : ℕ∞) p x
  /-- One-sided continuity of velocity at the initial surface. -/
  continuousWithinAt_initial :
    ∀ x : ℝ^n, ContinuousWithinAt u (globalDomain n) (PDE.Common.timeSpaceCons 0 x)

namespace FiniteTimeClassicalSolution

/-- The velocity tends to its prescribed datum through the physical half-space. -/
theorem tendsto_initial {n : ℕ} {initialVelocity : ℝ^n → ℝ^n} {momentum}
    (sol : FiniteTimeClassicalSolution initialVelocity momentum) (x : ℝ^n) :
    Filter.Tendsto sol.u
      (nhdsWithin (PDE.Common.timeSpaceCons 0 x) (globalDomain n))
      (nhds (initialVelocity x)) := by
  rw [← sol.initial_eq x]
  exact sol.continuousWithinAt_initial x

end FiniteTimeClassicalSolution

/-- A global incompressible residual solution for a prescribed momentum predicate. -/
structure GlobalResidualSolution {n : ℕ}
    (initialVelocity : ℝ^n → ℝ^n)
    (momentum : (ℝ^(n + 1) → ℝ^n) → (ℝ^(n + 1) → ℝ) → ℝ^(n + 1) → Prop) where
  /-- Candidate velocity field. -/
  u : ℝ^(n + 1) → ℝ^n
  /-- Candidate pressure field. -/
  p : ℝ^(n + 1) → ℝ
  /-- The equation-specific momentum law at every strictly positive time. -/
  momentum_at : ∀ {x : ℝ^(n + 1)}, x ∈ PDE.Common.positiveTimeDomain → momentum u p x
  /-- Pointwise incompressibility at every strictly positive time. -/
  divergenceFreeOn : DivergenceFreeOn u PDE.Common.positiveTimeDomain
  /-- Exact representative-level value at time zero. -/
  initial_eq :
    ∀ x : ℝ^n, u (PDE.Common.timeSpaceCons 0 x) = initialVelocity x

namespace GlobalResidualSolution

/-- The momentum law holds near every strictly positive-time point. -/
theorem eventually_momentum_at {n : ℕ} {initialVelocity : ℝ^n → ℝ^n} {momentum}
    (sol : GlobalResidualSolution initialVelocity momentum)
    {x : ℝ^(n + 1)} (hx : x ∈ PDE.Common.positiveTimeDomain) :
    ∀ᶠ y in nhds x, momentum sol.u sol.p y := by
  filter_upwards [PDE.Common.isOpen_positiveTimeDomain.mem_nhds hx] with y hy
  exact sol.momentum_at hy

/-- Projection to pointwise incompressibility at positive time. -/
theorem incompressible_at {n : ℕ} {initialVelocity : ℝ^n → ℝ^n} {momentum}
    (sol : GlobalResidualSolution initialVelocity momentum)
    {x : ℝ^(n + 1)} (hx : x ∈ PDE.Common.positiveTimeDomain) :
    DivergenceFreeAt sol.u x :=
  sol.divergenceFreeOn.at hx

/-- Incompressibility holds near every strictly positive-time point. -/
theorem eventually_incompressible_at {n : ℕ} {initialVelocity : ℝ^n → ℝ^n}
    {momentum} (sol : GlobalResidualSolution initialVelocity momentum)
    {x : ℝ^(n + 1)} (hx : x ∈ PDE.Common.positiveTimeDomain) :
    ∀ᶠ y in nhds x, DivergenceFreeAt sol.u y :=
  sol.divergenceFreeOn.eventually PDE.Common.isOpen_positiveTimeDomain hx

/-- Restriction of a global residual solution to a positive finite horizon. -/
def toFiniteTime {n : ℕ} {initialVelocity : ℝ^n → ℝ^n} {momentum}
    (sol : GlobalResidualSolution initialVelocity momentum) (T : ℝ) (hT : 0 < T) :
    FiniteTimeResidualSolution initialVelocity momentum where
  u := sol.u
  p := sol.p
  T := ⟨T, hT⟩
  momentum_at := fun hx ↦ sol.momentum_at hx.1
  divergenceFreeOn := fun _ hx ↦ sol.incompressible_at hx.1
  initial_eq := sol.initial_eq

end GlobalResidualSolution

/-- A global classical solution for a prescribed momentum predicate.

Velocity and pressure are smooth relative to the closed physical half-space. At time zero this is
a one-sided regularity statement and supplies the initial trace. -/
structure GlobalClassicalSolution {n : ℕ}
    (initialVelocity : ℝ^n → ℝ^n)
    (momentum : (ℝ^(n + 1) → ℝ^n) → (ℝ^(n + 1) → ℝ) → ℝ^(n + 1) → Prop)
    extends GlobalResidualSolution initialVelocity momentum where
  /-- Relative smoothness of velocity on the closed physical half-space. -/
  velocity_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) u (globalDomain n)
  /-- Relative smoothness of pressure on the closed physical half-space. -/
  pressure_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) p (globalDomain n)

namespace GlobalClassicalSolution

/-- The velocity tends to its prescribed datum through nonnegative times. -/
theorem tendsto_initial {n : ℕ} {initialVelocity : ℝ^n → ℝ^n} {momentum}
    (sol : GlobalClassicalSolution initialVelocity momentum) (x : ℝ^n) :
    Filter.Tendsto sol.u
      (nhdsWithin (PDE.Common.timeSpaceCons 0 x) (globalDomain n))
      (nhds (initialVelocity x)) := by
  rw [← sol.initial_eq x]
  exact sol.velocity_contDiffOn.continuousOn.continuousWithinAt
    (timeSpaceCons_zero_mem_globalDomain x)

/-- Restriction of a global classical solution to a positive finite horizon. -/
def toFiniteTime {n : ℕ} {initialVelocity : ℝ^n → ℝ^n} {momentum}
    (sol : GlobalClassicalSolution initialVelocity momentum) (T : ℝ) (hT : 0 < T) :
    FiniteTimeClassicalSolution initialVelocity momentum where
  toFiniteTimeResidualSolution := sol.toGlobalResidualSolution.toFiniteTime T hT
  velocity_contDiffAt := by
    intro x hx
    exact sol.velocity_contDiffOn.contDiffAt (globalDomain_mem_nhds hx.1)
  pressure_contDiffAt := by
    intro x hx
    exact sol.pressure_contDiffOn.contDiffAt (globalDomain_mem_nhds hx.1)
  continuousWithinAt_initial := by
    intro x
    exact sol.velocity_contDiffOn.continuousOn.continuousWithinAt
      (timeSpaceCons_zero_mem_globalDomain x)

end GlobalClassicalSolution

end IncompressibleFlow
