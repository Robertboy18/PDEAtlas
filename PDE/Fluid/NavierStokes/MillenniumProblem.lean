/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.GlobalSolutions
public import PDE.Fluid.NavierStokes.ZeroData
import PDE.Fluid.NavierStokes.ZeroSolutions.Classical

/-!
# Navier-Stokes Millennium Problem

We state the real-domain alternatives (A) and (C) of Fefferman's Clay problem description
(pp. 1-2) over this library's `GlobalSmoothSolution`. As in the Lean statements of the Millennium
Prize Problems (`lean-dojo/LeanMillenniumPrizeProblems`), global in time means a
`GlobalSmoothSolution`, never a finite horizon `T` read as infinity.

The Clay problem on `ℝ^3` asks for a proof of (A) or a proof of (C). Their disjunction alone
follows classically: if (A) fails at some viscosity `ν`, the scaling `v(x, t) = a • u(x, a t)`
with `a > 0` maps solutions at viscosity `ν` to solutions at viscosity `a ν` and keeps zero force
zero, which gives (C) at every viscosity. So we state the two alternatives separately.

The force is a smooth function on all of spacetime,
`forcing_contDiff : ContDiff ℝ (⊤ : ℕ∞) forcing`, restricted to `t ≥ 0`. The solution interface
imposes momentum and incompressibility at strictly positive times, with the initial trace on the
closed half-space, so no physical meaning is attached to totalized derivatives at `t = 0`.
`FeffermanC` quantifies the viscosity first and then the data, as in Fefferman's statement (C).
We do not state the periodic alternatives (B) and (D). All declarations live in the namespace
`MillenniumNSRDomain`, for the spatial domain `ℝ^3`.

## Main declarations

* `InitialData`, `MillenniumProblem`: the admissible data classes, namely smooth divergence-free
  rapidly decreasing initial velocity, smooth rapidly decreasing force, and positive viscosity.
* `HasGlobalSmoothFiniteEnergySolution`: existence of a `GlobalSmoothSolution` with uniformly
  bounded kinetic energy, Fefferman's condition (7).
* `FeffermanA`, `FeffermanC`: the formal alternatives (A) and (C).
* `zeroInitialData_hasGlobalSmoothFiniteEnergySolution`: the zero datum is a solved instance of
  the existence predicate.

## References

* C. L. Fefferman, "Existence and smoothness of the Navier–Stokes equation", official problem
  description of the Clay Mathematics Institute, conditions (4), (5) and (7), p. 1, and statements
  (A) and (C), p. 2; also in J. Carlson, A. Jaffe and A. Wiles (eds.), *The Millennium Prize
  Problems*, Clay Mathematics Institute and American Mathematical Society, 2006.
  <https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf>
* R. J. George, "Formalization of the Millennium Prize Problem Statements in Lean 4", version 3.0.0,
  file Problems/NavierStokes/MillenniumRDomain.lean.
  <https://github.com/lean-dojo/LeanMillenniumPrizeProblems>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

namespace MillenniumNSRDomain

open EuclideanSpace MeasureTheory Order NavierStokes

/-- Rapid spatial-decay bounds for all formal component derivatives of a vector field on `ℝ^3`.

For every component, every iterated partial derivative, and every polynomial weight, the weighted
absolute value is bounded. This predicate does not by itself assert differentiability because
`iteratedPartialDeriv` is totalized; `InitialData.initialVelocity_contDiff` supplies that
independent hypothesis. Together they formulate the rapidly decreasing initial-data condition in
the Fefferman/Clay statement. -/
def RapidlyDecayingInitialVelocity (initialVelocity : ℝ^3 → ℝ^3) :
    Prop :=
  ∀ (i : Fin 3) (α : List (Fin 3)) (K : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ^3,
        (1 + ‖x‖) ^ K *
          |iteratedPartialDeriv α (fun y ↦ initialVelocity y i) x| ≤ C

/-- Smooth rapidly decreasing, divergence-free initial data on `ℝ^3`.

This is the data class in Fefferman's condition (4). Finite kinetic energy is not stored as an
independent hypothesis: rapid decay is the stronger source condition, while the uniform energy
bound belongs to the solution-side condition (7). -/
structure InitialData where
  /-- Initial velocity field. -/
  initialVelocity : ℝ^3 → ℝ^3
  /-- Smoothness of the initial velocity. -/
  initialVelocity_contDiff : ContDiff ℝ (⊤ : ℕ∞) initialVelocity
  /-- Rapid spatial decay of all component derivatives. -/
  initialVelocity_rapidlyDecaying :
    RapidlyDecayingInitialVelocity initialVelocity
  /-- Incompressibility of the initial velocity. -/
  initialVelocity_divergenceFree :
    IncompressibleFlow.SpatialFieldDivergenceFree initialVelocity

/-- Rapid spacetime-decay bounds for formal derivatives of a force on `[0,∞) × ℝ^3`.

For every component, every iterated spacetime partial derivative, and every polynomial weight,
the `(1 + |x| + t)`-weighted absolute value is bounded on the physical domain. This matches the
Fefferman/Clay convention for the forced problem: derivatives may include the time coordinate and
the rapid-decay weight includes both the spatial size and time. Smoothness is a separate field of
`MillenniumProblem`; this predicate alone does not infer it from totalized derivatives. -/
def RapidlyDecayingForce (forcing : ℝ^(3 + 1) → ℝ^3) : Prop :=
  ∀ (i : Fin 3) (α : List (Fin 4)) (K : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ xt : ℝ^4, xt ∈ IncompressibleFlow.globalDomain 3 →
        (1 + ‖PDE.Common.spatialPart xt‖ + xt 0) ^ K *
            |iteratedPartialDeriv α (fun y ↦ forcing y i) xt| ≤ C

/-- A concrete Navier-Stokes problem datum on `ℝ^3`. -/
structure MillenniumProblem where
  /-- Initial data. -/
  initial : InitialData
  /-- Positive kinematic-viscosity coefficient. -/
  kinematicViscosity : Set.Ioi (0 : ℝ)
  /-- External force field. -/
  forcing : ℝ^(3 + 1) → ℝ^3
  /-- A smooth ambient extension of the force field.

  The force is represented by a function on all spacetime, so global
  `ContDiff` is the direct way to make the ambient derivatives in condition
  (5) meaningful at the initial-time boundary. Only its restriction to
  `t ≥ 0` enters the physical problem. -/
  forcing_contDiff : ContDiff ℝ (⊤ : ℕ∞) forcing
  /-- Rapid spacetime decay of all force components and spacetime derivatives. -/
  forcing_rapidlyDecaying : RapidlyDecayingForce forcing

/-- The Navier-Stokes equations determined by a Millennium problem datum.

It is computed from the fields of `problem`, so its viscosity, forcing, and initial velocity are
those of the datum. -/
def MillenniumProblem.nse (problem : MillenniumProblem) : Problem 3 :=
  { kinematicViscosity := problem.kinematicViscosity
    forcing := problem.forcing
    initialVelocity := problem.initial.initialVelocity
    initialVelocity_distributionallyDivergenceFree :=
      problem.initial.initialVelocity_divergenceFree.distributionallyDivergenceFree
        (problem.initial.initialVelocity_contDiff.of_le (by simp)) }

/-- Zero forcing. -/
def zeroForce : ℝ^(3 + 1) → ℝ^3 := fun _ ↦ 0

/-- Zero initial data for the `ℝ^3` Navier-Stokes problem. -/
def zeroInitialData : InitialData where
  initialVelocity := fun _ ↦ 0
  initialVelocity_contDiff := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : ℝ^3 ↦ (0 : ℝ^3))
    fun_prop
  initialVelocity_rapidlyDecaying := by
    intro i α K
    refine ⟨0, le_rfl, ?_⟩
    intro x
    change (1 + ‖x‖) ^ K *
        |iteratedPartialDeriv α (fun _ : ℝ^3 ↦ (0 : ℝ)) x| ≤ 0
    have hzero :
        iteratedPartialDeriv α (fun _ : ℝ^3 ↦ (0 : ℝ)) x = 0 :=
      PDE.iteratedPartialDeriv_zero (n := 3) α x
    rw [hzero]
    simp
  initialVelocity_divergenceFree := by
    intro x
    simp [partialDeriv]

/-- Fefferman's uniform-in-time kinetic-energy condition (7).

The library's `kineticEnergy` includes the conventional factor `1/2`; changing that normalization
only rescales the existential bound and therefore does not change the mathematical condition. -/
def HasUniformlyBoundedKineticEnergy (u : ℝ^(3 + 1) → ℝ^3) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 0 ≤ t →
      Integrable (kineticEnergyDensity u t) ∧
      kineticEnergy u t < C

/-- One admissible datum has a global smooth solution satisfying Fefferman's
energy condition (7). -/
def HasGlobalSmoothFiniteEnergySolution (problem : MillenniumProblem) : Prop :=
  ∃ sol : GlobalSmoothSolution problem.nse, HasUniformlyBoundedKineticEnergy sol.u

/-- The zero velocity field has uniformly bounded kinetic energy. -/
theorem zeroVelocity_hasUniformlyBoundedKineticEnergy :
    HasUniformlyBoundedKineticEnergy (fun _ : ℝ^(3 + 1) ↦
      (0 : ℝ^3)) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro t ht
  constructor
  · exact integrable_kineticEnergyDensity_of_memLp MemLp.zero
  · simp [kineticEnergy, kineticEnergyDensity,
      IncompressibleFlow.specificKineticEnergy]

/-- Build a problem with zero forcing from initial data and viscosity. -/
def problemWithZeroForce (initial : InitialData) (viscosity : ℝ) (hviscosity : 0 < viscosity) :
    MillenniumProblem where
  initial := initial
  kinematicViscosity := ⟨viscosity, hviscosity⟩
  forcing := zeroForce
  forcing_contDiff := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : ℝ^(3 + 1) ↦ (0 : ℝ^3))
    fun_prop
  forcing_rapidlyDecaying := by
    intro i α K
    refine ⟨0, le_rfl, ?_⟩
    intro xt hxt
    change (1 + ‖PDE.Common.spatialPart xt‖ + xt 0) ^ K *
        |iteratedPartialDeriv α (fun _ ↦ (0 : ℝ)) xt| ≤ 0
    have hzero :
        iteratedPartialDeriv α (fun _ : ℝ^4 ↦ (0 : ℝ)) xt = 0 := by
      exact PDE.iteratedPartialDeriv_zero (n := 4) α xt
    rw [hzero]
    simp

/-- The zero Millennium datum computes to the core zero Navier-Stokes problem.

The Clay/Fefferman zero datum and the core Navier-Stokes zero-data formulation are
definitionally the same problem. -/
theorem problemWithZeroForce_zeroInitialData_nse (viscosity : ℝ) (hviscosity : 0 < viscosity) :
    (problemWithZeroForce zeroInitialData viscosity hviscosity).nse =
      NavierStokes.zeroProblem 3 viscosity hviscosity :=
  rfl

/-- Formal Fefferman-style existence-and-smoothness alternative on `ℝ^3`, with zero forcing.

This proposition is the existence side of the open problem. -/
def FeffermanA : Prop :=
  ∀ (initial : InitialData) (viscosity : ℝ) (hviscosity : 0 < viscosity),
    HasGlobalSmoothFiniteEnergySolution (problemWithZeroForce initial viscosity hviscosity)

/-- Formal Fefferman-style breakdown/nonexistence alternative on `ℝ^3`, allowing smooth forcing.

For every fixed positive viscosity, it asks for admissible initial data and forcing for which no
global smooth finite-energy solution exists. This is the quantifier order in Fefferman's statement
(C); an existential quantifier over the viscosity would give a formally weaker statement. -/
def FeffermanC : Prop :=
  ∀ (viscosity : ℝ), 0 < viscosity →
    ∃ problem : MillenniumProblem,
      (problem.kinematicViscosity : ℝ) = viscosity ∧
        ¬ HasGlobalSmoothFiniteEnergySolution problem

/-- The zero Millennium datum has a global smooth finite-energy solution, namely zero. -/
theorem zeroInitialData_hasGlobalSmoothFiniteEnergySolution
    (viscosity : ℝ) (hviscosity : 0 < viscosity) :
    HasGlobalSmoothFiniteEnergySolution
      (problemWithZeroForce zeroInitialData viscosity hviscosity) := by
  refine ⟨NavierStokes.zeroGlobalSmoothSolution (n := 3) viscosity hviscosity, ?_⟩
  exact zeroVelocity_hasUniformlyBoundedKineticEnergy

end MillenniumNSRDomain
