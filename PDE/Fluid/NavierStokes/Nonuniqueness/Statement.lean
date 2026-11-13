/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Suitable

/-!
# The statement of Leray–Hopf nonuniqueness

`unforcedProblem u₀ hu₀` is the Navier–Stokes problem on `ℝ^n` with zero forcing, unit
viscosity and initial velocity `u₀`.

`NonuniquenessConclusion` is Theorem 1 of Hou, Wang and Yang: there is a
compactly supported divergence-free datum `u₀`, smooth away from the origin and in every `Lᵠ`
with `q < 3`, and a family of suitable Leray–Hopf solutions on `[0,1]` with datum `u₀`, indexed
by `s ∈ [0,1]`, whose velocities at time one are pairwise distinct `L²` classes. Every member is
smooth at positive times and lies in `Lʳ(0,1; Lᵠ(ℝ^3))` whenever `q ≥ 2`, `r ≥ 1` and
`3/q + 2/r > 1`. Leray–Hopf solutions are those of Definition 1 of the paper, and suitability
is the local energy inequality of Remark 1.

`ClassicalEnergyClass u p T` collects the energy-class bounds of a classical velocity and
pressure on `(0,T] × ℝ^n`. On `ℝ^3`, together with smoothness on the open slab
`(0,T) × ℝ^3`, the momentum equation, incompressibility and an `L²` initial trace, these bounds
make a classical solution of the unforced problem a suitable Leray–Hopf solution. The global
energy equality follows from the local one with spatial cutoffs: the Sobolev inequality puts
`u(t)` in `L⁶`, interpolation with `L²` gives `u ∈ L³((0,T) × ℝ^3)`, and with
`p ∈ L¹(0,T; L²)` the energy flux through the cutoffs tends to zero.

Smoothness means `ContDiff ℝ (⊤ : ℕ∞)`, infinite differentiability. The top element of
`WithTop ℕ∞` would mean analyticity, which a nonzero compactly supported datum cannot have on
`ℝ^3 \ {0}`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Theorem 1, p. 1, and Section 1.1,
  Definition 1, Remark 1 and (1.2), p. 2.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory Filter
open scoped ENNReal Topology

set_option linter.missingDocs true

/-- The unforced Navier–Stokes problem on `ℝ^n` with unit viscosity and initial velocity
`u₀`. -/
def unforcedProblem {n : ℕ} (u₀ : ℝ^n → ℝ^n)
    (hu₀ : IncompressibleFlow.DistributionallyDivergenceFree u₀) : Problem n where
  forcing := fun _ ↦ 0
  initialVelocity := u₀
  initialVelocity_distributionallyDivergenceFree := hu₀
  kinematicViscosity := ⟨1, one_pos⟩

/-- The unforced problem has zero forcing. -/
@[simp]
theorem unforcedProblem_forcing {n : ℕ} (u₀ : ℝ^n → ℝ^n)
    (hu₀ : IncompressibleFlow.DistributionallyDivergenceFree u₀) :
    (unforcedProblem u₀ hu₀).forcing = fun _ ↦ 0 :=
  rfl

/-- The initial velocity of the unforced problem is the prescribed datum. -/
@[simp]
theorem unforcedProblem_initialVelocity {n : ℕ} (u₀ : ℝ^n → ℝ^n)
    (hu₀ : IncompressibleFlow.DistributionallyDivergenceFree u₀) :
    (unforcedProblem u₀ hu₀).initialVelocity = u₀ :=
  rfl

/-- The unforced problem has unit kinematic viscosity. -/
@[simp]
theorem unforcedProblem_kinematicViscosity {n : ℕ} (u₀ : ℝ^n → ℝ^n)
    (hu₀ : IncompressibleFlow.DistributionallyDivergenceFree u₀) :
    ((unforcedProblem u₀ hu₀).kinematicViscosity : ℝ) = 1 :=
  rfl

/-- Energy-class bounds of a classical velocity `u` and pressure `p` on `(0,T] × ℝ^n`.

Derivatives of slices are spatial derivatives of `x ↦ u(t,x)`; at interior times they agree
with the spatial part of the spacetime derivative. The velocity, its spatial derivative and the
pressure have square-integrable slices; `u ∈ L∞(0,T; L²)`, `∇u ∈ L²(0,T; L²)` and
`p ∈ L¹(0,T; L²)`; the velocity slices are continuous into `L²` on `(0,T]`. Every positive-time
velocity slice is continuously differentiable. At `t = T` neither this nor the continuity
follows from smoothness on the open slab `(0,T) × ℝ^n`, and the Leray–Hopf interface needs the
weak gradient and weak continuity there. The pressure condition includes `t = 0`, as in
`PressureWeakSolution`.

Joint measurability of `u` and `p` is not a field: on the open slab it follows from the
smoothness that accompanies the class. -/
structure ClassicalEnergyClass {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ) (T : ℝ) :
    Prop where
  /-- The time horizon is positive. -/
  time_pos : 0 < T
  /-- Every velocity slice at a positive time is continuously differentiable in space. -/
  slice_contDiff : ∀ t ∈ Set.Ioc 0 T,
    ContDiff ℝ 1 (IncompressibleFlow.velocitySlice u t)
  /-- Every velocity slice at a positive time is square integrable. -/
  velocity_memLp : ∀ t ∈ Set.Ioc 0 T,
    MemLp (IncompressibleFlow.velocitySlice u t) 2 volume
  /-- The spatial derivative of every positive-time velocity slice is square integrable. -/
  gradient_memLp : ∀ t ∈ Set.Ioc 0 T,
    MemLp (fderiv ℝ (IncompressibleFlow.velocitySlice u t)) 2 volume
  /-- Every pressure slice on the closed slab `[0,T]` is square integrable. -/
  pressure_memLp : ∀ t ∈ Set.Icc 0 T,
    MemLp (fun x ↦ p (PDE.Common.timeSpaceCons t x)) 2 volume
  /-- The velocity lies in `L∞(0,T; L²)`. -/
  velocity_bounded : ∃ C : ℝ, ∀ t ∈ Set.Ioc 0 T,
    eLpNorm (IncompressibleFlow.velocitySlice u t) 2 volume ≤ ENNReal.ofReal C
  /-- The spatial derivative lies in `L²(0,T; L²)`. -/
  gradient_sq_integrableOn : IntegrableOn
    (fun t ↦ (eLpNorm (fderiv ℝ (IncompressibleFlow.velocitySlice u t)) 2 volume).toReal ^ 2)
    (Set.Ioc 0 T)
  /-- The pressure lies in `L¹(0,T; L²)`. -/
  pressure_integrableOn : IntegrableOn
    (fun t ↦ (eLpNorm (fun x ↦ p (PDE.Common.timeSpaceCons t x)) 2 volume).toReal)
    (Set.Ioc 0 T)
  /-- The velocity slices are continuous into `L²` on `(0,T]`. -/
  tendsto_velocity : ∀ t ∈ Set.Ioc 0 T,
    Tendsto (fun s ↦ eLpNorm (IncompressibleFlow.velocitySlice u s -
      IncompressibleFlow.velocitySlice u t) 2 volume) (𝓝[Set.Ioc 0 T] t) (𝓝 0)

/-- Theorem 1 of Hou, Wang and Yang: infinitely many distinct suitable
Leray–Hopf solutions of the unforced Navier–Stokes equations on `ℝ^3 × [0,1]` with one
initial datum.

The datum `u₀` is divergence-free, compactly supported, smooth away from the origin and in
`Lᵠ` for every `q < 3`. The solutions are indexed by `s ∈ [0,1]`, have horizon one, and their
velocities at time one are pairwise distinct `L²` classes. Each is smooth on `(0,1) × ℝ^3` in
velocity and pressure, and for `q ≥ 2`, `r ≥ 1` with `3/q + 2/r > 1` its velocity slices lie
in `Lᵠ` at positive times with `t ↦ ‖u(t)‖_q` in `Lʳ(0,1)`. -/
def NonuniquenessConclusion : Prop :=
  ∃ (u₀ : ℝ^3 → ℝ^3) (hu₀ : IncompressibleFlow.DistributionallyDivergenceFree u₀),
    HasCompactSupport u₀ ∧
    (∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u₀ x) ∧
    (∀ q : ℝ≥0∞, q < 3 → MemLp u₀ q volume) ∧
    ∃ sol : Set.Icc (0 : ℝ) 1 → SuitableLerayHopfSolution (unforcedProblem u₀ hu₀),
      (∀ s, ((sol s).T : ℝ) = 1) ∧
      Function.Injective (fun s ↦ (sol s).toPressureRepresentativeLerayHopfSolution
        |>.toLerayHopfSolution.toWeakSolution.velocityL2Slice 1) ∧
      (∀ s, ∀ z ∈ IncompressibleFlow.finiteTimeDomain 3 1,
        ContDiffAt ℝ (⊤ : ℕ∞) (sol s).u z ∧ ContDiffAt ℝ (⊤ : ℕ∞) (sol s).p z) ∧
      (∀ s (q r : ℝ), 2 ≤ q → 1 ≤ r → 1 < 3 / q + 2 / r →
        (∀ t ∈ Set.Ioc (0 : ℝ) 1,
          MemLp (IncompressibleFlow.velocitySlice (sol s).u t) (ENNReal.ofReal q) volume) ∧
        MemLp (fun t ↦ (eLpNorm (IncompressibleFlow.velocitySlice (sol s).u t)
            (ENNReal.ofReal q) volume).toReal)
          (ENNReal.ofReal r) (volume.restrict (Set.Ioc (0 : ℝ) 1)))

end NavierStokes
