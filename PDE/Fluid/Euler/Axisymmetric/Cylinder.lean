/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Problem
public import PDE.CoordinateSystems.Axisymmetric

/-!
# Euler flow in a periodic cylinder with a solid wall

Incompressible Euler flow in the solid cylinder of unit radius around the third coordinate
axis, periodic in the axial coordinate `z = x₂` with period `L`, with the impermeability
condition `u · n = 0` on the wall `{r = 1}`. The periodic cylinder `{r ≤ 1} × ℝ/Lℤ` is
represented by its covering `{r ≤ 1} × ℝ`: fields are total functions on spacetime `ℝ^4`
(time in coordinate `0`) that are `L`-periodic in coordinate `3`.

`SmoothSolution L data` is the classical notion. Velocity and pressure are smooth at every
point of `(0,T) × {r < 1}`, where the Euler momentum equation `Euler.MomentumEquationAt` and
incompressibility hold. The velocity is `C¹` up to the wall, so that its normal component on
`{r = 1}` is the classical one, and continuous at the initial surface, where it takes the
prescribed datum. On the whole space this is the notion of
`IncompressibleFlow.FiniteTimeClassicalSolution`; the momentum predicate is the same.

The pressure is required to be periodic, not only its gradient: a periodic gradient allows a
pressure `p₀ + c(t) z`, which drives a mean axial flow and is a different problem (for example
`u = a(t) e_z`, `p = -a'(t) z`). Unforced flows, as in Chen and Hou, are those with
`data.forcing = 0`.

## Main definitions

* `domain`, `closedDomain`, `wall`: the open and closed solid cylinders and their boundary.
* `spacetimeDomain`, `closedSpacetimeDomain`, `wallSpacetime`, `physicalDomain`: the spacetime
  sets `(0,T) × {r < 1}`, `(0,T) × {r ≤ 1}`, `(0,T) × {r = 1}` and `[0,T) × {r ≤ 1}`.
* `IsAxiallyPeriodicOn`: periodicity in the axial coordinate on a spacetime set.
* `wallNormalVelocity`: `x₀ u₀ + x₁ u₁`, the normal velocity on the wall.
* `SmoothSolution`: classical Euler solutions in the periodic cylinder with the wall condition.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6, pp. 94-95 (the case
  `L = 2`).
  <https://arxiv.org/abs/2210.07191v4>
* G. Luo and T. Y. Hou, "Potentially singular solutions of the 3D axisymmetric Euler equations",
  Proc. Natl. Acad. Sci. USA 111 (2014), no. 36, 12968-12973, for the same geometry.
  <https://doi.org/10.1073/pnas.1405238111>
-/

@[expose] public section

namespace Euler.Cylinder

open EuclideanSpace
open PDE.Common PDE.CoordinateSystems IncompressibleFlow
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-- The open solid cylinder `{x | x₀² + x₁² < 1}` of unit radius around the third axis. -/
def domain : Set (ℝ^3) :=
  {x | cylindricalRadiusSq x < 1}

/-- The closed solid cylinder `{x | x₀² + x₁² ≤ 1}`. -/
def closedDomain : Set (ℝ^3) :=
  {x | cylindricalRadiusSq x ≤ 1}

/-- The wall `{x | x₀² + x₁² = 1}` of the cylinder. -/
def wall : Set (ℝ^3) :=
  {x | cylindricalRadiusSq x = 1}

/-- The squared cylindrical radius is a continuous function. -/
theorem continuous_cylindricalRadiusSq : Continuous cylindricalRadiusSq := by
  unfold cylindricalRadiusSq
  fun_prop

/-- The open cylinder is open. -/
theorem isOpen_domain : IsOpen domain :=
  isOpen_lt continuous_cylindricalRadiusSq continuous_const

/-- The closed cylinder is closed. -/
theorem isClosed_closedDomain : IsClosed closedDomain :=
  isClosed_le continuous_cylindricalRadiusSq continuous_const

/-- The wall is closed. -/
theorem isClosed_wall : IsClosed wall :=
  isClosed_eq continuous_cylindricalRadiusSq continuous_const

/-- The squared cylindrical radius is a convex function. -/
theorem convexOn_cylindricalRadiusSq : ConvexOn ℝ Set.univ cylindricalRadiusSq := by
  have h0 : ConvexOn ℝ Set.univ (fun x : ℝ^3 ↦ x 0 ^ 2) := by
    simpa [Function.comp_def] using
      (Even.convexOn_pow (n := 2) even_two).comp_linearMap
        ((EuclideanSpace.proj (0 : Fin 3) : ℝ^3 →L[ℝ] ℝ) : ℝ^3 →ₗ[ℝ] ℝ)
  have h1 : ConvexOn ℝ Set.univ (fun x : ℝ^3 ↦ x 1 ^ 2) := by
    simpa [Function.comp_def] using
      (Even.convexOn_pow (n := 2) even_two).comp_linearMap
        ((EuclideanSpace.proj (1 : Fin 3) : ℝ^3 →L[ℝ] ℝ) : ℝ^3 →ₗ[ℝ] ℝ)
  exact h0.add h1

/-- The open cylinder is convex. -/
theorem convex_domain : Convex ℝ domain := by
  simpa [domain] using convexOn_cylindricalRadiusSq.convex_lt 1

/-- The closed cylinder is convex. -/
theorem convex_closedDomain : Convex ℝ closedDomain := by
  simpa [closedDomain] using convexOn_cylindricalRadiusSq.convex_le 1

/-- The open cylinder lies in the closed one. -/
theorem domain_subset_closedDomain : domain ⊆ closedDomain :=
  fun x hx ↦ (show cylindricalRadiusSq x < 1 from hx).le

/-- The wall lies in the closed cylinder. -/
theorem wall_subset_closedDomain : wall ⊆ closedDomain :=
  fun x hx ↦ (show cylindricalRadiusSq x = 1 from hx).le

/-- The closed cylinder is the union of the open cylinder and the wall. -/
theorem closedDomain_eq_union : closedDomain = domain ∪ wall := by
  ext x
  simp only [closedDomain, domain, wall, Set.mem_ofPred_eq, Set.mem_union]
  exact le_iff_lt_or_eq

/-- The origin lies in the open cylinder. -/
theorem zero_mem_domain : (0 : ℝ^3) ∈ domain := by
  simp [domain, cylindricalRadiusSq]

/-- Positive-time spacetime `(0,T) × {r < 1}`, where the equations are imposed. -/
def spacetimeDomain (T : ℝ) : Set (ℝ^4) :=
  {xt | 0 < xt 0 ∧ xt 0 < T ∧ spatialPart xt ∈ domain}

/-- Positive-time spacetime up to the wall, `(0,T) × {r ≤ 1}`. -/
def closedSpacetimeDomain (T : ℝ) : Set (ℝ^4) :=
  {xt | 0 < xt 0 ∧ xt 0 < T ∧ spatialPart xt ∈ closedDomain}

/-- Positive-time points of the wall, `(0,T) × {r = 1}`. -/
def wallSpacetime (T : ℝ) : Set (ℝ^4) :=
  {xt | 0 < xt 0 ∧ xt 0 < T ∧ spatialPart xt ∈ wall}

/-- The physical spacetime domain `[0,T) × {r ≤ 1}`, through which the initial trace is
taken. -/
def physicalDomain (T : ℝ) : Set (ℝ^4) :=
  {xt | 0 ≤ xt 0 ∧ xt 0 < T ∧ spatialPart xt ∈ closedDomain}

/-- The spatial part of a spacetime point depends continuously on the point. -/
theorem continuous_spatialPart : Continuous (spatialPart : ℝ^4 → ℝ^3) := by
  have h : (spatialPart : ℝ^4 → ℝ^3) = spatialPartCLM 3 :=
    funext fun z ↦ (spatialPartCLM_eq_spatialPart 3 z).symm
  rw [h]
  exact (spatialPartCLM 3).continuous

/-- The positive-time open spacetime cylinder is open. -/
theorem isOpen_spacetimeDomain (T : ℝ) : IsOpen (spacetimeDomain T) := by
  have htime : Continuous (fun xt : ℝ^4 ↦ xt 0) := by fun_prop
  exact (isOpen_lt continuous_const htime).inter
    ((isOpen_lt htime continuous_const).inter (isOpen_domain.preimage continuous_spatialPart))

/-- The open spacetime cylinder lies in the closed one. -/
theorem spacetimeDomain_subset_closedSpacetimeDomain (T : ℝ) :
    spacetimeDomain T ⊆ closedSpacetimeDomain T :=
  fun _ hx ↦ ⟨hx.1, hx.2.1, domain_subset_closedDomain hx.2.2⟩

/-- The positive-time wall lies in the closed spacetime cylinder. -/
theorem wallSpacetime_subset_closedSpacetimeDomain (T : ℝ) :
    wallSpacetime T ⊆ closedSpacetimeDomain T :=
  fun _ hx ↦ ⟨hx.1, hx.2.1, wall_subset_closedDomain hx.2.2⟩

/-- Positive times up to the wall lie in the physical domain. -/
theorem closedSpacetimeDomain_subset_physicalDomain (T : ℝ) :
    closedSpacetimeDomain T ⊆ physicalDomain T :=
  fun _ hx ↦ ⟨hx.1.le, hx.2.1, hx.2.2⟩

/-- A slice point at a time in `(0,T)` and a point of the open cylinder lies in the open
spacetime cylinder. -/
theorem timeSpaceCons_mem_spacetimeDomain {T t : ℝ} (ht : t ∈ Set.Ioo 0 T) {x : ℝ^3}
    (hx : x ∈ domain) : timeSpaceCons t x ∈ spacetimeDomain T := by
  simpa [spacetimeDomain] using ⟨ht.1, ht.2, hx⟩

/-- The spacetime translation by `L` in the axial coordinate. -/
def axialShift (L : ℝ) : ℝ^4 :=
  L • EuclideanSpace.single (3 : Fin 4) (1 : ℝ)

/-- The axial shift moves only the axial coordinate. -/
@[simp]
theorem axialShift_apply (L : ℝ) (i : Fin 4) :
    axialShift L i = if i = 3 then L else 0 := by
  by_cases h : i = 3 <;> simp [axialShift, h]

/-- A spacetime field is `L`-periodic in the axial coordinate at every point of `S`. -/
def IsAxiallyPeriodicOn {E : Type*} (L : ℝ) (f : ℝ^4 → E) (S : Set (ℝ^4)) : Prop :=
  ∀ ⦃xt : ℝ^4⦄, xt ∈ S → f (xt + axialShift L) = f xt

/-- The normal velocity `x₀ u₀ + x₁ u₁` at a spacetime point. On the wall `{r = 1}` the
outward unit normal at `x` is `(x₀, x₁, 0)`, so this is `u · n` there. -/
def wallNormalVelocity (u : ℝ^4 → ℝ^3) (xt : ℝ^4) : ℝ :=
  xt 1 * u xt 0 + xt 2 * u xt 1

/-- A classical Euler solution on `[0,T)` in the periodic cylinder `{r ≤ 1} × ℝ/Lℤ` with the
impermeable wall `{r = 1}`.

The momentum equation of `Euler.MomentumEquationAt`, incompressibility and interior
smoothness hold on `(0,T) × {r < 1}`; the velocity is `C¹` up to the wall and has zero normal
component there; both fields are `L`-periodic in `z`; and the velocity is continuous at the
initial surface with the prescribed value on the closed cylinder. Values outside the closed
cylinder are not constrained. -/
structure SmoothSolution (L : ℝ) (data : InitialValueData 3) where
  /-- Velocity field. -/
  u : ℝ^4 → ℝ^3
  /-- Pressure field. -/
  p : ℝ^4 → ℝ
  /-- Positive finite endpoint of the time interval. -/
  T : Set.Ioi (0 : ℝ)
  /-- The axial period is positive. -/
  period_pos : 0 < L
  /-- The Euler momentum equation in the open cylinder at positive times. -/
  momentum_at : ∀ ⦃xt : ℝ^4⦄, xt ∈ spacetimeDomain T → MomentumEquationAt data u p xt
  /-- Incompressibility in the open cylinder at positive times. -/
  divergenceFreeOn : DivergenceFreeOn u (spacetimeDomain T)
  /-- Smoothness of the velocity in the open cylinder at positive times. -/
  velocity_contDiffAt : ∀ ⦃xt : ℝ^4⦄, xt ∈ spacetimeDomain T → ContDiffAt ℝ (⊤ : ℕ∞) u xt
  /-- Smoothness of the pressure in the open cylinder at positive times. -/
  pressure_contDiffAt : ∀ ⦃xt : ℝ^4⦄, xt ∈ spacetimeDomain T → ContDiffAt ℝ (⊤ : ℕ∞) p xt
  /-- The velocity is `C¹` up to the wall at positive times. -/
  velocity_contDiffOn : ContDiffOn ℝ 1 u (closedSpacetimeDomain T)
  /-- Impermeability: zero normal velocity on the wall. -/
  wallNormalVelocity_eq_zero :
    ∀ ⦃xt : ℝ^4⦄, xt ∈ wallSpacetime T → wallNormalVelocity u xt = 0
  /-- Axial periodicity of the velocity on the physical domain. -/
  velocity_periodic : IsAxiallyPeriodicOn L u (physicalDomain T)
  /-- Axial periodicity of the pressure where it is defined by the equations. -/
  pressure_periodic : IsAxiallyPeriodicOn L p (spacetimeDomain T)
  /-- One-sided continuity of the velocity at the initial surface. -/
  continuousWithinAt_initial :
    ∀ ⦃x : ℝ^3⦄, x ∈ closedDomain →
      ContinuousWithinAt u (physicalDomain T) (timeSpaceCons 0 x)
  /-- The prescribed initial velocity on the closed cylinder. -/
  initial_eq : ∀ ⦃x : ℝ^3⦄, x ∈ closedDomain → u (timeSpaceCons 0 x) = data.initialVelocity x

namespace SmoothSolution

variable {L : ℝ} {data : InitialValueData 3}

/-- The velocity tends to its datum through the physical domain. -/
theorem tendsto_initial (sol : SmoothSolution L data) {x : ℝ^3} (hx : x ∈ closedDomain) :
    Filter.Tendsto sol.u (nhdsWithin (timeSpaceCons 0 x) (physicalDomain sol.T))
      (𝓝 (data.initialVelocity x)) := by
  rw [← sol.initial_eq hx]
  exact sol.continuousWithinAt_initial hx

/-- The momentum equation holds near every point of the open spacetime cylinder. -/
theorem eventually_momentum_at (sol : SmoothSolution L data) {xt : ℝ^4}
    (hxt : xt ∈ spacetimeDomain sol.T) :
    ∀ᶠ y in 𝓝 xt, MomentumEquationAt data sol.u sol.p y := by
  filter_upwards [(isOpen_spacetimeDomain sol.T).mem_nhds hxt] with y hy
  exact sol.momentum_at hy

/-- The Euler momentum residual vanishes in the open spacetime cylinder. -/
theorem momentumResidual_eq_zero (sol : SmoothSolution L data) {xt : ℝ^4}
    (hxt : xt ∈ spacetimeDomain sol.T) :
    eulerMomentumResidual 3 sol.u sol.p data.forcing xt = 0 :=
  (eulerMomentumResidual_eq_zero_iff 3 sol.u sol.p data.forcing xt).2 (sol.momentum_at hxt)

end SmoothSolution

end

end Euler.Cylinder
