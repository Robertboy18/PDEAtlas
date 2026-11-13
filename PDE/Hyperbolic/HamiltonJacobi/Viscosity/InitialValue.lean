/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Basic

/-!
# Initial data and slab regularity for Hamilton–Jacobi equations

The spacetime convention is `(x, t) : E × ℝ`. Initial-value solutions are
bounded and uniformly continuous on each finite closed time slab, satisfy
the touching-test equation for positive time, and attain their initial data.
The Hamiltonian in these definitions may depend on position. The comparison
theorem in `InitialComparison` is restricted to autonomous Hamiltonians;
`SpatialInitialComparison` treats position-dependent ones.

The touching tests are locally `C¹` at their contact points. Apart from the test class, this is
the definition of viscosity solution of the initial-value problem in Evans, §10.1.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.1.1, definition of viscosity solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The open forward spacetime half-space. -/
def positiveTimeDomain : Set (E × ℝ) := {z | 0 < z.2}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Positive time is an open condition in space × time. -/
theorem isOpen_positiveTimeDomain : IsOpen (positiveTimeDomain (E := E)) :=
  isOpen_lt continuous_const continuous_snd

open scoped Topology

/-- The closed forward spacetime slab `0 ≤ t ≤ T`. -/
def closedTimeSlab (T : ℝ) : Set (E × ℝ) :=
  {z | 0 ≤ z.2 ∧ z.2 ≤ T}

/-- Boundedness and uniform continuity on every finite positive-time slab. -/
def IsBoundedUniformContinuousOnSlabs (u : (E × ℝ) → ℝ) : Prop :=
  ∀ T, 0 < T →
    Bornology.IsBounded (u '' closedTimeSlab T) ∧
      UniformContinuousOn u (closedTimeSlab T)

/-- A viscosity subsolution of `u_t + H(Dₓu, x) = 0` satisfying the upper
initial condition `u(x, 0) ≤ g(x)`. -/
def IsViscosityInitialSubsolution
    (H : E → E → ℝ) (g : E → ℝ) (u : (E × ℝ) → ℝ) : Prop :=
  IsBoundedUniformContinuousOnSlabs u ∧
    IsSpatialViscositySubsolution H positiveTimeDomain u ∧
      ∀ x, u (x, 0) ≤ g x

/-- A viscosity supersolution of `u_t + H(Dₓu, x) = 0` satisfying the lower
initial condition `g(x) ≤ u(x, 0)`. -/
def IsViscosityInitialSupersolution
    (H : E → E → ℝ) (g : E → ℝ) (u : (E × ℝ) → ℝ) : Prop :=
  IsBoundedUniformContinuousOnSlabs u ∧
    IsSpatialViscositySupersolution H positiveTimeDomain u ∧
      ∀ x, g x ≤ u (x, 0)

/-- The bounded, uniformly continuous solution class for the initial-value
problem, with locally `C¹` touching tests.

The candidate is bounded and uniformly continuous on every slab
`E × [0, T]`, satisfies the viscosity equation on `t > 0`, and agrees
pointwise with the initial datum at `t = 0`. -/
def IsViscosityInitialSolution
    (H : E → E → ℝ) (g : E → ℝ) (u : (E × ℝ) → ℝ) : Prop :=
  IsBoundedUniformContinuousOnSlabs u ∧
    IsSpatialViscositySolution H positiveTimeDomain u ∧
      ∀ x, u (x, 0) = g x

/-- A viscosity solution of the initial-value problem is, in particular, a
subsolution with the corresponding upper initial trace. -/
theorem IsViscosityInitialSolution.subsolution {H : E → E → ℝ} {g : E → ℝ} {u : (E × ℝ) → ℝ}
    (hu : IsViscosityInitialSolution H g u) :
    IsViscosityInitialSubsolution H g u :=
  ⟨hu.1, hu.2.1.1, fun x ↦ (hu.2.2 x).le⟩

/-- A viscosity solution of the initial-value problem is, in particular, a
supersolution with the corresponding lower initial trace. -/
theorem IsViscosityInitialSolution.supersolution {H : E → E → ℝ} {g : E → ℝ} {u : (E × ℝ) → ℝ}
    (hu : IsViscosityInitialSolution H g u) :
    IsViscosityInitialSupersolution H g u :=
  ⟨hu.1, hu.2.1.2, fun x ↦ (hu.2.2 x).ge⟩

/-- A viscosity solution of the initial-value problem attains its prescribed
initial datum pointwise. -/
theorem IsViscosityInitialSolution.initial_eq {H : E → E → ℝ} {g : E → ℝ} {u : (E × ℝ) → ℝ}
    (hu : IsViscosityInitialSolution H g u) (x : E) :
    u (x, 0) = g x :=
  hu.2.2 x

/-- The full IVP solution notion is exactly the conjunction of its
comparison-compatible subsolution and supersolution notions. -/
theorem isViscosityInitialSolution_iff_sub_and_super {H : E → E → ℝ} {g : E → ℝ} {u : (E × ℝ) → ℝ} :
    IsViscosityInitialSolution H g u ↔ IsViscosityInitialSubsolution H g u ∧
      IsViscosityInitialSupersolution H g u := by
  constructor
  · exact fun hu ↦ ⟨hu.subsolution, hu.supersolution⟩
  · rintro ⟨⟨hBUC, hsub, hsubtrace⟩, ⟨_hBUC', hsuper, hsupertrace⟩⟩
    exact ⟨hBUC, ⟨hsub, hsuper⟩, fun x ↦ le_antisymm (hsubtrace x) (hsupertrace x)⟩

end

end HamiltonJacobi
