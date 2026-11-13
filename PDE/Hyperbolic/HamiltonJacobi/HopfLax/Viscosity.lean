/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Differentiability
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialComparison

/-!
# Multidimensional Hopf–Lax viscosity existence

The differentiable contact inequalities give the viscosity subsolution and
supersolution properties. The initial trace and spacetime estimates then
construct the viscosity initial-value solution for bounded uniformly continuous
data. Uniqueness reuses autonomous comparison.

Existence is Theorem 3 of Evans, §10.3.4, which assumes a bounded Lipschitz datum. The comparison
theorem needs only a continuous Hamiltonian, while the uniqueness theorem of §10.2 assumes the
Lipschitz conditions (3).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.4, Theorem 3; §10.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] {L g : E → ℝ}
    (hcont : Continuous L) (hL : Superlinear L)
    (hconv : ConvexOn ℝ Set.univ L) (hg : Continuous g)
    {K : NNReal} {A : ℝ} (hlower : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y)

include hcont hL hg hlower

include hconv in
/-- Dynamic programming yields the viscosity subsolution inequality for the
dual Hamiltonian, using locally `C¹` upper tests. -/
theorem isSpatialViscositySubsolution :
    IsSpatialViscositySubsolution (fun p _ ↦ hamiltonian L p)
      positiveTimeDomain (fun z : E × ℝ ↦ value L g z.2 z.1) :=
  ⟨isOpen_positiveTimeDomain, fun _ ht _ hφ hmax ↦
    residual_le_zero_of_isLocalMaxOn hcont hL hconv hg hlower ht hφ.differentiableAt_one hmax⟩

/-- An exact minimizing straight path gives the viscosity supersolution
inequality. Convexity is not needed for this direction. -/
theorem isSpatialViscositySupersolution :
    IsSpatialViscositySupersolution (fun p _ ↦ hamiltonian L p)
      positiveTimeDomain (fun z : E × ℝ ↦ value L g z.2 z.1) :=
  ⟨isOpen_positiveTimeDomain, fun _ ht _ hφ hmin ↦
    residual_nonneg_of_isLocalMinOn hcont hL hg hlower ht hφ.differentiableAt_one hmin⟩

end HamiltonJacobi.HopfLax

namespace HamiltonJacobi.HopfLax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A convex superlinear Lagrangian and bounded uniformly continuous data
give a multidimensional viscosity IVP solution for the dual Hamiltonian.

Continuity of the cost and compact attainment are derived. The value is uniformly
continuous on the forward half-space, bounded on finite slabs, and converges uniformly
in space to the datum as time decreases to zero. -/
theorem isViscosityInitialSolution {L g : E → ℝ}
    (hL : Superlinear L) (hconv : ConvexOn ℝ Set.univ L)
    (hg : UniformContinuous g) (hgb : Bornology.IsBounded (Set.range g)) :
    IsViscosityInitialSolution (fun p _ ↦ hamiltonian L p) g
      (fun z : E × ℝ ↦ value L g z.2 z.1) := by
  have hcont : Continuous L := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨M, hM⟩ := hgb.exists_norm_le
  have hlower : ∀ y, -M - ((0 : NNReal) : ℝ) * ‖y‖ ≤ g y := by
    intro y
    have hh : |g y| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM (g y) ⟨y, rfl⟩
    simpa only [NNReal.coe_zero, zero_mul, sub_zero] using (abs_le.mp hh).1
  exact ⟨boundedUniformContinuousOnSlabs hcont hL hconv hg hgb,
    ⟨isSpatialViscositySubsolution hcont hL hconv hg.continuous hlower,
      isSpatialViscositySupersolution hcont hL hg.continuous hlower⟩, value_zero L g⟩

/-- Every viscosity IVP solution for this Hamiltonian, tested by locally `C¹`
functions and bounded and uniformly continuous on each finite closed time slab,
agrees with the constructed Hopf–Lax solution at nonnegative times.
The comparison theorem itself holds for general continuous Hamiltonians. -/
theorem eqOn_value_of_isViscosityInitialSolution {L g : E → ℝ}
    (hL : Superlinear L) (hconv : ConvexOn ℝ Set.univ L)
    (hg : UniformContinuous g) (hgb : Bornology.IsBounded (Set.range g))
    {u : E × ℝ → ℝ} (hu : IsViscosityInitialSolution (fun p _ ↦ hamiltonian L p) g u) :
    Set.EqOn u (fun z : E × ℝ ↦ value L g z.2 z.1) {z | 0 ≤ z.2} :=
  hu.eqOn_of_initial_eq (isViscosityInitialSolution hL hconv hg hgb) (continuous_hamiltonian hL)

end HamiltonJacobi.HopfLax
