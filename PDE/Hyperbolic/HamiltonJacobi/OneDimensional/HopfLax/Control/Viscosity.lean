/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Control
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.InitialValue

/-!
# Viscosity theory for autonomous control values

Evans, §10.3.3, Theorem 2, proves directly that a control value function is a viscosity solution
of the Hamilton–Jacobi–Bellman equation. We take a shorter route for this autonomous problem: on
positive time the control value is exactly the Hopf–Lax formula, so the Hopf–Lax continuity and
viscosity theorems transfer directly to it.

The results are stated for the value function itself.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Theorem 2; §10.3.4, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi1D

noncomputable section

open PDE.Common

set_option linter.missingDocs true

/-- The spacetime value function of the autonomous control problem. -/
def controlValueSpacetime (H phi : ℝ → ℝ) : ℝ^2 → ℝ :=
  fun z ↦ HopfLax1D.controlValue H phi (z 0) (z 1)

/-- The closed-time control evolution.

This is the spacetime specialization of
`HopfLax1D.controlValueEvolution`. -/
def controlValueEvolutionSpacetime (H phi : ℝ → ℝ) : ℝ^2 → ℝ :=
  fun z ↦ HopfLax1D.controlValueEvolution H phi (z 0) (z 1)

/-- On positive time, the Hopf–Lax and autonomous control spacetime profiles
agree for Lipschitz initial data. -/
theorem hopfLaxSpacetime_eq_controlValueSpacetime_of_lipschitz {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) :
    Set.EqOn (hopfLaxSpacetime H phi) (controlValueSpacetime H phi) positiveTimeDomain :=
  fun z hz ↦ HopfLax1D.hopfLax_eq_controlValue_of_lipschitz hFin hphi (show 0 < z 0 from hz)

/-- For Lipschitz initial data, the closed-time control evolution is exactly
the canonical Hopf–Lax evolution. -/
theorem controlValueEvolutionSpacetime_eq_hopfLaxEvolutionSpacetime_of_lipschitz {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) :
    controlValueEvolutionSpacetime H phi = hopfLaxEvolutionSpacetime H phi :=
  funext fun _ ↦ HopfLax1D.controlValueEvolution_eq_hopfLaxEvolution_of_lipschitz hFin hphi _ _

/-- The closed-time control evolution has the prescribed time-zero trace. -/
@[simp]
theorem controlValueEvolutionSpacetime_zero (H phi : ℝ → ℝ) (x : ℝ) :
    controlValueEvolutionSpacetime H phi !₂[0, x] = phi x := by
  simp [controlValueEvolutionSpacetime]

/-- The autonomous control value is continuous on positive time for Lipschitz
initial data. -/
theorem controlValueSpacetime_continuousOn_of_lipschitz {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) :
    ContinuousOn (controlValueSpacetime H phi) positiveTimeDomain :=
  (hopfLaxSpacetime_continuousOn_of_lipschitz hFin hphi).congr fun _ hz ↦
    (hopfLaxSpacetime_eq_controlValueSpacetime_of_lipschitz hFin hphi hz).symm

/-- The autonomous control value is a continuous viscosity solution for the
biconjugate Hamiltonian on positive time. -/
theorem controlValueSpacetime_isContinuousDifferentiableTestSolution_biconjugate_of_lipschitz
    {H phi : ℝ → ℝ} (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) :
    IsContinuousDifferentiableTestSolution (HopfLax1D.legendreTransform
      (HopfLax1D.legendreTransform H)) positiveTimeDomain (controlValueSpacetime H phi) :=
  ⟨controlValueSpacetime_continuousOn_of_lipschitz hFin hphi,
    ((isAmbientDifferentiableTestSolution_congr_of_eqOn isOpen_positiveTimeDomain
      (hopfLaxSpacetime_eq_controlValueSpacetime_of_lipschitz hFin hphi)).1
      (hopfLaxSpacetime_isAmbientDifferentiableTestSolution_biconjugate_of_lipschitz hFin
        hphi)).toSpatial isOpen_positiveTimeDomain⟩

/-- For a convex differentiable Hamiltonian, the autonomous control value is
a continuous viscosity solution of the original Hamilton–Jacobi equation on
positive time. -/
theorem controlValueSpacetime_isContinuousDifferentiableTestSolution_of_lipschitz_convex
    {H phi : ℝ → ℝ} (hFin : HopfLax1D.LegendreFinite H) (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H)
    (hH : Differentiable ℝ H) {K : NNReal} (hphi : LipschitzWith K phi) :
    IsContinuousDifferentiableTestSolution H positiveTimeDomain (controlValueSpacetime H phi) :=
  ⟨controlValueSpacetime_continuousOn_of_lipschitz hFin hphi,
    ((isAmbientDifferentiableTestSolution_congr_of_eqOn isOpen_positiveTimeDomain
      (hopfLaxSpacetime_eq_controlValueSpacetime_of_lipschitz hFin hphi)).1
      (hopfLaxSpacetime_isAmbientDifferentiableTestSolution_of_lipschitz_convex hFin hconv hH
        hphi)).toSpatial isOpen_positiveTimeDomain⟩

/-- Bounded Lipschitz data make the closed-time autonomous control value a
viscosity solution of the complete Hamilton–Jacobi initial-value
problem. -/
theorem controlValueEvolutionSpacetime_isDifferentiableTestInitialSolution {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H)
    (hH : Differentiable ℝ H) {K : NNReal} (hphi : LipschitzWith K phi) {C : ℝ}
    (hphiBound : ∀ x, |phi x| ≤ C) :
    IsDifferentiableTestInitialSolution
      (fun p _x ↦ H p) phi (controlValueEvolutionSpacetime H phi) := by
  rw [controlValueEvolutionSpacetime_eq_hopfLaxEvolutionSpacetime_of_lipschitz hFin hphi]
  exact hopfLaxEvolutionSpacetime_isDifferentiableTestInitialSolution hFin hconv hH hphi hphiBound

end

end HamiltonJacobi1D
