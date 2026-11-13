/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.FiniteHorizon.Autonomous

/-!
# Global initial-value comparison for an autonomous Hamiltonian

Finite-horizon comparison gives forward-time initial-value comparison,
using one slab for each target point. The doubled-variable proof is in `FiniteHorizon.Autonomous`.
The uniqueness statement is Theorem 1 of Evans, §10.2, for an autonomous Hamiltonian that need
only be continuous; Evans assumes the Lipschitz condition (3).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, condition (3) and Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open Set

/-- Initial ordering propagates to all nonnegative times for a continuous
autonomous Hamiltonian. Both candidates are bounded and uniformly continuous
on finite closed time slabs. Maximum attainment and exclusion of the initial,
terminal, and localization boundaries are derived in the proof. -/
theorem IsSpatialViscositySubsolution.le_of_initial_le {H : E → ℝ} {u v : (E × ℝ) → ℝ}
    (hu : IsSpatialViscositySubsolution (fun p _ ↦ H p) positiveTimeDomain u)
    (hv : IsSpatialViscositySupersolution (fun p _ ↦ H p) positiveTimeDomain v) (hH : Continuous H)
    (hub : IsBoundedUniformContinuousOnSlabs u) (hvb : IsBoundedUniformContinuousOnSlabs v)
    (hinit : ∀ x : E, u (x, 0) ≤ v (x, 0)) {z₀ : (E × ℝ)} (hz₀ : 0 ≤ z₀.2) :
    u z₀ ≤ v z₀ := by
  have hT : 0 < z₀.2 + 1 := by linarith only [hz₀]
  exact hu.le_of_initial_le_on_slab hv (fun _ hz ↦ hz.1) (fun _ hz ↦ hz.1)
    hH (hub _ hT) (hvb _ hT) hinit hT ⟨hz₀, by linarith only []⟩

/-- Comparison for the initial-value predicates, allowing ordered
initial data. The conclusion is restricted to nonnegative times, since
these predicates impose no condition at negative time. -/
theorem IsViscosityInitialSubsolution.le {H g h : E → ℝ} {u v : (E × ℝ) → ℝ}
    (hu : IsViscosityInitialSubsolution (fun p _ ↦ H p) g u)
    (hv : IsViscosityInitialSupersolution (fun p _ ↦ H p) h v) (hH : Continuous H)
    (hgh : ∀ x, g x ≤ h x) {z : (E × ℝ)} (hz : 0 ≤ z.2) :
    u z ≤ v z := by
  apply hu.2.1.le_of_initial_le hv.2.1 hH hu.1 hv.1 ?_ hz
  intro x
  exact (hu.2.2 x).trans ((hgh x).trans (hv.2.2 x))

/-- Uniqueness on the forward half-space for continuous autonomous
Hamiltonians and bounded, uniformly continuous IVP solutions with local
`C¹` touching tests. -/
theorem IsViscosityInitialSolution.eqOn_of_initial_eq {H g : E → ℝ} {u v : (E × ℝ) → ℝ}
    (hu : IsViscosityInitialSolution (fun p _ ↦ H p) g u)
    (hv : IsViscosityInitialSolution (fun p _ ↦ H p) g v) (hH : Continuous H) :
    EqOn u v {z : (E × ℝ) | 0 ≤ z.2} := by
  intro z hz
  exact le_antisymm (hu.subsolution.le hv.supersolution hH (fun _ ↦ le_rfl) hz)
    (hv.subsolution.le hu.supersolution hH (fun _ ↦ le_rfl) hz)

end

end HamiltonJacobi
