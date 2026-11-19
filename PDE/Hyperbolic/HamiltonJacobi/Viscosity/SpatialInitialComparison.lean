/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.FiniteHorizon.Spatial

/-!
# Global initial-value comparison for position-dependent Hamiltonians

Global-time comparison follows from finite-horizon comparison, one slab
at a time. The doubled-variable argument, with an
arbitrary terminal horizon, is in `FiniteHorizon.Spatial`. The bounds are condition (3) of
Evans, §10.2, with separate constants, and the uniqueness statement is his Theorem 1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, condition (3) and Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi

noncomputable section

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Initial ordering propagates for a position-dependent Hamiltonian with
uniform momentum Lipschitz control and spatial variation bounded by
`Cx * ‖x-y‖ * (1+‖p‖)`. Both candidates use local `C¹` tests and are bounded
and uniformly continuous on finite closed time slabs. -/
theorem IsSpatialViscositySubsolution.le_of_initial_le_of_lipschitz {H : E → E → ℝ}
    {u v : E × ℝ → ℝ} {Cp Cx : NNReal} (hu : IsSpatialViscositySubsolution H positiveTimeDomain u)
    (hv : IsSpatialViscositySupersolution H positiveTimeDomain v)
    (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖))
    (hub : IsBoundedUniformContinuousOnSlabs u) (hvb : IsBoundedUniformContinuousOnSlabs v)
    (hinit : ∀ x : E, u (x, 0) ≤ v (x, 0)) {z₀ : E × ℝ} (hz₀ : 0 ≤ z₀.2) :
    u z₀ ≤ v z₀ := by
  have hT : 0 < z₀.2 + 1 := by linarith only [hz₀]
  exact hu.le_of_initial_le_on_slab_of_lipschitz hv
    (fun _ hz ↦ hz.1) (fun _ hz ↦ hz.1) hp hx (hub _ hT) (hvb _ hT)
    hinit hT ⟨hz₀, by linarith only []⟩

/-- Ordered initial data give ordered forward-time IVP candidates under the
momentum and spatial Lipschitz bounds. The initial inequalities may be strict;
equality with the data is not required for this subsolution–supersolution result. -/
theorem IsViscosityInitialSubsolution.le_of_lipschitz {H : E → E → ℝ} {g h : E → ℝ}
    {u v : E × ℝ → ℝ} {Cp Cx : NNReal} (hu : IsViscosityInitialSubsolution H g u)
    (hv : IsViscosityInitialSupersolution H h v) (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖)) (hgh : ∀ x, g x ≤ h x) {z : E × ℝ}
    (hz : 0 ≤ z.2) :
    u z ≤ v z := by
  apply hu.2.1.le_of_initial_le_of_lipschitz hv.2.1 hp hx hu.1 hv.1 ?_ hz
  intro x
  exact (hu.2.2 x).trans ((hgh x).trans (hv.2.2 x))

/-- Uniqueness on the forward half-space for position-dependent IVP solutions
with the same initial data. The solution predicate uses local `C¹`
touching tests and bounded uniform continuity on every finite time slab. -/
theorem IsViscosityInitialSolution.eqOn_of_initial_eq_of_lipschitz {H : E → E → ℝ} {g : E → ℝ}
    {u v : E × ℝ → ℝ} {Cp Cx : NNReal} (hu : IsViscosityInitialSolution H g u)
    (hv : IsViscosityInitialSolution H g v) (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖)) :
    EqOn u v {z : E × ℝ | 0 ≤ z.2} := by
  intro z hz
  exact le_antisymm (hu.subsolution.le_of_lipschitz hv.supersolution hp hx (fun _ ↦ le_rfl) hz)
    (hv.subsolution.le_of_lipschitz hu.supersolution hp hx (fun _ ↦ le_rfl) hz)

end

end HamiltonJacobi
