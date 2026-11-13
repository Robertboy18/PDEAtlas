/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Weak.Uniqueness

/-!
# The semiconcave weak initial-value problem

This is the class of weak solutions of (38) in Evans, §3.3.3(b): Lipschitz continuity on
the closed forward half-space, the initial values (a), the equation almost everywhere (b),
and spatial semiconcavity with bound `C * (1 + 1/t)` (c). Neither the solution nor the datum
needs to be bounded.

The functions are defined on all of spacetime so that Mathlib's Fréchet
derivative applies. Values at negative times are unconstrained.
The weak uniqueness theorem therefore gives equality on the forward
half-space rather than equality of these ambient functions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), definition of weak solution (38) and
  Theorem 7.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

namespace HamiltonJacobi.Weak

open MeasureTheory Set

variable {n : ℕ}

/-- A forward Lipschitz solution of the Hamilton–Jacobi initial-value problem
with Evans's spatial semiconcavity condition. The equation is imposed almost
everywhere at positive times; the initial values are imposed at every point. -/
structure IsInitialSolution (H g : ℝ^n → ℝ) (u : ℝ^n × ℝ → ℝ) : Prop where
  /-- One Lipschitz constant controls the whole closed forward half-space. -/
  lipschitz : ∃ K : NNReal, LipschitzOnWith K u {z | 0 ≤ z.2}
  /-- The prescribed continuous representative attains its initial values. -/
  initial : ∀ x, u (x, 0) = g x
  /-- The original Hamiltonian occurs in the almost-everywhere equation. -/
  equation : ∀ᵐ z ∂(volume : Measure (ℝ^n × ℝ)).restrict positiveTimeDomain,
    fderiv ℝ u z (0, 1) + H (∇ (fun x ↦ u (x, z.2)) z.1) = 0
  /-- A single positive constant gives the spatial second-difference bound. -/
  semiconcave : ∃ C : ℝ, 0 < C ∧ ∀ x z t, 0 < t →
    u (x + z, t) - 2 * u (x, t) + u (x - z, t) ≤ C * (1 + t⁻¹) * ‖z‖ ^ 2

/-- Semiconcave weak solutions with common initial values agree at every
nonnegative time. The Lipschitz and semiconcavity constants may differ. -/
theorem IsInitialSolution.eqOn [Fact (0 < n)] {H g : ℝ^n → ℝ}
    (hH : ContDiff ℝ 2 H) (hconv : ConvexOn ℝ univ H)
    {u v : ℝ^n × ℝ → ℝ} (hu : IsInitialSolution H g u) (hv : IsInitialSolution H g v) :
    EqOn u v {z | 0 ≤ z.2} := by
  obtain ⟨Ku, hKu⟩ := hu.lipschitz
  obtain ⟨Kv, hKv⟩ := hv.lipschitz
  obtain ⟨Cu, hCu, husemi⟩ := hu.semiconcave
  obtain ⟨Cv, hCv, hvsemi⟩ := hv.semiconcave
  rintro ⟨x, t⟩ ht
  exact eq_of_ae_solution_of_semiconcave_of_initial_eq hH hconv hKu hKv
    hu.equation hv.equation hCu.le hCv.le husemi hvsemi
    (fun y ↦ (hu.initial y).trans (hv.initial y).symm) x t ht

end HamiltonJacobi.Weak
