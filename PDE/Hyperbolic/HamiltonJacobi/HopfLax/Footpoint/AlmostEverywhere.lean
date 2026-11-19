/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Footpoint.Derivative
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.InitialPotential.Derivative
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Minimizing footpoints and almost-everywhere derivatives

Compact attainment supplies a minimizing footpoint at every positive time.
The fixed-footpoint comparison identifies every such minimizer with the
spatial derivative almost everywhere on each fixed time slice. The joint
almost-everywhere theorem applies Rademacher to the continued potential
instead of combining the slice statements.

In the notation of Evans, §3.4.2, `minimizingFootpoint L h t x` is a minimizer `y(x, t)` in the
formula (24) for `w` (Evans takes the smallest one), and the almost-everywhere identity is
`w_x = L'((x - y(x, t))/t)` from step 4 of the proof of Theorem 1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, equation (24), Theorem 1 and steps 3-4
  of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped NNReal

namespace HamiltonJacobi.HopfLax

/-- Choose a minimizing footpoint whenever one exists. The default
outside the attained regime is irrelevant to the positive-time theorems. -/
def minimizingFootpoint (L h : ℝ → ℝ) (t x : ℝ) : ℝ := by
  classical
  exact if hex : ∃ y, value L h t x = h y + t * L ((x - y) / t)
    then hex.choose else x

/-- Continuous superlinear costs and Lipschitz primitives make the chosen
footpoint a minimizer for every positive time and every endpoint. -/
theorem minimizingFootpoint_spec {L h : ℝ → ℝ} (hcont : Continuous L) (hL : Superlinear L) {K : ℝ≥0}
    (hh : LipschitzWith K h) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    value L h t x = h (minimizingFootpoint L h t x) +
      t * L ((x - minimizingFootpoint L h t x) / t) := by
  have hex := exists_value_eq_fixed_footpoint hcont hL hh ht x
  simpa only [minimizingFootpoint, dite_eq_left hex] using hex.choose_spec

/-- On each fixed positive time slice, every minimizing footpoint gives the
spatial derivative almost everywhere. The exceptional set is allowed
to depend on time. -/
theorem ae_deriv_value_eq_deriv_cost_of_fixed_footpoint {L h : ℝ → ℝ} (hL : Superlinear L)
    (hD : Differentiable ℝ L) {K : ℝ≥0} (hh : LipschitzWith K h) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x : ℝ, ∀ y, value L h t x = h y + t * L ((x - y) / t) →
      deriv (value L h t) x = deriv L ((x - y) / t) := by
  filter_upwards [(lipschitzWith_value hL hh ht.le).ae_differentiableAt] with x hx
  exact fun y hy ↦ deriv_value_eq_deriv_cost_of_fixed_footpoint hL hh ht hy hx (hD _)

/-- Joint differentiability identifies every minimizing footpoint with the
spatial component of the continued potential's derivative. -/
theorem spatial_fderiv_eq_deriv_cost_of_fixed_footpoint {L h : ℝ → ℝ} (hL : Superlinear L)
    (hD : Differentiable ℝ L) {K : ℝ≥0} (hh : LipschitzWith K h) {p : ℝ × ℝ} (ht : 0 < p.2)
    (hd : DifferentiableAt ℝ (forwardValue L h) p) {y : ℝ}
    (hy : value L h p.2 p.1 = h y + p.2 * L ((p.1 - y) / p.2)) :
    fderiv ℝ (forwardValue L h) p (1, 0) = deriv L ((p.1 - y) / p.2) := by
  have hs := hasDerivAt_value_of_differentiableAt_forwardValue hd
  rw [max_eq_left ht.le] at hs
  rw [← hs.deriv]
  exact deriv_value_eq_deriv_cost_of_fixed_footpoint hL hh ht hy hs.differentiableAt (hD _)

/-- The footpoint identity holds jointly almost everywhere in spacetime.
This statement comes from joint Rademacher differentiability in spacetime. -/
theorem ae_spatial_fderiv_eq_deriv_cost_of_fixed_footpoint {L h : ℝ → ℝ} (hL : Superlinear L)
    (hconv : ConvexOn ℝ univ L) (hD : Differentiable ℝ L) {K : ℝ≥0} (hh : LipschitzWith K h) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.2 → ∀ y, value L h p.2 p.1 = h y + p.2 * L ((p.1 - y) / p.2) →
      fderiv ℝ (forwardValue L h) p (1, 0) = deriv L ((p.1 - y) / p.2) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_forwardValue hL hconv hh
  have hd := hC.ae_differentiableAt (μ := volume.prod volume)
  rw [Measure.volume_eq_prod]
  filter_upwards [hd] with p hp
  exact fun ht y hy ↦ spatial_fderiv_eq_deriv_cost_of_fixed_footpoint hL hD hh ht hp hy

end HamiltonJacobi.HopfLax
