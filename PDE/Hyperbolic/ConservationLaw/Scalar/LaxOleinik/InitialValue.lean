/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Duality
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Footpoint
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Legendre.Derivative

/-!
# The prescribed-flux Lax–Oleinik initial solution

The solution uses the Legendre conjugate, the integral primitive, and an
attained minimizing footpoint. Continuous inversion of the flux derivative
identifies the formula, and the Hopf–Lax potential supplies the weak initial
identity and measurability. Inversion is a hypothesis here;
`LaxOleinik.UniformlyConvex` derives it from a positive second-derivative bound.
The formula is (29) of Evans, §3.4.2, with `G = (F')⁻¹` as in (28).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, equations (28)-(29) and Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- The Lax–Oleinik solution for a prescribed scalar flux, extended by
zero outside positive time. -/
def solution (F g : ℝ → ℝ) : ℝ^2 → ℝ :=
  costSolution (HopfLax1D.legendreTransform F) g

/-- At every positive time and spatial point the construction has the
inverse-derivative footpoint formula. The footpoint comes from the
variational value. -/
theorem solution_eq_inverse_footpoint {F G g : ℝ → ℝ} (hconv : ConvexOn ℝ univ F)
    (hF : Differentiable ℝ F) (hG : Function.RightInverse G (deriv F)) (hcont : Continuous G)
    {p : ℝ^2} (ht : 0 < p 0) :
    solution F g p = G ((p 1 - minimizingFootpoint (HopfLax1D.legendreTransform F)
      (fun x ↦ ∫ s in (0 : ℝ)..x, g s) (p 0) (p 1)) / p 0) := by
  simp only [solution, costSolution, ite_eq_left ht]
  exact (HopfLax1D.hasDerivAt_legendreTransform_of_continuous_rightInverse
    hconv hF hG hcont.continuousAt).deriv

/-- Continuous inversion of the derivative of a convex flux gives the full
weak initial solution for arbitrary `L∞` data. Finiteness of the
conjugate, attainment, measurability, and the initial identity are derived. -/
theorem solution_spec_of_continuous_rightInverse {F G g : ℝ → ℝ} (hconv : ConvexOn ℝ univ F)
    (hF : Differentiable ℝ F) (hG : Function.RightInverse G (deriv F)) (hcont : Continuous G)
    (hg : MemLp g ∞ volume) :
    IsWeakInitialValueSolution F g (solution F g) ∧ MemLp (solution F g) ∞ volume := by
  have hFin := HopfLax1D.legendreFinite_of_surjective_deriv hconv hF hG.surjective
  have hD : Differentiable ℝ (HopfLax1D.legendreTransform F) := fun v ↦
    (HopfLax1D.hasDerivAt_legendreTransform_of_continuous_rightInverse
      hconv hF hG (hcont.continuousAt (x := v))).differentiableAt
  have h := costSolution_spec (superlinear_scalar_legendre hFin)
    (HopfLax1D.convexOn_legendreTransform hFin) hD hg
  simpa only [hamiltonian_legendreTransform_eq hFin hconv hF, solution] using h

/-- The prescribed-flux footpoint solution preserves every essential bound
on the datum, including the zero bound. -/
theorem ae_norm_solution_le_of_continuous_rightInverse {F G g : ℝ → ℝ} (hconv : ConvexOn ℝ univ F)
    (hF : Differentiable ℝ F) (hG : Function.RightInverse G (deriv F)) (hcont : Continuous G)
    (hg : MemLp g ∞ volume) {K : ℝ≥0} (hK : ∀ᵐ x : ℝ, ‖g x‖ ≤ K) :
    ∀ᵐ p : ℝ^2, ‖solution F g p‖ ≤ K := by
  have hFin := HopfLax1D.legendreFinite_of_surjective_deriv hconv hF hG.surjective
  exact ae_norm_costSolution_le (superlinear_scalar_legendre hFin)
    (HopfLax1D.convexOn_legendreTransform hFin)
    (fun v ↦ (HopfLax1D.hasDerivAt_legendreTransform_of_continuous_rightInverse
      hconv hF hG (hcont.continuousAt (x := v))).differentiableAt) hg hK

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
