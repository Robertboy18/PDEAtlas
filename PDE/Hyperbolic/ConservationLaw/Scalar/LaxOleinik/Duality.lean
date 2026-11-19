/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Potential
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.ScalarCompatibility

/-!
# Prescribing the flux in the Hopf–Lax construction

The scalar conjugate is `HopfLax1D.legendreTransform`. Its biconjugacy
theorem identifies the Hamiltonian of the evolved cost with the prescribed
differentiable convex flux. This needs only finiteness of the conjugate. In Evans, §3.4.2, the
cost is `L = F*`, equation (25).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, equation (25).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set HamiltonJacobi.HopfLax
open scoped ENNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- The potential derivative for a prescribed scalar flux, using its
Legendre transform as the cost. -/
def derivativeSolution (F g : ℝ → ℝ) : ℝ^2 → ℝ :=
  potentialDerivative (HopfLax1D.legendreTransform F) g

/-- The generic Hamiltonian of the scalar conjugate is exactly the prescribed
differentiable convex flux. -/
theorem hamiltonian_legendreTransform_eq {F : ℝ → ℝ} (hFin : HopfLax1D.LegendreFinite F)
    (hconv : ConvexOn ℝ univ F) (hF : Differentiable ℝ F) :
    hamiltonian (HopfLax1D.legendreTransform F) = F := by
  funext p
  simpa only [hamiltonian, HopfLax1D.legendreTransform, real_inner_comm,
    RCLike.inner_apply, conj_trivial] using
    HopfLax1D.biconjugate_eq_of_convex_of_differentiable hFin hconv hF p

/-- A differentiable convex flux with finite conjugate admits the
Hopf–Lax weak initial solution for every essentially bounded datum. -/
theorem derivativeSolution_spec {F g : ℝ → ℝ} (hFin : HopfLax1D.LegendreFinite F)
    (hconv : ConvexOn ℝ univ F) (hF : Differentiable ℝ F) (hg : MemLp g ∞ volume) :
    IsWeakInitialValueSolution F g (derivativeSolution F g) ∧
      MemLp (derivativeSolution F g) ∞ volume := by
  have h := potentialDerivative_spec (superlinear_scalar_legendre hFin)
    (HopfLax1D.convexOn_legendreTransform hFin) hg
  simpa only [hamiltonian_legendreTransform_eq hFin hconv hF, derivativeSolution] using h

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
