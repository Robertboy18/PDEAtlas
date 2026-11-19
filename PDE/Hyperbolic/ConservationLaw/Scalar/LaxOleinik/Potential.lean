/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Primitive.Bounded
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.InitialPotential.Equation
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.ConservationLaw.Potential

/-!
# Conservation laws from the Hopf–Lax primitive

For an arbitrary essentially bounded datum, the interval primitive is globally
Lipschitz. Evolving it by the Hopf–Lax formula and taking its
spatial derivative gives a measurable, essentially bounded conservation-law
solution. Integration by parts retains the primitive on the initial face and
recovers the supplied datum almost everywhere.

The flux here is the dual of the specified convex superlinear cost.
Prescribing the flux instead goes through `LaxOleinik.Duality`. The construction is (23)-(27) of
Evans, §3.4.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, equations (23)-(27).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Common HamiltonJacobi.HopfLax HamiltonJacobi1D
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- The totalized spatial derivative of the Hopf–Lax evolution of the
normalized interval primitive, in `(time, space)` coordinates. -/
def potentialDerivative (L g : ℝ → ℝ) (p : ℝ^2) : ℝ :=
  fderiv ℝ (forwardValue L (fun x ↦ ∫ s in (0 : ℝ)..x, g s))
    (scalarSpaceTimeEquiv p) (1, 0)

/-- The Hopf–Lax derivative is a weak initial-value solution and
is globally essentially bounded. The datum is only assumed to belong to `L∞`;
it need not be bounded at every point of its supplied representative. -/
theorem potentialDerivative_spec {L g : ℝ → ℝ} (hL : Superlinear L) (hconv : ConvexOn ℝ univ L)
    (hg : MemLp g ∞ volume) :
    IsWeakInitialValueSolution (hamiltonian L) g (potentialDerivative L g) ∧
      MemLp (potentialDerivative L g) ∞ volume := by
  obtain ⟨K, hh⟩ := exists_lipschitzWith_intervalIntegral_of_memLp_top hg 0
  obtain ⟨C, hW⟩ := exists_lipschitzWith_forwardValue hL hconv hh
  have hgLoc : LocallyIntegrable g volume := hg.locallyIntegrable (by simp)
  have htrace : ∀ᵐ x : ℝ, deriv
        (fun y ↦ forwardValue L (fun z ↦ ∫ s in (0 : ℝ)..z, g s) (y, 0)) x = g x := by
    simp only [forwardValue_zero]
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hgLoc] with x hx using (hx 0).deriv
  exact ⟨isWeakInitialValueSolution_of_lipschitz_potential hW
    (continuous_hamiltonian hL) hgLoc htrace (ae_forwardValue_residual_eq_zero hL hconv hh),
    memLp_top_spatial_fderiv_of_lipschitz hW⟩

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
