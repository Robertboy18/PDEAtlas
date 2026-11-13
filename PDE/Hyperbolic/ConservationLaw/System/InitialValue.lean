/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.InitialValue
public import PDE.Hyperbolic.ConservationLaw.Riemann.Data
public import PDE.Hyperbolic.ConservationLaw.System.Weak

/-!
# Initial-value problems for one-dimensional conservation-law systems

We specialize the initial-boundary weak formulation to

`u_t + (f(u))_x = 0`.

The formulation is the Bochner identity
`PDE.Hyperbolic.ConservationLaw.IsWeakInitialValueSolution`, which implies
the interior weak equation for the system. In a Euclidean state space it is the identity (13)
of Evans, §11.1.1, which Evans uses to define integral solutions of systems.

For vector-valued states, the shared trace predicate from
the scalar initial-trace theory measures the error by the Euclidean norm:

`∫_[a,b] ‖u(t, x) - u₀(x)‖ dx → 0` as `t ↓ 0`.

The solution predicate is the conjunction of the interior weak equation and
this trace property. The dominated-convergence criterion for traces applies
unchanged.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equations (12)-(13) and the definition of
  integral solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Hyperbolic.ConservationLaw.Scalar

variable {m : ℕ}

/-! ## Direct initial-boundary formulation -/

/-- A direct system weak solution, including the initial-boundary term, is an
interior weak solution on `t > 0`. -/
theorem IsWeakInitialValueSolution.interior {flux : ℝ^m → ℝ^m} {u₀ : ℝ → ℝ^m} {u : ℝ^2 → ℝ^m}
    (hu : IsWeakInitialValueSolution flux u₀ u) :
    IsWeakSolution flux forwardHalfSpace u := by
  exact
    { u_locallyIntegrable := hu.u_locallyIntegrable
      flux_locallyIntegrable := hu.flux_locallyIntegrable
      weak_eq := by
        intro φ
        simpa [weakIntegrand, PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integrand] using
          hu.interior_identity φ }

/-! ## Strong traces -/

/-- An interior weak system solution that attains its prescribed initial
state strongly in local `L¹`. -/
def IsWeakSolutionWithInitialTrace
    (flux : ℝ^m → ℝ^m) (u₀ : ℝ → ℝ^m)
    (u : ℝ^2 → ℝ^m) : Prop :=
  IsWeakSolution flux forwardHalfSpace u ∧
    HasInitialTraceLocallyL1 u u₀

/-- The interior distributional solution carried by a system solution with
initial trace. -/
theorem IsWeakSolutionWithInitialTrace.interior {flux : ℝ^m → ℝ^m} {u₀ : ℝ → ℝ^m} {u : ℝ^2 → ℝ^m}
    (hu : IsWeakSolutionWithInitialTrace flux u₀ u) :
    IsWeakSolution flux forwardHalfSpace u :=
  hu.1

/-- Strong local `L¹` attainment of the prescribed vector-valued initial
state. -/
theorem IsWeakSolutionWithInitialTrace.initialTrace {flux : ℝ^m → ℝ^m} {u₀ : ℝ → ℝ^m}
    {u : ℝ^2 → ℝ^m} (hu : IsWeakSolutionWithInitialTrace flux u₀ u) :
    HasInitialTraceLocallyL1 u u₀ :=
  hu.2

end PDE.Hyperbolic.ConservationLaw.System
