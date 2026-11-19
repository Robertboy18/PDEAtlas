/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.InitialValue
public import PDE.Hyperbolic.ConservationLaw.System.WeakSolution.Classical.Equivalence
public import PDE.Hyperbolic.ConservationLaw.System.WeakSolution.Classical.InitialTrace

/-!
# Classical and weak Cauchy problems for conservation-law systems

For a C¹ flux and a field that is C¹ on `t > 0` and continuous on `t ≥ 0`,
the full initial-boundary weak formulation is equivalent to the classical
equation for positive time and attainment of the initial datum almost everywhere.
For continuous initial data, attainment is pointwise.

The integral formulation includes the initial term with its positive sign:
`∫_{t > 0} (φ_t • u + φ_x • f(u)) + ∫ φ(0,x) • g(x) = 0`.
Tests are globally C¹ and compactly supported, and may cross time zero.
All spacetime integrability requirements follow from continuity up to the
initial face; only local integrability of `g` is needed for the raw identity.
The PDE itself is asserted only at positive times.

The identity is (13) of Evans, §11.1.1, the definition of an integral solution. Evans pairs the
system with smooth `ℝᵐ`-valued tests (12) supported in `ℝ × [0, ∞)`; we use scalar `C¹` tests and
a vector-valued integral. Evans derives (13) for smooth solutions by integration by parts; we
prove both directions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equations (12)-(13) and the definition of an
  integral solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Distributions

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ} {flux : ℝ^m → ℝ^m} {u : ℝ^2 → ℝ^m} {g : ℝ → ℝ^m}

/-- A C¹ interior field continuous up to time zero satisfies the full weak
Cauchy problem exactly when it solves the classical interior equation and
its initial slice equals the prescribed datum almost everywhere. -/
theorem isWeakInitialValueSolution_iff_classical_and_initial_ae (hflux : ContDiff ℝ 1 flux)
    (hu : ContDiffOn ℝ 1 u forwardHalfSpace) (hboundary : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0}) :
    IsWeakInitialValueSolution flux g u ↔ IsClassicalSolutionOn flux forwardHalfSpace u ∧
      (fun x ↦ u !₂[0, x]) =ᵐ[volume] g := by
  constructor
  · exact fun hweak ↦ ⟨(isWeakSolution_iff_isClassicalSolutionOn hflux hu).mp
        (IsWeakInitialValueSolution.interior hweak),
      (hweak.initial_ae_eq_slice hflux.continuous hboundary).symm⟩
  · rintro ⟨hclassical, hinitial⟩
    exact isWeakInitialValueSolution_of_interior_of_initialTrace
      (locallyIntegrable_restrict_forwardHalfSpace_of_continuousOn hboundary)
      (locallyIntegrable_restrict_forwardHalfSpace_of_continuousOn
        (hflux.continuous.comp_continuousOn hboundary))
      ((Scalar.hasInitialTraceLocallyL1_of_continuousOn hboundary).congr_initial_ae hinitial)
      ((isWeakSolution_iff_isClassicalSolutionOn hflux hu).mpr hclassical).weak_eq

/-- With continuous initial data, the full weak Cauchy problem is equivalent
to the classical PDE for positive time and the pointwise initial condition. -/
theorem isWeakInitialValueSolution_iff_classical_and_initial
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiffOn ℝ 1 u forwardHalfSpace)
    (hboundary : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0}) (hg : Continuous g) :
    IsWeakInitialValueSolution flux g u ↔
      IsClassicalSolutionOn flux forwardHalfSpace u ∧ ∀ x, u !₂[0, x] = g x := by
  rw [isWeakInitialValueSolution_iff_classical_and_initial_ae hflux hu hboundary]
  have hslice : Continuous (fun x : ℝ ↦ u !₂[0, x]) :=
    hboundary.comp_continuous (by fun_prop) (fun x ↦ by simp)
  exact and_congr_right fun _ ↦ ⟨fun h ↦ congrFun (Measure.eq_of_ae_eq h hslice hg),
      fun h ↦ Filter.Eventually.of_forall h⟩

/-- Boundary continuity supplies the integrability clauses of the weak
predicate. For locally integrable initial data, only the full test identity
remains to be checked. -/
theorem isWeakInitialValueSolution_iff_integral_weakIntegrand_initial (hflux : Continuous flux)
    (hu : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0}) (hg : LocallyIntegrable g volume) :
    IsWeakInitialValueSolution flux g u ↔ ∀ φ : InitialValueTestFunction,
      (∫ p in forwardHalfSpace, weakIntegrand flux u φ p) + ∫ x, φ !₂[0, x] • g x = 0 := by
  constructor
  · exact fun hweak ↦ hweak.weak_initial_eq
  · intro hweak
    have hui := locallyIntegrable_restrict_forwardHalfSpace_of_continuousOn hu
    have hfi := locallyIntegrable_restrict_forwardHalfSpace_of_continuousOn
      (hflux.comp_continuousOn hu)
    exact
      { u_locallyIntegrable := locallyIntegrableOn_of_locallyIntegrable_restrict hui
        flux_locallyIntegrable := locallyIntegrableOn_of_locallyIntegrable_restrict hfi
        initial_locallyIntegrable := hg
        spacetime_integrable := integrableOn_initialWeakIntegrand hui hfi
        weak_initial_eq := hweak }

/-- The full integral identity is equivalent to the classical Cauchy problem
with almost-everywhere initial equality for locally integrable data. -/
theorem classical_and_initial_ae_iff_integral_weakIntegrand_initial (hflux : ContDiff ℝ 1 flux)
    (hu : ContDiffOn ℝ 1 u forwardHalfSpace) (hboundary : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0})
    (hg : LocallyIntegrable g volume) :
    (IsClassicalSolutionOn flux forwardHalfSpace u ∧ (fun x ↦ u !₂[0, x]) =ᵐ[volume] g) ↔ ∀ φ :
      InitialValueTestFunction, (∫ p in forwardHalfSpace, weakIntegrand flux u φ p) + ∫ x,
      φ !₂[0, x] • g x = 0 := by
  rw [← isWeakInitialValueSolution_iff_classical_and_initial_ae hflux hu hboundary,
    isWeakInitialValueSolution_iff_integral_weakIntegrand_initial hflux.continuous hboundary hg]

/-- For continuous initial data, the initial-boundary test identity
is equivalent to the pointwise classical Cauchy problem. -/
theorem classical_and_initial_iff_integral_weakIntegrand_initial
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiffOn ℝ 1 u forwardHalfSpace)
    (hboundary : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0}) (hg : Continuous g) :
    (IsClassicalSolutionOn flux forwardHalfSpace u ∧ ∀ x, u !₂[0, x] = g x) ↔ ∀ φ :
      InitialValueTestFunction, (∫ p in forwardHalfSpace, weakIntegrand flux u φ p) + ∫ x,
      φ !₂[0, x] • g x = 0 := by
  rw [← isWeakInitialValueSolution_iff_classical_and_initial hflux hu hboundary hg,
    isWeakInitialValueSolution_iff_integral_weakIntegrand_initial
      hflux.continuous hboundary hg.locallyIntegrable]

end PDE.Hyperbolic.ConservationLaw.System
