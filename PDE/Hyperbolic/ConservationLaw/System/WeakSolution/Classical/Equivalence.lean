/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Weak
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.Hyperbolic.ConservationLaw.InteriorWeakForm

/-!
# Classical and weak conservation-law systems

For a C¹ state and C¹ flux, the test-function identity
`∫ (φ_t • u + φ_x • f(u)) = 0` is equivalent to the pointwise conservation law.
The state needs C¹ regularity only on the open spacetime domain.

Integration by parts tests the continuous conservative residual against smooth
compactly supported functions. Mathlib's vector-valued fundamental lemma gives
almost-everywhere vanishing, and continuity gives vanishing at every interior
point. The predicates `IsWeakSolution` and `IsClassicalSolutionOn`
therefore agree under these regularity hypotheses.

The identity is the interior part of (13) of Evans, §11.1.1, with no initial-data term; Evans
pairs the system with smooth `ℝᵐ`-valued tests (12), and we use scalar tests.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equations (12)-(13).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ} {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m}

/-- The interior integral identity forces the conservative residual to vanish
pointwise when the state and its composed flux are C¹ on the domain. -/
theorem fluxResidual_eq_zero_of_integral_weakIntegrand_eq_zero
    (hu : ContDiffOn ℝ 1 u U) (hfluxu : ContDiffOn ℝ 1 (flux ∘ u) U)
    (hweak : ∀ φ : 𝓓^{1}(U, ℝ), ∫ p, weakIntegrand flux u φ p = 0) :
    ∀ p ∈ U, fluxResidual flux u p = 0 := by
  have hcontinuous : ContinuousOn (fluxResidual flux u) U :=
    (hu.continuousOn_partialDeriv 0 U.isOpen).add (hfluxu.continuousOn_partialDeriv 1 U.isOpen)
  have hae : ∀ᵐ p ∂volume, p ∈ U → fluxResidual flux u p = 0 := by
    apply U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hcontinuous.locallyIntegrableOn U.isOpen.measurableSet)
    intro g hg hc hs
    let φ : 𝓓^{1}(U, ℝ) := ⟨g, hg.of_le (by simp), hc, hs⟩
    have hparts : (∫ p, g p • fluxResidual flux u p) = -∫ p, weakIntegrand flux u φ p :=
      InteriorWeakForm.integral_smul_divergence_eq_neg_integrand hu hfluxu φ
    rw [hparts, hweak φ, neg_zero]
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' U.isOpen.measurableSet).mpr hae) U.isOpen
    hcontinuous continuousOn_const

/-- For C¹ data, being a classical solution is equivalent to the scalar
test-function Bochner integral identity. Local integrability follows from
regularity and is not an extra hypothesis. -/
theorem isClassicalSolutionOn_iff_integral_weakIntegrand_eq_zero
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiffOn ℝ 1 u U) :
    IsClassicalSolutionOn flux U u ↔ ∀ φ : 𝓓^{1}(U, ℝ), ∫ p, weakIntegrand flux u φ p = 0 := by
  have hfluxu : ContDiffOn ℝ 1 (flux ∘ u) U := hflux.comp_contDiffOn hu
  constructor
  · intro hclassical φ
    have hzero : (fun p ↦ φ p • fluxResidual flux u p) = 0 := by
      funext p
      by_cases hp : p ∈ U
      · simp [hclassical.residual_eq_zero p hp]
      · simp [φ.zero_on_compl hp]
    have hparts : (∫ p, φ p • fluxResidual flux u p) = -∫ p, weakIntegrand flux u φ p :=
      InteriorWeakForm.integral_smul_divergence_eq_neg_integrand hu hfluxu φ
    rw [hzero, integral_zero'] at hparts
    exact neg_eq_zero.mp hparts.symm
  · intro hweak
    exact
      { differentiableAt := fun p hp ↦
          (hu.contDiffAt (U.isOpen.mem_nhds hp)).differentiableAt one_ne_zero
        flux_differentiableAt := fun p _ ↦ hflux.differentiable_one (u p)
        residual_eq_zero := fluxResidual_eq_zero_of_integral_weakIntegrand_eq_zero hu hfluxu hweak }

/-- On any open spacetime domain, a C¹ state for a C¹ flux is weak exactly
when it is classical. In particular, the weak identity implies the PDE at
every point of the domain. -/
theorem isWeakSolution_iff_isClassicalSolutionOn
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiffOn ℝ 1 u U) :
    IsWeakSolution flux U u ↔ IsClassicalSolutionOn flux U u := by
  rw [isClassicalSolutionOn_iff_integral_weakIntegrand_eq_zero hflux hu]
  constructor
  · exact fun hweak ↦ hweak.weak_eq
  · intro hweak
    exact
      { u_locallyIntegrable := hu.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
        flux_locallyIntegrable :=
          (hflux.comp_contDiffOn hu).continuousOn.locallyIntegrableOn U.isOpen.measurableSet
        weak_eq := hweak }

end PDE.Hyperbolic.ConservationLaw.System
