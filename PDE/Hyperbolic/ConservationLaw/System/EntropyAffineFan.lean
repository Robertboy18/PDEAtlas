/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.EntropyWeak
public import PDE.Hyperbolic.ConservationLaw.AffineFan
import PDE.Hyperbolic.ConservationLaw.System.AffineFan

/-!
# Entropy equality across affine fans

The supplied middle-state map is `C¹` on the entire positive-time half-space,
including the two affine interfaces. It satisfies the conservation law in the
fan region and matches the constant outer states at those interfaces. These
hypotheses give the entropy identity for every compatible entropy pair, so the
three-region affine fan has zero distributional entropy production.

Convexity is not needed: it selects admissible discontinuities, whereas a
continuous rarefaction fan satisfies the entropy equation with equality.

The argument is the one used for the conservation law itself. Inside the fan
the entropy residual `∂t η(u) + ∂x q(u)` vanishes by the chain rule and the
compatibility `Dq = Dη ∘ Df` built into `EntropyPair`, and along the two
interfaces the traces of `η(u)` and `q(u)` match the constant outer values, so
the fan integration theorem applies to the pair `(η(u), q(u))`. For smooth solutions this is
the computation (27) of Evans, §11.4.2; a continuous fan satisfies the entropy inequalities (29)
with equality.

## Main results

* `integral_entropyWeakIntegrand_affineFan_eq_zero`: the tested entropy
  production of the fan is zero for every compatible entropy pair.
* `satisfiesEntropyInequalityFor_affineFan`, `isEntropyWeakSolution_affineFan`:
  the fan satisfies every entropy inequality and is an entropy weak solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.2, equations (26)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.System

noncomputable section

open MeasureTheory
open PDE.Common
open TopologicalSpace

open scoped Distributions Topology

variable {m : ℕ}

/-- A smooth conservative affine fan has zero tested entropy production for
every compatible entropy pair. -/
theorem integral_entropyWeakIntegrand_affineFan_eq_zero {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    (leftSpeed rightSpeed : ℝ) (hspeed : leftSpeed ≤ rightSpeed) (leftState rightState : ℝ^m)
    (middle : ℝ^2 → ℝ^m) (hmiddle : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 middle p)
    (hconservation : ∀ p ∈ AffineFan.middleRegion leftSpeed rightSpeed,
      fluxResidual flux middle p = 0)
    (hleft : ∀ t : ℝ, 0 < t → middle (AffineInterface.interface leftSpeed t) = leftState)
    (hright : ∀ t : ℝ, 0 < t → middle (AffineInterface.interface rightSpeed t) = rightState)
    (φ : 𝓓^{1}(forwardHalfSpace, ℝ)) :
    (∫ p : ℝ^2, entropyWeakIntegrand E
      (AffineFan.profile leftSpeed rightSpeed leftState middle rightState) φ p ∂volume) = 0 := by
  let entropyMiddle : ℝ^2 → ℝ := E.entropy ∘ middle
  let entropyFluxMiddle : ℝ^2 → ℝ := E.entropyFlux ∘ middle
  have hEntropyMiddle : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 entropyMiddle p :=
    fun p hp ↦ E.entropy_contDiff.contDiffAt.comp p (hmiddle p hp)
  have hEntropyFluxMiddle : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 entropyFluxMiddle p :=
    fun p hp ↦ E.entropyFlux_contDiff.contDiffAt.comp p (hmiddle p hp)
  have hEntropyConservation : ∀ p ∈ AffineFan.middleRegion leftSpeed rightSpeed,
        (∂[(0 : Fin 2)] entropyMiddle) p + (∂[(1 : Fin 2)] entropyFluxMiddle) p = 0 := by
    intro p hp
    simpa [entropyResidual, entropyMiddle, entropyFluxMiddle] using
      E.entropyResidual_eq_zero_of_flux (hmiddle p hp.1).differentiableAt_one (hconservation p hp)
  have hscalar := AffineFan.integral_conservative_pair_profile_eq_zero φ leftSpeed rightSpeed hspeed
      entropyMiddle entropyFluxMiddle (E.entropy leftState) (E.entropyFlux leftState)
      (E.entropy rightState) (E.entropyFlux rightState)
      hEntropyMiddle hEntropyFluxMiddle hEntropyConservation
      (fun t ht ↦ by simp [entropyMiddle, hleft t ht])
      (fun t ht ↦ by simp [entropyFluxMiddle, hleft t ht])
      (fun t ht ↦ by simp [entropyMiddle, hright t ht])
      (fun t ht ↦ by simp [entropyFluxMiddle, hright t ht])
  calc
    (∫ p : ℝ^2, entropyWeakIntegrand E (AffineFan.profile leftSpeed rightSpeed
            leftState middle rightState) φ p ∂volume) =
        ∫ p : ℝ^2, (AffineFan.profile leftSpeed rightSpeed (E.entropy leftState) entropyMiddle
                (E.entropy rightState) p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
            AffineFan.profile leftSpeed rightSpeed (E.entropyFlux leftState) entropyFluxMiddle
                (E.entropyFlux rightState) p *
              (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p) ∂volume := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [entropyWeakIntegrand]
      rw [AffineFan.comp_profile E.entropy leftSpeed rightSpeed leftState rightState middle p]
      rw [AffineFan.comp_profile E.entropyFlux leftSpeed rightSpeed leftState rightState middle p]
      rfl
    _ = 0 := hscalar

/-- A smooth conservative affine fan satisfies the entropy inequality for
every compatible entropy pair, in fact with equality. -/
theorem satisfiesEntropyInequalityFor_affineFan {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    (leftSpeed rightSpeed : ℝ) (hspeed : leftSpeed ≤ rightSpeed) (leftState rightState : ℝ^m)
    (middle : ℝ^2 → ℝ^m) (hmiddle : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 middle p)
    (hconservation : ∀ p ∈ AffineFan.middleRegion leftSpeed rightSpeed,
      fluxResidual flux middle p = 0)
    (hleft : ∀ t : ℝ, 0 < t → middle (AffineInterface.interface leftSpeed t) = leftState)
    (hright : ∀ t : ℝ, 0 < t → middle (AffineInterface.interface rightSpeed t) = rightState) :
    SatisfiesEntropyInequalityFor forwardHalfSpace
      (AffineFan.profile leftSpeed rightSpeed leftState middle rightState) E := by
  let entropyMiddle : ℝ^2 → ℝ := E.entropy ∘ middle
  let entropyFluxMiddle : ℝ^2 → ℝ := E.entropyFlux ∘ middle
  have hEntropyMiddleContinuous : ContinuousOn entropyMiddle forwardHalfSpace :=
    fun p hp ↦ (E.entropy_contDiff.contDiffAt.comp p (hmiddle p hp)).continuousAt
        |>.continuousWithinAt
  have hEntropyFluxMiddleContinuous : ContinuousOn entropyFluxMiddle forwardHalfSpace :=
    fun p hp ↦ (E.entropyFlux_contDiff.contDiffAt.comp p (hmiddle p hp)).continuousAt
        |>.continuousWithinAt
  refine ⟨?_, ?_, ?_⟩
  · have hprofile := locallyIntegrableOn_affineFan leftSpeed rightSpeed hspeed
        (E.entropy leftState) (E.entropy rightState) entropyMiddle
        (hEntropyMiddleContinuous.locallyIntegrableOn forwardHalfSpace.isOpen.measurableSet)
    apply hprofile.congr
    refine ae_restrict_of_forall_mem forwardHalfSpace.isOpen.measurableSet fun p _ ↦ ?_
    exact (AffineFan.comp_profile E.entropy leftSpeed rightSpeed leftState rightState middle p).symm
  · have hprofile := locallyIntegrableOn_affineFan leftSpeed rightSpeed hspeed
        (E.entropyFlux leftState) (E.entropyFlux rightState) entropyFluxMiddle
        (hEntropyFluxMiddleContinuous.locallyIntegrableOn forwardHalfSpace.isOpen.measurableSet)
    apply hprofile.congr
    refine ae_restrict_of_forall_mem forwardHalfSpace.isOpen.measurableSet fun p _ ↦ ?_
    exact (AffineFan.comp_profile E.entropyFlux leftSpeed rightSpeed
        leftState rightState middle p).symm
  · intro φ _
    rw [integral_entropyWeakIntegrand_affineFan_eq_zero
      E leftSpeed rightSpeed hspeed leftState rightState middle
      hmiddle hconservation hleft hright φ]

/-- A smooth conservative affine fan is an entropy weak solution.

The weak conservation law and every convex entropy identity use the same
middle-state equation and matching traces, so no additional fan data need be
bundled. -/
theorem isEntropyWeakSolution_affineFan {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 1 flux)
    (leftSpeed rightSpeed : ℝ) (hspeed : leftSpeed ≤ rightSpeed) (leftState rightState : ℝ^m)
    (middle : ℝ^2 → ℝ^m) (hmiddle : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 middle p)
    (hconservation : ∀ p ∈ AffineFan.middleRegion leftSpeed rightSpeed,
      fluxResidual flux middle p = 0)
    (hleft : ∀ t : ℝ, 0 < t → middle (AffineInterface.interface leftSpeed t) = leftState)
    (hright : ∀ t : ℝ, 0 < t → middle (AffineInterface.interface rightSpeed t) = rightState) :
    IsEntropyWeakSolution flux forwardHalfSpace
      (AffineFan.profile leftSpeed rightSpeed leftState middle rightState) := by
  constructor
  · exact isWeakSolution_affineFan flux hflux
      leftSpeed rightSpeed hspeed leftState rightState middle hmiddle hconservation hleft hright
  · exact fun E ↦ satisfiesEntropyInequalityFor_affineFan E.toEntropyPair
      leftSpeed rightSpeed hspeed leftState rightState middle hmiddle hconservation hleft hright

end

end PDE.Hyperbolic.ConservationLaw.System
