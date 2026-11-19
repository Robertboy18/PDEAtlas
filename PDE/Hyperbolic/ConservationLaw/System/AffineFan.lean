/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.AffineFan
public import PDE.Hyperbolic.ConservationLaw.System.Weak
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Affine fans for systems of conservation laws

We lift the scalar affine-fan integration theorem to finite-dimensional
systems. A smooth conservative middle state, joined continuously to constant
states along two ordered affine interfaces, is a weak solution.

The proof is coordinatewise: each coordinate of the Bochner integral in `PiLp`
is the corresponding scalar integral, so the boundary calculation is the one in
`ConservationLaw.AffineFan`. The centered rarefaction waves of Evans, §11.2.2, Theorem 1, are
fans of this kind.

## Main results

* `locallyIntegrableOn_affineFan`: an ordered fan is locally integrable on
  `t > 0` whenever its middle state is.
* `isWeakSolution_affineFan`: for a `C¹` flux, a middle state that is `C¹` on
  `t > 0`, satisfies `u_t + (f(u))_x = 0` in the fan region, and takes the
  constant outer states as traces on the two interfaces defines a weak solution
  of the system on `t > 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.System

noncomputable section

open MeasureTheory
open PDE.Common
open TopologicalSpace

open scoped Distributions Topology

variable {m n : ℕ}

private theorem locallyIntegrableOn_indicator {E : Type*} [NormedAddCommGroup E] {f : ℝ^2 → E}
    {U s : Set ℝ^2} (hf : LocallyIntegrableOn f U volume) (hs : MeasurableSet s) :
    LocallyIntegrableOn (s.indicator f) U volume := by
  intro p hp
  rcases hf p hp with ⟨t, ht, hft⟩
  exact ⟨t, ht, hft.indicator hs⟩

/-- An ordered affine fan is locally integrable whenever its middle state is
locally integrable on positive time. -/
theorem locallyIntegrableOn_affineFan {E : Type*} [NormedAddCommGroup E] (leftSpeed rightSpeed : ℝ)
    (hspeed : leftSpeed ≤ rightSpeed) (leftState rightState : E) (middle : ℝ^2 → E)
    (hmiddle : LocallyIntegrableOn middle forwardHalfSpace volume) :
    LocallyIntegrableOn (AffineFan.profile leftSpeed rightSpeed leftState middle rightState)
      forwardHalfSpace volume := by
  let left := AffineInterface.leftHalfSpace leftSpeed
  let right := AffineInterface.leftHalfSpace rightSpeed
  have hassembled : LocallyIntegrableOn ((fun _ : ℝ^2 ↦ rightState) +
      right.indicator (fun p ↦ middle p - rightState) +
      left.indicator (fun p ↦ leftState - middle p)) forwardHalfSpace volume :=
    ((locallyIntegrableOn_const rightState).add (locallyIntegrableOn_indicator
      (hmiddle.sub (locallyIntegrableOn_const rightState))
      (AffineInterface.measurableSet_leftHalfSpace rightSpeed))).add
      (locallyIntegrableOn_indicator ((locallyIntegrableOn_const leftState).sub hmiddle)
        (AffineInterface.measurableSet_leftHalfSpace leftSpeed))
  refine hassembled.congr
    (ae_restrict_of_forall_mem forwardHalfSpace.isOpen.measurableSet fun p hp ↦ ?_)
  by_cases hleft : p ∈ left
  · have hright : p ∈ right :=
      lt_of_lt_of_le hleft (mul_le_mul_of_nonneg_right hspeed (le_of_lt hp))
    simp [left, right, hleft, hright, AffineFan.profile]
  · by_cases hright : p ∈ right <;> simp [left, right, hleft, hright, AffineFan.profile]

/-- A smooth state that is conservative between two matching affine traces
defines a weak solution of a finite-dimensional conservation-law system.

The statement uses no bundled Riemann profile: the only structure in the
conclusion is the weak-solution predicate. The extension of the middle state
must be `C¹` on positive time, but the conservation law is required only in the
fan region.
-/
theorem isWeakSolution_affineFan (flux : ℝ^m → ℝ^m) (hflux : ContDiff ℝ 1 flux)
    (leftSpeed rightSpeed : ℝ) (hspeed : leftSpeed ≤ rightSpeed) (leftState rightState : ℝ^m)
    (middle : ℝ^2 → ℝ^m) (hmiddle : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 middle p)
    (hconservation : ∀ p ∈ AffineFan.middleRegion leftSpeed rightSpeed,
      fluxResidual flux middle p = 0)
    (hleft : ∀ t : ℝ, 0 < t → middle (AffineInterface.interface leftSpeed t) = leftState)
    (hright : ∀ t : ℝ, 0 < t → middle (AffineInterface.interface rightSpeed t) = rightState) :
    IsWeakSolution flux forwardHalfSpace
      (AffineFan.profile leftSpeed rightSpeed leftState middle rightState) := by
  let middleFlux : ℝ^2 → ℝ^m := fun p ↦ flux (middle p)
  have hmiddleFlux (p : ℝ^2) (hp : p ∈ forwardHalfSpace) : ContDiffAt ℝ 1 middleFlux p :=
    hflux.contDiffAt.comp p (hmiddle p hp)
  have hstateLocal : LocallyIntegrableOn
      (AffineFan.profile leftSpeed rightSpeed leftState middle rightState)
      forwardHalfSpace volume :=
    locallyIntegrableOn_affineFan leftSpeed rightSpeed hspeed leftState rightState middle
      (ContinuousOn.locallyIntegrableOn (fun p hp ↦ (hmiddle p hp).continuousAt.continuousWithinAt)
        forwardHalfSpace.isOpen.measurableSet)
  have hfluxLocal : LocallyIntegrableOn
      (fun p ↦ flux (AffineFan.profile leftSpeed rightSpeed leftState middle rightState p))
      forwardHalfSpace volume :=
    (locallyIntegrableOn_affineFan leftSpeed rightSpeed hspeed (flux leftState)
      (flux rightState) middleFlux (ContinuousOn.locallyIntegrableOn
        (fun p hp ↦ (hmiddleFlux p hp).continuousAt.continuousWithinAt)
        forwardHalfSpace.isOpen.measurableSet)).congr
      (ae_restrict_of_forall_mem forwardHalfSpace.isOpen.measurableSet fun p _ ↦
        (AffineFan.comp_profile flux leftSpeed rightSpeed leftState rightState middle p).symm)
  refine ⟨hstateLocal, hfluxLocal, fun φ ↦ PiLp.ext fun i ↦ ?_⟩
  have hintegrable : Integrable (weakIntegrand flux
      (AffineFan.profile leftSpeed rightSpeed leftState middle rightState) φ) volume :=
    integrable_weakIntegrand hstateLocal hfluxLocal φ
  rw [MeasureTheory.eval_integral_piLp (fun j ↦ hintegrable.eval_piLp j) i]
  have hscalarConservation : ∀ p ∈ AffineFan.middleRegion leftSpeed rightSpeed,
      (∂[(0 : Fin 2)] (fun q ↦ middle q i)) p +
        (∂[(1 : Fin 2)] (fun q ↦ middleFlux q i)) p = 0 := fun p hp ↦ by
    simpa [fluxResidual, middleFlux, Function.comp_def,
      partialDeriv_apply (0 : Fin 2) i (hmiddle p hp.1).differentiableAt_one,
      partialDeriv_apply (1 : Fin 2) i (hmiddleFlux p hp.1).differentiableAt_one] using
      congrArg (fun state : ℝ^m ↦ state i) (hconservation p hp)
  have hintegrand (p : ℝ^2) : weakIntegrand flux
          (AffineFan.profile leftSpeed rightSpeed leftState middle rightState) φ p i =
        AffineFan.profile leftSpeed rightSpeed (leftState i) (fun q ↦ middle q i)
            (rightState i) p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
          AffineFan.profile leftSpeed rightSpeed (flux leftState i)
            (fun q ↦ middleFlux q i) (flux rightState i) p *
            (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p := by
    simp only [weakIntegrand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [AffineFan.comp_profile (fun state : ℝ^m ↦ state i)
      leftSpeed rightSpeed leftState rightState middle p,
      AffineFan.comp_profile (fun state : ℝ^m ↦ flux state i)
        leftSpeed rightSpeed leftState rightState middle p]
    simp only [middleFlux, mul_comm]
  exact (integral_congr_ae (Filter.Eventually.of_forall hintegrand)).trans
    (AffineFan.integral_conservative_pair_profile_eq_zero φ leftSpeed rightSpeed hspeed
      (fun p ↦ middle p i) (fun p ↦ middleFlux p i) (leftState i) (flux leftState i)
      (rightState i) (flux rightState i) (fun p hp ↦ (contDiffAt_piLp 2).1 (hmiddle p hp) i)
      (fun p hp ↦ (contDiffAt_piLp 2).1 (hmiddleFlux p hp) i) hscalarConservation
      (fun t ht ↦ by simp [hleft t ht]) (fun t ht ↦ by simp [middleFlux, hleft t ht])
      (fun t ht ↦ by simp [hright t ht]) (fun t ht ↦ by simp [middleFlux, hright t ht]))

end

end PDE.Hyperbolic.ConservationLaw.System
