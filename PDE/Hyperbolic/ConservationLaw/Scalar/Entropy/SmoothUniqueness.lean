/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.SmoothTesting
public import PDE.Hyperbolic.ConservationLaw.Scalar.InitialValue.L1
public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.Uniqueness

/-!
# Uniqueness for Evans's smooth entropy and test classes

Theorem 3 of Evans, §11.4.3, is uniqueness of entropy solutions in his sense: smooth convex
entropy pairs, nonnegative smooth compactly supported tests, and solutions in
`C([0, ∞), L¹(ℝ)) ∩ L∞` with `u(·, t) → g` in `L¹` as `t → 0`.
The class `IsEntropySolutionInSmoothTestClass` records these requirements using an L¹ curve and
its almost-everywhere spatial representatives. The state itself need not be smooth.

We convert to the C¹ entropy formulation and the strong local L¹ trace.
Kružkov contraction then gives spacetime almost-everywhere uniqueness for every smooth
scalar flux.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, definition of entropy solution and Theorem 3,
  equations (35)-(38).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory PDE.Common
open scoped ContDiff NNReal

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- Evans's scalar entropy solution class with smooth entropy pairs and smooth tests.
The L¹ curve supplies time continuity and the prescribed initial value. -/
structure IsEntropySolutionInSmoothTestClass
    (flux : ℝ → ℝ) (u₀ : ℝ → ℝ) (u : ℝ^2 → ℝ) : Prop where
  /-- The state is measurable on positive spacetime. -/
  measurable : AEStronglyMeasurable u (volume.restrict forwardHalfSpace)
  /-- The state is uniformly essentially bounded on positive spacetime. -/
  bounded : ∃ M : ℝ, ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M
  /-- Only smooth entropy pairs and nonnegative smooth compact tests are required. -/
  entropy : SatisfiesSmoothEntropyInequality flux forwardHalfSpace u
  /-- The spatial slices represent a continuous L¹ curve starting at the datum. -/
  l1_curve : ∃ w : ℝ≥0 → Lp ℝ 1 (volume : Measure ℝ),
    Continuous w ∧
      (∀ t : ℝ≥0, (fun x : ℝ ↦ u !₂[(t : ℝ), x]) =ᵐ[volume] w t) ∧
      u₀ =ᵐ[volume] w 0

variable {flux : ℝ → ℝ} {u₀ : ℝ → ℝ} {u v : ℝ^2 → ℝ}

/-- The smooth book class implies the C¹ entropy formulation and strong local initial trace. -/
theorem IsEntropySolutionInSmoothTestClass.isEntropySolutionWithInitialTrace
    (h : IsEntropySolutionInSmoothTestClass flux u₀ u) (hf : ContDiff ℝ ∞ flux) :
    IsEntropySolutionWithInitialTrace flux u₀ u := by
  obtain ⟨M, hM⟩ := h.bounded
  obtain ⟨w, hw, hrep, h₀⟩ := h.l1_curve
  exact ⟨h.entropy.isEntropyWeakSolution hf h.measurable hM,
    hasInitialTraceLocallyL1_of_continuousAt_L1 w hw.continuousAt hrep h₀⟩

/-- Theorem 3 of Evans, §11.4.3: bounded scalar entropy solutions in the book's smooth
test class, with the same L¹ initial datum and smooth flux, agree almost everywhere. -/
theorem IsEntropySolutionInSmoothTestClass.unique_ae
    (hu : IsEntropySolutionInSmoothTestClass flux u₀ u)
    (hv : IsEntropySolutionInSmoothTestClass flux u₀ v) (hf : ContDiff ℝ ∞ flux) :
    u =ᵐ[volume.restrict forwardHalfSpace] v := by
  obtain ⟨Mu, hMu⟩ := hu.bounded
  obtain ⟨Mv, hMv⟩ := hv.bounded
  apply (hu.isEntropySolutionWithInitialTrace hf).unique_ae
    (hv.isEntropySolutionWithInitialTrace hf) (hf.of_le (by simp)) (M := max Mu Mv)
  · exact hMu.mono fun _ hp ↦ hp.trans (le_max_left _ _)
  · exact hMv.mono fun _ hp ↦ hp.trans (le_max_right _ _)

end PDE.Hyperbolic.ConservationLaw.Scalar
