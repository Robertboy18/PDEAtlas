/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.InitialBoundaryCutoff
import PDE.DistributionTheory.TestFunction

/-!
# Initial boundary terms for Kato's inequality

A time cutoff recovers the boundary pairing from a strong local `L¹` trace.
The argument applies to independently specified density and flux fields, so it
also applies to the entropy distance and its two-state flux. All integrability
near time zero is with respect to the restricted half-space measure.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

/-- An interior divergence inequality and a strong initial trace imply its
initial-boundary version. This is applied below to the Kato density and flux. -/
theorem initial_boundary_inequality {u q : ℝ^2 → ℝ} {u₀ : ℝ → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (htrace : HasInitialTraceLocallyL1 u u₀)
    (hineq : ∀ φ : 𝓓^{1}(forwardHalfSpace, ℝ), (∀ p, 0 ≤ φ p) → 0 ≤ ∫ p,
      InteriorWeakForm.integrand u q φ p)
    (φ : InitialValueTestFunction) (hφ : ∀ p, 0 ≤ φ p) :
    0 ≤ (∫ p : ℝ^2 in forwardHalfSpace, InteriorWeakForm.integrand u q φ p) +
      ∫ x : ℝ, φ !₂[0, x] * u₀ x := by
  have hI := integrableOn_initialWeakIntegrand hu hq φ
  have hlim := (tendsto_integral_initialTimeCutoff_smul hI).add
    (tendsto_integral_derivCutoff_test_mul hu htrace φ)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hnonneg : ∀ p, 0 ≤ interiorCutoffTest φ hε p :=
    fun p ↦ mul_nonneg (Real.smoothTransition.nonneg _) (hφ p)
  have h := hineq (interiorCutoffTest φ hε) hnonneg
  have heq : (∫ p : ℝ^2 in forwardHalfSpace,
      InteriorWeakForm.integrand u q (interiorCutoffTest φ hε) p) =
      ∫ p : ℝ^2, InteriorWeakForm.integrand u q (interiorCutoffTest φ hε) p := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ ?_
    simp only [InteriorWeakForm.integrand,
      (interiorCutoffTest φ hε).partialDeriv_eq_zero_of_notMem hp, zero_smul, add_zero]
  rw [← heq] at h
  have hform : InteriorWeakForm.integrand u q (interiorCutoffTest φ hε) =
      fun p ↦ initialTimeCutoff ε (p 0) • InteriorWeakForm.integrand u q φ p +
        deriv (initialTimeCutoff ε) (p 0) • (φ p • u p) :=
    funext (integrand_interiorCutoffTest u q φ hε)
  rw [hform] at h
  rwa [integral_add (integrableOn_initialTimeCutoff_smul hI ε)
    (integrableOn_derivCutoff_test_smul hu φ ε)] at h

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov
