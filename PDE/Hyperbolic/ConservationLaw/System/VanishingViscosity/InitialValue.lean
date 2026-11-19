/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.VanishingViscosity.Weak
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.TimeCutoff

/-!
# The initial-boundary identity of a viscous system

The equation is tested away from time zero, then an increasing time
cutoff is removed. Continuity of the state up to the initial slice recovers
the initial datum. Derivatives of the state need no bounds near that slice.

The identity is that of step 3 of the proof of Evans, §11.4.2, Theorem 2, with the initial
term `∫ v(0, x) · u(0, x) dx` in place of Evans's `∫ g · v dx`. Letting `ε → 0` in it, Evans
obtains the identity (13) of §11.1.1 that defines an integral solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equation (13); §11.4.2, equation (31) and step 3
  of the proof of Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace PDE.Common PDE.Analysis
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-- The viscous PDE gives its weak initial-boundary equation, with the
positive initial term and both spatial derivatives on the smooth test. -/
theorem integral_initialWeakIntegrand_add_viscous_eq_zero {flux : ℝ^m → ℝ^m} {u : ℝ^2 → ℝ^m} {ε : ℝ}
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiffOn ℝ 2 u forwardHalfSpace)
    (hclosed : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0})
    (hui : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hfi : LocallyIntegrable (fun p ↦ flux (u p)) (volume.restrict forwardHalfSpace))
    (hpde : ∀ p ∈ forwardHalfSpace, fluxResidual flux u p = ε • (∂[1] (∂[1] u)) p)
    (φ : 𝓓((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p in forwardHalfSpace, (∂[0] (φ : ℝ^2 → ℝ)) p • u p + (∂[1] (φ : ℝ^2 → ℝ)) p • flux (u p)) +
      (∫ x : ℝ, φ !₂[0, x] • u !₂[0, x]) + ε • ∫ p in forwardHalfSpace,
      (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) p • u p = 0 := by
  let ψ : InitialValueTestFunction :=
    .mk φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset
  have hI := integrableOn_initialWeakIntegrand hui hfi ψ
  have hc : Continuous (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) :=
    (contDiff_top_partialDeriv (contDiff_top_partialDeriv φ.contDiff)).continuous
  have hs : HasCompactSupport (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) :=
    (φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single 1 1)).fderiv_apply
      (𝕜 := ℝ) (EuclideanSpace.single 1 1)
  have hII : IntegrableOn (fun p ↦ (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) p • u p)
      forwardHalfSpace := hui.integrable_smul_left_of_hasCompactSupport hc hs
  have hlim := ((tendsto_integral_initialTimeCutoff_smul hI).add
    (tendsto_integral_derivCutoff_test_smul hui ψ
      (ψ.tendsto_integral_smul_of_continuousOn hclosed))).add
        ((tendsto_integral_initialTimeCutoff_smul hII).const_smul ε)
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  have hweak := integral_weakIntegrand_add_viscous_eq_zero hflux hu hpde
    (smoothInteriorCutoffTest φ hδ)
  have heq (p : ℝ^2) : (∂[0] ((smoothInteriorCutoffTest φ hδ) : ℝ^2 → ℝ)) p • u p +
        (∂[1] ((smoothInteriorCutoffTest φ hδ) : ℝ^2 → ℝ)) p • flux (u p) =
      initialTimeCutoff δ (p 0) • InteriorWeakForm.integrand u (fun p ↦ flux (u p)) ψ p +
        deriv (initialTimeCutoff δ) (p 0) • (ψ p • u p) :=
    integrand_interiorCutoffTest u (fun p ↦ flux (u p)) ψ hδ p
  rw [show (fun p ↦ (∂[0] ((smoothInteriorCutoffTest φ hδ) : ℝ^2 → ℝ)) p • u p +
      (∂[1] ((smoothInteriorCutoffTest φ hδ) : ℝ^2 → ℝ)) p • flux (u p)) =
      fun p ↦ initialTimeCutoff δ (p 0) • InteriorWeakForm.integrand u (fun p ↦ flux (u p)) ψ p +
        deriv (initialTimeCutoff δ) (p 0) • (ψ p • u p) from funext heq] at hweak
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := (forwardHalfSpace : Set ℝ^2)) (fun p hp ↦ by
        have hz := initialTimeCutoff_zero hδ (le_trans (le_of_not_gt hp) hδ.le)
        have hd := deriv_initialTimeCutoff_eq_zero hδ
          (fun hm ↦ (not_lt_of_ge (le_of_not_gt hp)) (hδ.trans_le hm.1))
        simp [hz, hd]), integral_add (integrableOn_initialTimeCutoff_smul hI δ)
      (integrableOn_derivCutoff_test_smul hui ψ δ)] at hweak
  have hsecond : (∫ p, (∂[1] (∂[1] ((smoothInteriorCutoffTest φ hδ) : ℝ^2 → ℝ))) p
      • u p) = ∫ p in forwardHalfSpace,
        initialTimeCutoff δ (p 0) • ((∂[1] (∂[1] (φ : ℝ^2 → ℝ))) p • u p) := by
    simp_rw [secondPartialDeriv_smoothInteriorCutoffTest, mul_smul]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro p hp
    rw [initialTimeCutoff_zero hδ (le_trans (le_of_not_gt hp) hδ.le), zero_smul]
  rw [hsecond] at hweak
  exact hweak.symm

end PDE.Hyperbolic.ConservationLaw.System
