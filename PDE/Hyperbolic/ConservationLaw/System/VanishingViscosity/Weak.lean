/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Weak
public import PDE.Hyperbolic.ConservationLaw.InteriorWeakForm
public import PDE.DistributionTheory.TestFunction.IntegrationByParts

/-!
# Testing the viscous conservation law

Two spatial integrations by parts put the viscosity term entirely on the test.
The state needs regularity only on the open domain containing its support.

This is the identity of step 3 of the proof of Evans, §11.4.2, Theorem 2, for tests with
compact support in an open set on which the state solves the viscous system (31), so without
the initial term.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.2, equation (31) and step 3 of the proof of Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-- The interior weak identity of a viscous solution, with both spatial
derivatives transferred to the test. -/
theorem integral_weakIntegrand_add_viscous_eq_zero {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ^m} {ε : ℝ} (hflux : ContDiff ℝ 1 flux) (hu : ContDiffOn ℝ 2 u U)
    (hpde : ∀ p ∈ U, fluxResidual flux u p = ε • (∂[1] (∂[1] u)) p) (φ : 𝓓(U, ℝ)) :
    (∫ p, (∂[0] (φ : ℝ^2 → ℝ)) p • u p + (∂[1] (φ : ℝ^2 → ℝ)) p • flux (u p)) +
      ε • ∫ p, (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) p • u p = 0 := by
  let ψ : 𝓓^{1}(U, ℝ) :=
    .mk φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset
  have hfirst := InteriorWeakForm.integral_smul_divergence_eq_neg_integrand
    (hu.of_le (by norm_num)) (hflux.comp_contDiffOn (hu.of_le (by norm_num))) ψ
  have heq : (∫ p, φ p • fluxResidual flux u p) =
      ε • ∫ p, φ p • (∂[1] (∂[1] u)) p := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hp : p ∈ U
    · rw [hpde p hp, smul_comm]
    · simp [φ.zero_on_compl hp]
  have hsecond := PDE.DistributionTheory.integral_smul_secondPartialDeriv_eq 1
    (φ.contDiff.of_le (by simp))
    (fun p hp ↦ hu.contDiffAt (U.isOpen.mem_nhds (φ.tsupport_subset hp))) φ.hasCompactSupport
  change (∫ p, φ p • fluxResidual flux u p) =
    -(∫ p, (∂[0] (φ : ℝ^2 → ℝ)) p • u p + (∂[1] (φ : ℝ^2 → ℝ)) p • flux (u p)) at hfirst
  rw [heq, hsecond] at hfirst
  rw [hfirst, add_neg_cancel]

end PDE.Hyperbolic.ConservationLaw.System
