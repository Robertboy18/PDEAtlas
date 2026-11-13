/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.Trace

/-!
# Time cutoffs at the initial boundary

The shared Banach-valued cutoff theorem specializes to scalar conservation
laws and their strong-trace predicate. The interior weak equation and a strong
local `L¹` initial trace then give the weak identity for tests that meet the
initial slice, when the state and the flux are locally integrable up to time
zero. Local boundedness up to time zero suffices when the scalar flux is
continuous. Entropy inequalities use the same boundary-kernel limit.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- The initial boundary kernel recovers the compact test pairing with the strong initial trace. -/
theorem tendsto_integral_derivCutoff_test_mul {u : ℝ^2 → ℝ} {u₀ : ℝ → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (htrace : HasInitialTraceLocallyL1 u u₀) (φ : InitialValueTestFunction) :
    Tendsto (fun ε : ℝ ↦ ∫ p : ℝ^2 in forwardHalfSpace, deriv (initialTimeCutoff ε) (p 0) *
      (φ p * u p)) (𝓝[>] 0) (𝓝 (∫ x : ℝ, φ !₂[0, x] * u₀ x)) :=
  tendsto_integral_derivCutoff_test_smul hu φ (htrace.tendsto_integral_test_smul φ)

/-- The interior conservation law and a strong local `L¹` trace imply the weak
initial-boundary identity. The local integrability assumptions use the restricted
half-space measure at every spacetime point, so they control the state and flux
near the initial boundary as well as at positive times. -/
theorem IsWeakSolutionWithInitialTrace.isWeakInitialValueSolution {flux : ℝ → ℝ} {u₀ : ℝ → ℝ}
    {u : ℝ^2 → ℝ} (hu : IsWeakSolutionWithInitialTrace flux u₀ u)
    (hu_int : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hflux_int : LocallyIntegrable (fun p ↦ flux (u p)) (volume.restrict forwardHalfSpace)) :
    IsWeakInitialValueSolution flux u₀ u := by
  apply isWeakInitialValueSolution_of_interior_of_initialTrace hu_int hflux_int hu.initialTrace
  intro φ
  simpa only [weakIntegrand, InteriorWeakForm.integrand, smul_eq_mul, mul_comm] using
    hu.interior.weak_eq φ

/-- For a continuous flux, bounds on compact spacetime sets up to time zero
turn the interior weak equation and strong local `L¹` initial trace into
the initial-boundary weak formulation. The bound may depend on the compact
set and is needed only at positive times. -/
theorem IsWeakSolutionWithInitialTrace.isWeakInitialValueSolution_of_locallyBounded {flux : ℝ → ℝ}
    {u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ} (hu : IsWeakSolutionWithInitialTrace flux u₀ u)
    (hflux : Continuous flux)
    (hbound : ∀ K : Set ℝ^2, IsCompact K → ∃ C : ℝ, ∀ p ∈ K, p ∈ forwardHalfSpace → ‖u p‖ ≤ C) :
    IsWeakInitialValueSolution flux u₀ u := by
  apply hu.isWeakInitialValueSolution
  · exact locallyIntegrable_restrict_of_bound_on_compacts forwardHalfSpace.isOpen.measurableSet
      hu.interior.u_locallyIntegrable.aestronglyMeasurable hbound
  · exact locallyIntegrable_comp_restrict_of_bound_on_compacts forwardHalfSpace.isOpen.measurableSet
      hu.interior.u_locallyIntegrable.aestronglyMeasurable hbound hflux

end PDE.Hyperbolic.ConservationLaw.Scalar
