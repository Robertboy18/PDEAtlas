/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.InitialValue
public import PDE.Hyperbolic.ConservationLaw.Riemann.Trace
public import PDE.Hyperbolic.ConservationLaw.System.Riemann.Construction
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.Trace
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.VectorTesting

/-!
# Initial traces of the local system Riemann construction

Every fixed nonzero spatial point lies outside a finite propagation cone at
all sufficiently small positive times. The bounded wave construction therefore
attains the Riemann datum pointwise away from the jump, and strongly in local
`L¹` by the dominated-convergence criterion.

The construction from the flux is Theorem 4 of Evans, §11.2.4, the local solution of
Riemann's problem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2, equations (1)-(2); §11.2.4, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter MeasureTheory Set
open PDE.Common PDE.Hyperbolic.ConservationLaw.Scalar
open scoped ENNReal Topology Distributions InnerProductSpace

/-- The local Riemann construction attains its step datum strongly in
local `L¹` and belongs to `L∞` on the entire positive-time half-space. -/
theorem exists_local_riemann_solution_with_trace {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 2 flux) (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hfamilies : ∀ k, IsGenuinelyNonlinearFamily flux k ∨ IsLinearlyDegenerateFamily flux k)
    (left : ℝ^m) :
    ∃ δ K M : ℝ, 0 < δ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ right : ℝ^m, ‖right - left‖ < δ →
      ∃ u : ℝ^2 → ℝ^m,
        IsWeakSolutionWithInitialTrace flux (riemannData left right) u ∧
        Measurable u ∧ MemLp u ∞ (volume.restrict forwardHalfSpace) ∧
        (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
        (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
        (∀ p : ℝ^2, 0 < p 0 → p 1 < -M * p 0 → u p = left) ∧
        (∀ p : ℝ^2, 0 < p 0 → M * p 0 ≤ p 1 → u p = right) := by
  obtain ⟨δ, K, M, hδ, hK, hM, hsolve⟩ :=
    exists_local_riemann_weak_solution hflux hhyper hfamilies left
  refine ⟨δ, K, M, hδ, hK, hM, fun right hright ↦ ?_⟩
  obtain ⟨u, hu, hmu, hbu, hsu, hlu, hru⟩ := hsolve right hright
  refine ⟨u, ⟨hu, hasInitialTraceLocallyL1_riemannData_of_finitePropagation hmu hbu hlu hru⟩,
    hmu, ?_, hbu, hsu, hlu, hru⟩
  exact memLp_top_of_bound hmu.aestronglyMeasurable K
    ((ae_restrict_mem forwardHalfSpace.isOpen.measurableSet).mono fun p hp ↦ hbu p hp)

/-- A local weak Riemann solution from `C²` strict hyperbolicity and the
genuinely nonlinear or linearly degenerate alternative for every ordered family.

One radius, state bound and propagation speed work for every sufficiently close
right state. The same constructed function is the finite gluing of ordered weak
waves whose successive endpoint states satisfy `IsElementaryConnection`.
It satisfies the initial weak equation and attains the
step datum strongly in local `L¹`. The literal vector-test integrals are
integrable and include the initial face.

The statement records elementary connections between states, but does not identify
the returned wave profiles with the shocks, rarefactions or contacts witnessing those
connections. -/
theorem exists_local_riemann_initialValue_solution {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 2 flux) (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hfamilies : ∀ k, IsGenuinelyNonlinearFamily flux k ∨ IsLinearlyDegenerateFamily flux k)
    (left : ℝ^m) :
    ∃ δ K M : ℝ, 0 < δ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ right : ℝ^m, ‖right - left‖ < δ →
      ∃ (fields : Fin m → CharacteristicField flux) (state : ℕ → ℝ^m)
        (lo hi : Fin m → ℝ) (wave : Fin m → ℝ^2 → ℝ^m) (u : ℝ^2 → ℝ^m),
        (∀ k, (fields k).speed = characteristicSpeed flux k) ∧
        state 0 = left ∧ state m = right ∧
        (∀ k, IsElementaryConnection fields k (state k) (state (k + 1))) ∧
        (∀ k, lo k < hi k) ∧
        (∀ i j, i < j → hi i < lo j) ∧
        (∀ k, -M ≤ lo k ∧ hi k ≤ M) ∧
        (∀ k, IsWeakSolution flux forwardHalfSpace (wave k) ∧
          Measurable (wave k) ∧
          (∀ p : ℝ^2, 0 < p 0 → ‖wave k p‖ ≤ K) ∧
          (∀ c : ℝ, 0 < c → ∀ p, wave k (c • p) = wave k p) ∧
          (∀ p : ℝ^2, 0 < p 0 → p 1 < lo k * p 0 → wave k p = state k) ∧
          (∀ p : ℝ^2, 0 < p 0 → hi k * p 0 ≤ p 1 → wave k p = state (k + 1))) ∧
        IsWeakInitialValueSolution flux (riemannData left right) u ∧
        IsWeakSolutionWithInitialTrace flux (riemannData left right) u ∧
        Measurable u ∧ MemLp u ∞ (volume.restrict forwardHalfSpace) ∧
        (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
        (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
        (∀ p : ℝ^2, 0 < p 0 → p 1 < -M * p 0 → u p = left) ∧
        (∀ p : ℝ^2, 0 < p 0 → M * p 0 ≤ p 1 → u p = right) ∧
        (∀ p, u p = left + ∑ k : Fin m, (wave k p - state k)) ∧
        (∀ ψ : 𝓓^{1}((⊤ : TopologicalSpace.Opens ℝ^2), ℝ^m),
          IntegrableOn (fun p ↦
            ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪flux (u p), (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ)
            forwardHalfSpace volume ∧
          Integrable (fun x : ℝ ↦ ⟪riemannData left right x, ψ !₂[0, x]⟫_ℝ) volume ∧
          (∫ p in forwardHalfSpace,
            ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪flux (u p), (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ) +
            ∫ x : ℝ, ⟪riemannData left right x, ψ !₂[0, x]⟫_ℝ = 0) := by
  obtain ⟨δ, K, M, hδ, hK, hM, hsolve⟩ :=
    exists_local_riemann_wave_decomposition hflux hhyper hfamilies left
  refine ⟨δ, K, M, hδ, hK, hM, fun right hright ↦ ?_⟩
  obtain ⟨fields, state, lo, hi, wave, u, hc, hfirst, hlast, hchain,
    hwindow, hsep, hcone, hwaves, hu, hmu, hbu, hsu, hlu, hru, hformula⟩ := hsolve right hright
  have htrace := hasInitialTraceLocallyL1_riemannData_of_finitePropagation hmu hbu hlu hru
  have hlocal : ∀ C : Set (ℝ^2), IsCompact C → ∃ B : ℝ, ∀ p ∈ C, p ∈ forwardHalfSpace → ‖u p‖ ≤ B :=
    fun _ _ ↦ ⟨K, fun p _ hp ↦ hbu p hp⟩
  have hui := locallyIntegrable_restrict_of_bound_on_compacts (μ := volume)
    forwardHalfSpace.isOpen.measurableSet hmu.aestronglyMeasurable hlocal
  have hfi := locallyIntegrable_comp_restrict_of_bound_on_compacts (μ := volume)
    forwardHalfSpace.isOpen.measurableSet hmu.aestronglyMeasurable hlocal hflux.continuous
  have hinitial := isWeakInitialValueSolution_of_interior_of_initialTrace hui hfi htrace
    (fun φ ↦ by simpa only [weakIntegrand, InteriorWeakForm.integrand] using hu.weak_eq φ)
  refine ⟨fields, state, lo, hi, wave, u, hc, hfirst, hlast, hchain,
    hwindow, hsep, hcone, hwaves, hinitial, ⟨hu, htrace⟩, hmu, ?_, hbu, hsu, hlu, hru, hformula, ?_⟩
  · exact memLp_top_of_bound hmu.aestronglyMeasurable K
      ((ae_restrict_mem forwardHalfSpace.isOpen.measurableSet).mono fun p hp ↦ hbu p hp)
  · exact fun ψ ↦ ⟨integrableOn_initialVectorWeakIntegrand hui hfi ψ,
      integrable_initialVectorBoundary htrace.initial_locallyIntegrable ψ,
      (initialWeak_eq_zero_iff_vectorTests hui hfi
        htrace.initial_locallyIntegrable).mp hinitial.weak_initial_eq ψ⟩

end PDE.Hyperbolic.ConservationLaw.System
