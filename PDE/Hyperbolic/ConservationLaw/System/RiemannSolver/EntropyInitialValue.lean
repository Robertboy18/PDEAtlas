/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyConstruction
public import PDE.Hyperbolic.ConservationLaw.System.InitialValue
public import PDE.Hyperbolic.ConservationLaw.Riemann.Trace
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.Trace

/-!
# The entropy admissible local Riemann initial-value solution

The constructed Lax shocks, contacts and rarefactions satisfy all convex
compatible entropy inequalities, and so does their finite assembly. The
same solution satisfies the initial-face weak equation and has the Riemann
datum as a strong local `L¹` trace. The jump radius and propagation bounds
are uniform in the right state and in the entropy pair. The solution is the integral solution
of Riemann's problem in Theorem 4 of Evans, §11.2.4, and it also satisfies the entropy
inequalities (29) of §11.4.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equation (13); §11.2.4, Theorem 4; §11.4.2,
  equations (25)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open MeasureTheory Set
open PDE.Hyperbolic.ConservationLaw.Scalar
open scoped ENNReal

/-- The local Riemann IVP from a `C²` strictly hyperbolic flux and the usual
family alternatives, with Lax shocks, contacts and characteristic
rarefaction fans. The same profile satisfies the weak initial-value equation,
strong local `L¹` trace, uniform bound and propagation cone. Entropy inequalities
for the components and their assembly follow from the flux hypotheses.
The entropy pairs need only be `C¹` and convex; in particular all compatible
`C²` convex pairs are covered. -/
theorem exists_local_riemann_entropy_initialValue_solution_with_elementary_waves {m : ℕ}
    {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 2 flux) (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
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
        (∀ k, IsElementaryWave fields k (state k) (state (k + 1)) (wave k) ∧
          IsEntropyWeakSolution flux forwardHalfSpace (wave k) ∧
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
        (∀ k p, 0 < p 0 → lo k * p 0 ≤ p 1 → p 1 < hi k * p 0 →
          u p = wave k p) ∧
        IsEntropyWeakSolution flux forwardHalfSpace u := by
  obtain ⟨δ, K, M, hδ, hK, hM, hsolve⟩ :=
    exists_local_riemann_entropy_elementary_decomposition hflux hhyper hfamilies left
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
    (fun φ ↦ by simpa only [weakIntegrand, InteriorWeakForm.integrand] using hu.weak.weak_eq φ)
  refine ⟨fields, state, lo, hi, wave, u, hc, hfirst, hlast, hchain,
    hwindow, hsep, hcone, hwaves, hinitial, ⟨hu.weak, htrace⟩, hmu, ?_,
    hbu, hsu, hlu, hru, hformula, ?_, hu⟩
  · exact memLp_top_of_bound hmu.aestronglyMeasurable K
      ((ae_restrict_mem forwardHalfSpace.isOpen.measurableSet).mono fun p hp ↦ hbu p hp)
  · intro k p ht ha hb
    rw [hformula p, ← hfirst]
    exact sum_waves_eq_of_mem_window state wave lo hi (fun i j hij ↦ (hsep i j hij).le)
      (fun i ↦ (hwaves i).2.2.2.2.2.1) (fun i ↦ (hwaves i).2.2.2.2.2.2) k ht ha hb

end PDE.Hyperbolic.ConservationLaw.System
