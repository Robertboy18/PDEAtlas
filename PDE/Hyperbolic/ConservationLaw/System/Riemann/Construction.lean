/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Riemann.ElementaryChain
public import PDE.Hyperbolic.ConservationLaw.System.Riemann.WeakSolution
import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyConstruction

/-!
# Weak Riemann solutions from local wave curves

`exists_local_riemann_wave_decomposition` is the conclusion of the proof of Evans, §11.2.4,
Theorem 4: the states `state k` are the `z_k` of (44)-(45), each joined to the next by a wave of
family `k`, and the speed windows `(lo k, hi k)` are ordered and disjoint, as in step 4 of that
proof. It is `exists_local_riemann_entropy_elementary_decomposition` of
`RiemannSolver.EntropyConstruction`, which holds the construction, without the entropy
inequalities and without the identification of each wave with the shock, contact or
rarefaction of its connection.
`exists_local_riemann_weak_solution` is Theorem 4 for the weak equation on `t > 0`;
`exists_local_riemann_initialValue_solution` adds the Riemann datum as initial trace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.4, Theorem 4 and its proof, equations (44)-(49).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

/-- Hyperbolicity and the family alternatives construct ordered elementary
states, weak waves in separated speed windows, and their finite gluing.
The radius and bounds precede the right state. The finite-sum identity ties the
solution to these same waves, including in the zero-family case.

`IsElementaryConnection` describes the successive endpoint states. The conclusions
about each `wave k` give its weak equation, bounds, self-similarity and outer states;
they do not identify its profile with the shock or rarefaction witnessing that
connection. -/
theorem exists_local_riemann_wave_decomposition {m : ℕ} {flux : ℝ^m → ℝ^m}
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
        IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
        (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
        (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
        (∀ p : ℝ^2, 0 < p 0 → p 1 < -M * p 0 → u p = left) ∧
        (∀ p : ℝ^2, 0 < p 0 → M * p 0 ≤ p 1 → u p = right) ∧
        (∀ p, u p = left + ∑ k : Fin m, (wave k p - state k)) := by
  obtain ⟨δ, K, M, hδ, hK, hM, hsolve⟩ :=
    exists_local_riemann_entropy_elementary_decomposition hflux hhyper hfamilies left
  refine ⟨δ, K, M, hδ, hK, hM, fun right hright ↦ ?_⟩
  obtain ⟨fields, state, lo, hi, wave, u, hcanonical, hfirst, hlast, hchain, hwindow, hsep, hcone,
    hwaves, hu, hrest⟩ := hsolve right hright
  exact ⟨fields, state, lo, hi, wave, u, hcanonical, hfirst, hlast, hchain, hwindow, hsep, hcone,
    fun k ↦ ⟨(hwaves k).2.1.weak, (hwaves k).2.2⟩, hu.weak, hrest⟩

/-- A `C²` strictly hyperbolic system with genuinely nonlinear or linearly
degenerate characteristic families admits bounded self-similar weak solutions
for all sufficiently small Riemann jumps. The neighborhood, state bound, and
propagation speed are chosen before the right state. Initial-value identities
follow separately from the finite propagation cone. -/
theorem exists_local_riemann_weak_solution {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 2 flux)
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hfamilies : ∀ k, IsGenuinelyNonlinearFamily flux k ∨ IsLinearlyDegenerateFamily flux k)
    (left : ℝ^m) :
    ∃ δ K M : ℝ, 0 < δ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ right : ℝ^m, ‖right - left‖ < δ →
      ∃ u : ℝ^2 → ℝ^m,
        IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
        (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
        (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
        (∀ p : ℝ^2, 0 < p 0 → p 1 < -M * p 0 → u p = left) ∧
        (∀ p : ℝ^2, 0 < p 0 → M * p 0 ≤ p 1 → u p = right) := by
  obtain ⟨δ, K, M, hδ, hK, hM, hsolve⟩ :=
    exists_local_riemann_wave_decomposition hflux hhyper hfamilies left
  refine ⟨δ, K, M, hδ, hK, hM, fun right hright ↦ ?_⟩
  obtain ⟨_fields, _state, _lo, _hi, _wave, u, _hcanonical, _hfirst, _hlast, _hchain,
    _hwindow, _hsep, _hcone, _hwaves, hu, hmu, hbu, hsu, hlu, hru, _hformula⟩ := hsolve right hright
  exact ⟨u, hu, hmu, hbu, hsu, hlu, hru⟩

end PDE.Hyperbolic.ConservationLaw.System
