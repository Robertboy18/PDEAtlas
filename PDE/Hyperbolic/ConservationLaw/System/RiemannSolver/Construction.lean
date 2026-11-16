/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.LocalWave
public import PDE.Hyperbolic.ConservationLaw.System.Riemann.ElementaryChain
public import PDE.Hyperbolic.ConservationLaw.System.Riemann.WeakSolution
import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyConstruction

/-!
# Local Riemann solutions with realized elementary waves

`exists_local_riemann_elementary_decomposition` is Theorem 4 of Evans, §11.2.4, with each wave
realized by a spacetime profile: a Lax shock, a contact, or a characteristic rarefaction. The
conclusion is local in the size of the initial jump and global for positive time by
self-similarity. It asserts elementary admissibility and the weak equation of every wave and of
the assembled solution.

The construction is in `RiemannSolver.EntropyConstruction`. Its theorem
`exists_local_riemann_entropy_elementary_decomposition` has the same hypotheses and proves, in
addition, every convex entropy inequality for the waves and for their assembly. The theorem
here is that statement with the entropy inequalities dropped.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.4, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

/-- Construct a local self-similar Riemann solution from a `C²` strictly
hyperbolic flux with genuinely nonlinear or linearly degenerate families.
Every component profile realizes the elementary connection between its
successive states. The radius and bounds are fixed before the right state. -/
theorem exists_local_riemann_elementary_decomposition {m : ℕ} {flux : ℝ^m → ℝ^m}
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
        (∀ k, IsElementaryWave fields k (state k) (state (k + 1)) (wave k) ∧
          IsWeakSolution flux forwardHalfSpace (wave k) ∧
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
    fun k ↦ ⟨(hwaves k).1, (hwaves k).2.1.weak, (hwaves k).2.2⟩, hu.weak, hrest⟩

end PDE.Hyperbolic.ConservationLaw.System
