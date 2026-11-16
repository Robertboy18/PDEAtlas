/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.Construction
public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.Gluing
public import PDE.Hyperbolic.ConservationLaw.System.InitialValue
public import PDE.Hyperbolic.ConservationLaw.Riemann.Trace
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.Trace
import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyInitialValue

/-!
# The local elementary Riemann initial-value solution

The constructed self-similar solution has its Riemann datum as a strong
local `L¹` trace and satisfies the initial-face weak equation. Its component
profiles realize their elementary connections, and the assembled solution
agrees pointwise with each component in its speed window. The solution is the one of
Theorem 4 of Evans, §11.2.4, and the weak initial-value equation is (13) of §11.1.1.

The theorem is `exists_local_riemann_entropy_initialValue_solution_with_elementary_waves` of
`RiemannSolver.EntropyInitialValue`, which has the same hypotheses, in a weaker form: the
components are stated as weak solutions, and the entropy admissibility of the assembled
solution is stated as an implication from the entropy inequalities of the components. The
entropy theorem proves both without that hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equation (13); §11.2.4, Theorem 4.
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
strong local `L¹` trace, uniform bound and propagation cone. Entropy gluing
is recorded as an implication from the component inequalities. This is the weak form of
`exists_local_riemann_entropy_initialValue_solution_with_elementary_waves`, which proves the
component inequalities. -/
theorem exists_local_riemann_initialValue_solution_with_elementary_waves {m : ℕ} {flux : ℝ^m → ℝ^m}
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
        ((∀ k, SatisfiesEntropyInequality flux forwardHalfSpace (wave k)) →
          IsEntropyWeakSolution flux forwardHalfSpace u) := by
  obtain ⟨δ, K, M, hδ, hK, hM, hsolve⟩ :=
    exists_local_riemann_entropy_initialValue_solution_with_elementary_waves hflux hhyper
      hfamilies left
  refine ⟨δ, K, M, hδ, hK, hM, fun right hright ↦ ?_⟩
  obtain ⟨fields, state, lo, hi, wave, u, hc, hfirst, hlast, hchain, hwindow, hsep, hcone, hwaves,
    hinitial, htrace, hmu, hmem, hbu, hsu, hlu, hru, hformula, hinside, hentropy⟩ :=
    hsolve right hright
  exact ⟨fields, state, lo, hi, wave, u, hc, hfirst, hlast, hchain, hwindow, hsep, hcone,
    fun k ↦ ⟨(hwaves k).1, (hwaves k).2.1.weak, (hwaves k).2.2⟩, hinitial, htrace, hmu, hmem, hbu,
    hsu, hlu, hru, hformula, hinside, fun _ ↦ hentropy⟩

end PDE.Hyperbolic.ConservationLaw.System
