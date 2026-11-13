/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Existence
public import PDE.Elliptic.Classical.Harmonic.BoundaryUniqueness

/-!
# Independence of the harmonic corrector construction

`exists_unique_harmonic_corrector_of_local_graph` adds uniqueness to the corrector of
`exists_harmonic_corrector_of_local_graph`: every harmonic function continuous on the closure with
boundary values `Φ(y - x)` agrees with it on the closure. Any two choices of pole cutoff, smooth
lifting or weak solver therefore give the same corrector, and the competing function need not come
from a Sobolev field. The uniqueness is Evans's §2.2.3(a), Theorem 5, for Laplace's equation with
boundary data `Φ(· - x)`; we obtain it from
`LaplacianEquation.IsHarmonicPDE.eqOn_closure_of_boundary_eq`, which needs no connectedness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3(a), Theorem 5 (Uniqueness), p. 28; §2.2.4(a), the
  corrector problem (26), p. 34.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

namespace PotentialTheory.GreenFunction.Domain

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary
open scoped ENNReal

/-- The constructed corrector is unique among all classical harmonic
functions continuous on the closure with the fundamental boundary values. -/
theorem exists_unique_harmonic_corrector_of_local_graph
    {m : ℕ} {Ω : Set ℝ^(m + 1)} (hn : 2 ≤ m + 1)
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
    ∃ U : H¹(Ω), ∃ φ : ℝ^(m + 1) → ℝ,
      baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ ∧
      LaplacianEquation.IsHarmonicPDE (m + 1) φ Ω ∧
      ContinuousOn φ (closure Ω) ∧
      EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) ∧
      ∀ ψ : ℝ^(m + 1) → ℝ,
        LaplacianEquation.IsHarmonicPDE (m + 1) ψ Ω →
        ContinuousOn ψ (closure Ω) →
        EqOn ψ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) →
        EqOn ψ φ (closure Ω) := by
  obtain ⟨U, φ, hU, hh, hc, hb, _⟩ :=
    exists_harmonic_corrector_of_local_graph hn hΩ hbounded hgraph hx
  refine ⟨U, φ, hU, hh, hc, hb, ?_⟩
  intro ψ hψ hψc hψb
  exact hψ.eqOn_closure_of_boundary_eq hh hΩ hbounded hψc hc
    (fun y hy ↦ (hψb hy).trans (hb hy).symm)

end PotentialTheory.GreenFunction.Domain
