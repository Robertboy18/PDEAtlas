/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Harmonic.ContinuousBoundary
public import PDE.Elliptic.PotentialTheory.FundamentalSolution
import PDE.Analysis.Calculus.LocalExtension.Punctured

/-!
# Constructing the harmonic corrector on a C¹ domain

On a bounded open domain with C¹ graph boundary, `exists_harmonic_corrector_of_local_graph`
constructs, for each pole `x` in the domain, a solution `φ` of Evans's corrector problem (26) in
§2.2.4(a): `φ` is harmonic in the domain, continuous on the closure and equal to `Φ(y - x)` on the
boundary, and it is almost everywhere equal to a weakly harmonic `H¹` function. The logarithmic
kernel in dimension two is included, and the domain need not be connected. Classical boundary
gradients need the stronger geometry of `Corrector.ClassicalBoundary`.

## How it works

Evans takes the corrector as given and computes it explicitly only for the half-space and the unit
ball. We construct it. `ContDiffOn.exists_contDiff_compactSupport_eq_away_pole` changes the
fundamental solution inside a ball about the pole into a smooth compactly supported function equal
to `Φ(· - x)` on the closure outside the ball, which is an `H¹` lifting of the boundary values.
`SobolevSpace.GraphSpace.exists_continuous_harmonic_extension_of_local_graph` adds an `H¹₀` field
that makes the lifting weakly harmonic; Weyl's lemma gives the classical harmonic representative,
and the C¹ barriers of `PDE.Elliptic.BoundaryContinuity.tendsto_at_boundary_of_c1Domain` give its
boundary values.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the corrector problem (26), p. 34, and the remark
  after Theorem 12, p. 35; §2.2.4(b), the corrector for the half-space, p. 36; §2.2.4(c), the
  corrector (39) for the unit ball, p. 39.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

namespace PotentialTheory.GreenFunction.Domain

open Filter MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary
open scoped ENNReal InnerProductSpace Topology

/-- A bounded open C¹ graph domain has the harmonic corrector for every
interior fundamental pole. Its continuous closure representative belongs to the
H¹ space and takes the fundamental-solution values on the whole boundary. -/
theorem exists_harmonic_corrector_of_local_graph
    {m : ℕ} {Ω : Set ℝ^(m + 1)} (hn : 2 ≤ m + 1)
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω)
    {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
    ∃ U : H¹(Ω), ∃ φ : ℝ^(m + 1) → ℝ,
      baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ ∧
      LaplacianEquation.IsHarmonicPDE (m + 1) φ Ω ∧
      ContinuousOn φ (closure Ω) ∧
      EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) ∧
      ∀ t : H¹₀(Ω),
        (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
          (derivCoordCLM i t)) = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hkernel : ContDiffOn ℝ (⊤ : ℕ∞) (fundamentalSolution (m + 1)) {0}ᶜ :=
    fun y hy ↦ (contDiffAt_fundamentalSolution (m + 1) y hy).contDiffWithinAt
  obtain ⟨A, hA, hAc, heq⟩ := hkernel.exists_contDiff_compactSupport_eq_away_pole
    hbounded x hr
  let G : H¹(Ω) := mkWkpSpaceOnOfContDiff A hA hAc
  have hG : baseRepresentative G =ᵐ[domainMeasure (m + 1) Ω] A := by
    simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (k := 1) (p := 2) (Ω := Ω) A hA hAc
        (baseIndex (m + 1) 1)
  obtain ⟨w, φ, hc, hh, hb, hU, hw⟩ := exists_continuous_harmonic_extension_of_local_graph
    hn hΩ hbounded hgraph G hA.continuous.continuousOn hG
  refine ⟨G + (w : H¹(Ω)), φ, hU, hh, hc, ?_, hw⟩
  intro y hy
  rw [hb hy]
  apply (heq y (frontier_subset_closure hy) ?_).eq_of_nhds
  by_contra! hnear
  have hyΩ : y ∈ Ω := hball (show y ∈ ball x r by
    simpa only [mem_ball, dist_eq_norm] using hnear)
  rw [hΩ.frontier_eq] at hy
  exact hy.2 hyΩ

end PotentialTheory.GreenFunction.Domain
