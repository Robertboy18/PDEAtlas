/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.WeakHarmonic
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Existence

/-!
# Weak normal traces for constructed Green correctors

The C¹-domain solver of `Corrector.Existence` supplies the harmonic corrector, its H¹ class,
and its continuous boundary values. The quotient construction then gives its
bounded outward weak normal trace. Neither a solution nor boundary derivative
is assumed. The conclusion is a functional on the Hilbert trace space, not the
surface-integrable normal derivative appearing in the classical Green formula.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev InnerProductSpace

namespace PotentialTheory.GreenFunction.Domain

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Trace.C1 SobolevSpace.Boundary

/-- Every interior pole of a bounded C¹ graph domain has a continuous harmonic
corrector with a bounded weak normal trace on the quotient trace space.
The operational atlas in the conclusion is constructed from the geometric hypotheses. -/
theorem exists_harmonic_corrector_with_weakNormalTrace_of_local_graph
    {m : ℕ} {Ω : Set ℝ^(m + 1)} (hn : 2 ≤ m + 1)
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
    letI := hgraph.c1ExtensionAtlas hΩ hbounded
    ∃ U : H¹(Ω), ∃ φ : ℝ^(m + 1) → ℝ,
      ∃ N : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ,
        baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ ∧
        LaplacianEquation.IsHarmonicPDE (m + 1) φ Ω ∧
        ContinuousOn φ (closure Ω) ∧
        EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) ∧
        (∀ t : H¹₀(Ω),
          (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
            (derivCoordCLM i t)) = 0) ∧
        (∀ V : H¹(Ω), N (traceClass V) = inner ℝ (∇ U) (∇ V)) ∧
        ‖N‖ ≤ ‖∇ U‖ := by
  let := hgraph.c1ExtensionAtlas hΩ hbounded
  obtain ⟨U, φ, hU, hh, hc, hb, hw⟩ :=
    exists_harmonic_corrector_of_local_graph hn hΩ hbounded hgraph hx
  exact ⟨U, φ, weakHarmonicNormalTrace U hw, hU, hh, hc, hb, hw,
    weakHarmonicNormalTrace_traceClass U hw, norm_weakHarmonicNormalTrace_le U hw⟩

end PotentialTheory.GreenFunction.Domain
