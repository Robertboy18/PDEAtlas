/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Lifting
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.TraceSpace

/-!
# The C¹ quotient trace space as half-order boundary data

For a fixed operational C¹ atlas, the quotient of `H¹(Ω)` by the physical
trace kernel is continuously linearly equivalent to the Hilbert space of
compatible half-order chart data. The forward map descends the fractional
trace, and the inverse takes the quotient class of its bounded lifting.
`Trace.C1.Fractional.Identification` adds the physical surface L² values and
the two norm bounds.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open ContinuousLinearMap.KernelQuotient
open scoped Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Identify the quotient Hilbert trace space with half-order boundary data for the fixed atlas. -/
def traceSpaceEquiv :
    Trace.C1.HilbertTraceSpace (Ω := Ω) ≃L[ℝ] HalfOrderBoundarySpace (Ω := Ω) :=
  let forward := (trace (Ω := Ω)).ker.liftQL (fractionalTrace (Ω := Ω))
    (le_of_eq (ker_fractionalTrace (Ω := Ω)).symm)
  let backward := (Trace.C1.traceClass (Ω := Ω)).comp (lifting (Ω := Ω))
  ContinuousLinearEquiv.equivOfInverse forward backward
    (by
      intro q
      obtain ⟨u, rfl⟩ := (trace (Ω := Ω)).ker.mkQ_surjective q
      change Submodule.Quotient.mk (lifting (fractionalTrace u)) =
        (Submodule.Quotient.mk u : Trace.C1.HilbertTraceSpace (Ω := Ω))
      rw [Submodule.Quotient.eq, ← ker_fractionalTrace (Ω := Ω)]
      change fractionalTrace (lifting (fractionalTrace u) - u) = 0
      rw [map_sub, fractionalTrace_lifting, sub_self])
    (by
      intro g
      exact fractionalTrace_lifting g)

/-- The equivalence sends a trace class to the fractional trace of its representative. -/
@[simp]
theorem traceSpaceEquiv_traceClass (u : H¹(Ω)) :
    traceSpaceEquiv (Trace.C1.traceClass u) = fractionalTrace u := rfl

/-- The inverse is the quotient class of the constructed H¹ lifting. -/
@[simp ←]
theorem traceSpaceEquiv_symm_apply (g : HalfOrderBoundarySpace (Ω := Ω)) :
    (traceSpaceEquiv (Ω := Ω)).symm g = Trace.C1.traceClass (lifting g) := rfl

end SobolevSpace.Trace.C1.Fractional
