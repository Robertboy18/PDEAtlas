/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.TraceSpaceEquiv

/-!
# Identification of the C¹ quotient trace space

For a fixed operational C¹ atlas, `traceSpaceEquiv` identifies the quotient of
`H¹(Ω)` by the physical trace kernel with the Hilbert space of compatible
half-order chart data (`Trace.C1.Fractional.TraceSpaceEquiv`).

The equivalence preserves the physical surface L² value. The
kernel representative and the constructed lifting give the two norm bounds.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open ContinuousLinearMap.KernelQuotient
open scoped Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The quotient and fractional descriptions have the same physical surface L² value. -/
@[simp]
theorem boundaryValue_traceSpaceEquiv (q : Trace.C1.HilbertTraceSpace (Ω := Ω)) :
    boundaryValue (traceSpaceEquiv q) = Trace.C1.boundaryValue q := by
  obtain ⟨u, rfl⟩ := (trace (Ω := Ω)).ker.mkQ_surjective q
  exact boundaryValue_fractionalTrace u

/-- Passing from fractional data to their quotient class preserves the physical boundary value. -/
@[simp]
theorem boundaryValue_traceSpaceEquiv_symm (g : HalfOrderBoundarySpace (Ω := Ω)) :
    Trace.C1.boundaryValue ((traceSpaceEquiv (Ω := Ω)).symm g) = boundaryValue g := by
  rw [traceSpaceEquiv_symm_apply]
  exact trace_lifting g

/-- The fractional norm is bounded by the quotient norm with the fractional trace constant. -/
theorem norm_traceSpaceEquiv_le (q : Trace.C1.HilbertTraceSpace (Ω := Ω)) :
    ‖traceSpaceEquiv q‖ ≤ ‖fractionalTrace (Ω := Ω)‖ * ‖q‖ := by
  have h := (fractionalTrace (Ω := Ω)).le_opNorm (representative (trace (Ω := Ω)) q)
  rw [norm_representative] at h
  have hq := congrArg (traceSpaceEquiv (Ω := Ω)) (mk_representative (trace (Ω := Ω)) q)
  change fractionalTrace (representative (trace (Ω := Ω)) q) = traceSpaceEquiv q at hq
  rwa [hq] at h

/-- The quotient norm is no greater than the norm of the constructed lifting. -/
theorem norm_traceSpaceEquiv_symm_le_norm_lifting (g : HalfOrderBoundarySpace (Ω := Ω)) :
    ‖(traceSpaceEquiv (Ω := Ω)).symm g‖ ≤ ‖lifting g‖ := by
  rw [traceSpaceEquiv_symm_apply]
  exact Submodule.Quotient.norm_mk_le (trace (Ω := Ω)).ker (lifting g)

/-- The quotient norm is bounded by the fractional norm with the lifting constant. -/
theorem norm_traceSpaceEquiv_symm_le (g : HalfOrderBoundarySpace (Ω := Ω)) :
    ‖(traceSpaceEquiv (Ω := Ω)).symm g‖ ≤ ‖lifting (Ω := Ω)‖ * ‖g‖ :=
  (norm_traceSpaceEquiv_symm_le_norm_lifting g).trans ((lifting (Ω := Ω)).le_opNorm g)

/-- The fractional trace-space norm controls the original quotient norm. -/
theorem norm_le_norm_traceSpaceEquiv (q : Trace.C1.HilbertTraceSpace (Ω := Ω)) :
    ‖q‖ ≤ ‖lifting (Ω := Ω)‖ * ‖traceSpaceEquiv q‖ := by
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    norm_traceSpaceEquiv_symm_le (traceSpaceEquiv q)

end SobolevSpace.Trace.C1.Fractional
