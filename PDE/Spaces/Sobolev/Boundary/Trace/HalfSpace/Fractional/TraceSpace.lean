/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Operator

/-!
# Identification of the half-space trace range with real `H^{1/2}`

The physical `L²` trace has precisely the range of the real Bessel
boundary realization. Its quotient Hilbert space is continuously linearly
equivalent to `H^{1/2}`, preserving that physical realization. The explicit
lifting and the trace estimate give both norm comparisons.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Trace.HalfSpace.Fractional

open SobolevSpace.Fractional SobolevSpace.Fractional.Trace
open ContinuousLinearMap.KernelQuotient

/-- The bounded lift realizes the prescribed fractional datum as a physical trace. -/
theorem trace_fractionalLifting (n : ℕ) (v : HsSpaceReal n (1 / 2)) :
    trace n (fractionalLifting n v) =
      HsSpaceReal.toL2FunCLM n (by norm_num : (0 : ℝ) ≤ 1 / 2) v := by
  rw [← physical_fractionalTrace, fractionalTrace_fractionalLifting]

/-- The range of the physical trace is exactly the real fractional boundary space
as a subspace of physical `L²`. -/
theorem range_trace_eq_range_fractionalL2 (n : ℕ) :
    Set.range (trace n) =
      Set.range (HsSpaceReal.toL2FunCLM n (by norm_num : (0 : ℝ) ≤ 1 / 2)) := by
  ext f
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨fractionalTrace n u, physical_fractionalTrace n u⟩
  · rintro ⟨v, rfl⟩
    exact ⟨fractionalLifting n v, trace_fractionalLifting n v⟩

/-- The fractional trace descends through the kernel of the physical trace. -/
def traceSpaceToFractional (n : ℕ) : HilbertTraceSpace n →L[ℝ] HsSpaceReal n (1 / 2) :=
  (trace n).ker.liftQL (fractionalTrace n) (le_of_eq (ker_fractionalTrace n).symm)

/-- The quotient class of the explicit lifting. -/
def fractionalToTraceSpace (n : ℕ) : HsSpaceReal n (1 / 2) →L[ℝ] HilbertTraceSpace n :=
  (traceClass n).comp (fractionalLifting n)

/-- The induced map sends a class to its fractional trace. -/
theorem traceSpaceToFractional_traceClass (n : ℕ) (u : UpperH1 n) :
    traceSpaceToFractional n (traceClass n u) = fractionalTrace n u := rfl

/-- The quotient lifting is a right inverse of the induced fractional trace. -/
theorem traceSpaceToFractional_fractionalToTraceSpace (n : ℕ)
    (v : HsSpaceReal n (1 / 2)) :
    traceSpaceToFractional n (fractionalToTraceSpace n v) = v :=
  fractionalTrace_fractionalLifting n v

/-- Lifting the trace of a class returns the same class because their physical traces agree. -/
theorem fractionalToTraceSpace_traceSpaceToFractional (n : ℕ) (q : HilbertTraceSpace n) :
    fractionalToTraceSpace n (traceSpaceToFractional n q) = q := by
  obtain ⟨u, rfl⟩ := (trace n).ker.mkQ_surjective q
  change Submodule.Quotient.mk (fractionalLifting n (fractionalTrace n u)) =
    (Submodule.Quotient.mk u : HilbertTraceSpace n)
  rw [Submodule.Quotient.eq]
  change trace n (fractionalLifting n (fractionalTrace n u) - u) = 0
  rw [map_sub, sub_eq_zero, trace_fractionalLifting, physical_fractionalTrace]

/-- The quotient Hilbert trace space is continuously linearly equivalent to
the real Fourier-defined `H^{1/2}` boundary space. -/
def traceSpaceEquiv (n : ℕ) : HilbertTraceSpace n ≃L[ℝ] HsSpaceReal n (1 / 2) :=
  ContinuousLinearEquiv.equivOfInverse (traceSpaceToFractional n) (fractionalToTraceSpace n)
    (fractionalToTraceSpace_traceSpaceToFractional n)
    (traceSpaceToFractional_fractionalToTraceSpace n)

/-- The trace-space equivalence preserves the original physical boundary realization. -/
theorem physical_traceSpaceEquiv (n : ℕ) (q : HilbertTraceSpace n) :
    HsSpaceReal.toL2FunCLM n (by norm_num : (0 : ℝ) ≤ 1 / 2) (traceSpaceEquiv n q) =
      boundaryValue n q := by
  obtain ⟨u, rfl⟩ := (trace n).ker.mkQ_surjective q
  exact physical_fractionalTrace n u

/-- The Bessel norm of a trace class is bounded by its quotient norm, with the constant
already proved for reflection extension and the Fourier trace. -/
theorem norm_traceSpaceEquiv_le (n : ℕ) (q : HilbertTraceSpace n) :
    ‖traceSpaceEquiv n q‖ ≤
      (Real.sqrt Real.pi * ‖(h1GraphEquiv (n + 1)).symm.toContinuousLinearMap‖ *
        ‖Extension.GraphSpace.HalfSpace.extendCLM (n := n + 1) (p := 2)‖) * ‖q‖ := by
  have h := norm_fractionalTrace_le n (representative (trace n) q)
  rw [norm_representative] at h
  have hq := congrArg (traceSpaceToFractional n) (mk_representative (trace n) q)
  change fractionalTrace n (representative (trace n) q) = traceSpaceEquiv n q at hq
  rwa [hq] at h

/-- Conversely, the quotient norm of boundary data is bounded by the norm of its explicit
lifting, giving the other direction of the trace norm comparison. -/
theorem norm_traceSpaceEquiv_symm_le (n : ℕ) (v : HsSpaceReal n (1 / 2)) :
    ‖(traceSpaceEquiv n).symm v‖ ≤
      (‖(h1GraphEquiv (n + 1)).toContinuousLinearMap‖ * (Real.sqrt Real.pi)⁻¹) * ‖v‖ := by
  change ‖(trace n).ker.mkQL (fractionalLifting n v)‖ ≤ _
  exact (Submodule.Quotient.norm_mk_le (trace n).ker (fractionalLifting n v)).trans
    (norm_fractionalLifting_le n v)

/-- The quotient norm and the `H^{1/2}` norm control each other. -/
theorem traceSpace_norm_comparisons (n : ℕ) (q : HilbertTraceSpace n) :
    ‖traceSpaceEquiv n q‖ ≤
        (Real.sqrt Real.pi * ‖(h1GraphEquiv (n + 1)).symm.toContinuousLinearMap‖ *
          ‖Extension.GraphSpace.HalfSpace.extendCLM (n := n + 1) (p := 2)‖) * ‖q‖ ∧
      ‖q‖ ≤ (‖(h1GraphEquiv (n + 1)).toContinuousLinearMap‖ * (Real.sqrt Real.pi)⁻¹) *
        ‖traceSpaceEquiv n q‖ := by
  refine ⟨norm_traceSpaceEquiv_le n q, ?_⟩
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    norm_traceSpaceEquiv_symm_le n (traceSpaceEquiv n q)

end SobolevSpace.Trace.HalfSpace.Fractional
