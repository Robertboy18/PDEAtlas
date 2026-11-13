/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Fractional.Lifting.Operator
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Fractional.Lifting.Trace
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Fractional.Gagliardo

/-!
# The lifting is a right inverse of the trace

The extension's positive-height averages converge to its boundary datum.
They also converge to the Sobolev trace. The two limits agree, first as
physical `Lᵖ` classes and then in the fractional graph. Every fractional
datum is therefore the trace of a Sobolev function.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open Approximation Fractional

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The physical trace of the lifting agrees almost everywhere with its boundary datum. -/
theorem traceLp_mollifiedLifting_ae (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    (traceLp n p hp.le (mollifiedLifting μ hp g) : ℝ^n → F) =ᵐ[volume]
      (GagliardoSpace.toLp n (1 - 1 / p) univ g : ℝ^n → F) := by
  apply coeFn_traceLp_eq_of_base_ae_mollifiedExtension μ hp
    (U := mollifiedLifting μ hp g)
  · simpa only [Measure.restrict_univ] using
      Lp.memLp (GagliardoSpace.toLp n (1 - 1 / p) univ g)
  · exact mollifiedLifting_base_ae μ hp g

/-- Taking the fractional trace after lifting recovers the original datum. -/
@[simp]
theorem traceGagliardo_mollifiedLifting (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    traceGagliardo n p hp (mollifiedLifting μ hp g) = g := by
  apply GagliardoSpace.toLp_injective
  apply Lp.ext
  simpa only [Measure.restrict_univ] using
    (toLp_traceGagliardo_apply_ae n p hp (mollifiedLifting μ hp g)).trans
      (traceLp_mollifiedLifting_ae μ hp g)

/-- The trace and lifting compose to the identity as bounded linear maps. -/
theorem traceGagliardo_comp_mollifiedLifting (μ : Mollifier n) (hp : 1 < p) :
    (traceGagliardo (F := F) n p hp).comp (mollifiedLifting μ hp) = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro g
  exact traceGagliardo_mollifiedLifting μ hp g

/-- Every intrinsic fractional boundary datum occurs as a `W¹ᵖ` trace. -/
theorem traceGagliardo_surjective (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) :
    Function.Surjective (traceGagliardo (F := F) n p hp) :=
  fun g ↦ ⟨mollifiedLifting (standardMollifier n) hp g,
    traceGagliardo_mollifiedLifting (standardMollifier n) hp g⟩

end SobolevSpace.VectorValued.Trace.HalfSpace
