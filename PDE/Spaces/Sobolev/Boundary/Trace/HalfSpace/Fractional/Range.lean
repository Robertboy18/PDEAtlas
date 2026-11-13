/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.RightInverse

/-!
# The range of the finite-exponent trace

A boundary function occurs as a `W¹ᵖ` trace exactly when it satisfies the
intrinsic fractional condition of order `1 - 1 / p`. The forward trace
estimate and the bounded mollified lifting prove the two directions.
The same identification holds inside boundary `Lᵖ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.Trace.HalfSpace

open Approximation Fractional

variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The intrinsic fractional condition characterizes physical boundary traces.
The equality is almost everywhere, as it must be for Sobolev data. -/
theorem memGagliardo_iff_exists_traceLp (hp : 1 < p) (g : ℝ^n → ℝ) :
    MemGagliardo n (1 - 1 / p) univ g (p := ENNReal.ofReal p) ↔
      ∃ u : W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊),
        (traceLp n p hp.le u : ℝ^n → ℝ) =ᵐ[volume] g := by
  constructor
  · intro hg
    refine ⟨mollifiedLifting (standardMollifier n) hp
      (GagliardoSpace.ofFunction g hg), ?_⟩
    refine (traceLp_mollifiedLifting_ae (standardMollifier n) hp
      (GagliardoSpace.ofFunction g hg)).trans ?_
    simpa only [Measure.restrict_univ] using
      GagliardoSpace.toLp_ofFunction_apply_ae g hg
  · rintro ⟨u, hu⟩
    apply (memGagliardo_traceLp n p hp u).congr_ae
    simpa only [Measure.restrict_univ] using hu

/-- Inside boundary `Lᵖ`, the trace range is exactly the Gagliardo operator domain.
Restriction to `univ` accounts for the graph's boundary-measure convention. -/
theorem range_restrict_traceLp_eq_gagliardoDomain (hp : 1 < p) :
    LinearMap.range
        ((Lp.restrictionCLMOfLE
          (Measure.restrict_le_self :
            (volume : Measure ℝ^n).restrict univ ≤ volume)).comp
              (traceLp n p hp.le)).toLinearMap =
      gagliardoDomain n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := ℝ) := by
  rw [← toLp_comp_traceGagliardo n p hp, ← GagliardoSpace.range_toLp]
  apply le_antisymm
  · rintro f ⟨u, rfl⟩
    exact ⟨traceGagliardo n p hp u, rfl⟩
  · rintro f ⟨g, rfl⟩
    refine ⟨mollifiedLifting (standardMollifier n) hp g, ?_⟩
    change GagliardoSpace.toLp n (1 - 1 / p) univ
      (traceGagliardo n p hp (mollifiedLifting (standardMollifier n) hp g)) = _
    rw [traceGagliardo_mollifiedLifting]
    rfl

end SobolevSpace.Trace.HalfSpace
