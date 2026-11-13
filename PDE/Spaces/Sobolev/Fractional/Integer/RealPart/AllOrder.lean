/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.Complex
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction

/-!
# Real weak derivatives from integer Bessel regularity

Taking the real part of a complex integer Sobolev distribution gives a real
weak-derivative graph of the same order. The complex graph equivalence constructs
all derivatives; no classical representative or prior real-valuedness is needed.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace.GraphSpace TemperedDistribution
open scoped Sobolev SchwartzMap

namespace SobolevSpace.Fractional

variable {n k : ℕ}

/-- The real part of a complex `H^k` distribution has all weak derivatives
through order `k` in real L². -/
theorem exists_wkpSpaceOn_re_of_memSobolev
    (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hu : MemSobolev (k : ℝ) 2 (u : 𝓢'(ℝ^n, ℂ))) :
    ∃ U : W^{k,2}(ℝ^n),
      (wkpBaseCoordinateCLM U : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ (u x).re := by
  obtain ⟨U, hU⟩ := (exists_complexWkSpace_iff_memSobolev u).mpr hu
  refine ⟨U.re, ?_⟩
  have hr := Complex.reCLM.coeFn_compLpL (U.1 (baseIndex n k))
  simp only [domainMeasure, Measure.restrict_univ] at hr
  filter_upwards [hr, hU] with x hx hy
  exact hx.trans (congrArg Complex.re hy)

end SobolevSpace.Fractional
