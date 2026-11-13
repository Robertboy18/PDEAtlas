/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.LocalBranches

/-!
# Continuity at simple knots

Every positive-degree Cox–de Boor basis is continuous at a knot with two
nondegenerate neighboring cells. This also gives continuity of finite spline sums
without assumptions on their coefficients.
-/

@[expose] public section

namespace CAS.Splines

open Set

noncomputable section

/-- Positive-degree polynomial branches have a common value at a simple knot. -/
theorem coxDeBoorBranch_value_match (knots : KnotSequence) (cell degree index : ℕ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2)) :
    coxDeBoorBranch knots cell (degree + 1) index (knots (cell + 1)) =
      coxDeBoorBranch knots (cell + 1) (degree + 1) index (knots (cell + 1)) := by
  induction degree generalizing index with
  | zero =>
      by_cases hi : index = cell
      · subst index
        simp [coxDeBoorBranch, leftBlendWeight, rightBlendWeight,
          ne_of_gt (sub_pos.mpr hleft), ne_of_gt (sub_pos.mpr hright)]
      · by_cases hip : index + 1 = cell
        · have hir : index ≠ cell + 1 := by omega
          have hi2 : index + 2 = cell + 1 := by omega
          simp [coxDeBoorBranch, hi, hip, hir, rightBlendWeight, hi2]
        · by_cases hir : index = cell + 1
          · subst index
            simp [coxDeBoorBranch, leftBlendWeight, hip]
          · simp [coxDeBoorBranch, hi, hip, hir]
  | succ degree ih =>
      simp only [coxDeBoorBranch.eq_2 (degree := degree + 1), ih]

/-- A positive-degree basis is continuous where adjacent knot cells are nondegenerate. -/
theorem continuousAt_coxDeBoorBasis_of_simple_knot (knots : KnotSequence)
    (cell degree index : ℕ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2)) :
    ContinuousAt (coxDeBoorBasis knots (degree + 1) index) (knots (cell + 1)) := by
  have hglue := continuousAt_branch_glue
    (hasDerivAt_coxDeBoorBranch knots cell (degree + 1) index _).continuousAt
    (hasDerivAt_coxDeBoorBranch knots (cell + 1) (degree + 1) index _).continuousAt
    (coxDeBoorBranch_value_match knots cell degree index hleft hright)
  apply hglue.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hright] with x hxleft hxright
  split_ifs with hx
  · exact coxDeBoorBasis_eq_branch knots cell (degree + 1) index ⟨hxleft.le, hx⟩
  · exact coxDeBoorBasis_eq_branch knots (cell + 1) (degree + 1) index
      ⟨le_of_not_gt hx, by simpa only [Nat.add_assoc] using hxright⟩

/-- Finite spline sums inherit continuity at a simple knot, for arbitrary coefficients. -/
theorem continuousAt_spline_sum_of_simple_knot (knots : KnotSequence)
    (cell degree : ℕ) (indices : Finset ℕ) (coefficients : ℕ → ℝ)
    (hleft : knots cell < knots (cell + 1))
    (hright : knots (cell + 1) < knots (cell + 2)) :
    ContinuousAt (fun x ↦ ∑ i ∈ indices, coxDeBoorBasis knots (degree + 1) i x *
      coefficients i) (knots (cell + 1)) := by
  apply tendsto_finsetSum indices
  intro i _
  exact (continuousAt_coxDeBoorBasis_of_simple_knot knots cell degree i hleft hright).mul
    continuousAt_const

end

end CAS.Splines
