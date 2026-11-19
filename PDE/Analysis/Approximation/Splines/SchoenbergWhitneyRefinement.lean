/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.KnotRefinement
public import PDE.Analysis.Approximation.Splines.SchoenbergWhitney
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Positivity.Finset
import PDE.Analysis.Approximation.Splines.RepeatedKnotInsertion

/-!
# Geometric refinement for the Schoenberg–Whitney theorem

If strictly increasing sample points satisfy the Schoenberg–Whitney inequalities
`t_i < x_i < t_(i+p+1)`, the collocation matrix of a finite Cox–de Boor family of degree `p`
has positive determinant, for any nondecreasing knot sequence, including repeated knots. For
B-splines this is the case of the whole matrix in Theorem 2 of de Boor and DeVore. Schoenberg
and Whitney, Theorem 2, characterize unique interpolation by splines with simple knots,
written with truncated powers, by the interlacing inequalities (2.9).

## Main results

* `SchoenbergWhitneyCondition.det_collocation_pos`: the collocation determinant is positive.
* `SchoenbergWhitneyCondition.det_collocation_ne_zero`,
  `SchoenbergWhitneyCondition.linearIndependent`: the collocation matrix is nonsingular and the
  family is linearly independent.

## How it works

We follow de Boor and DeVore's proof of their Theorem 2. A `KnotRefinement` writes the coarse
collocation matrix as the refined one times a basis-change matrix whose ordered minors are
nonnegative, so by the Cauchy–Binet formula the coarse determinant is a sum of nonnegative
terms, as in their (4.4a), and one positive term suffices. Where they take any refinement fine
enough for (4.9), we insert each sample point `p + 1` times with `insertKnotRepeatedlyAfter`;
with the half-open convention of `coxDeBoorBasis`, the refined basis then takes the values of a
Kronecker selector at the sample points. In place of their explicit choice of the positive
term, the induction over the insertions keeps an increasing selection of refined rows on which
the minor of the basis-change matrix is positive (`KnotRefinement.PositiveSelection`).

## References

* I. J. Schoenberg and A. Whitney, "On Pólya frequency functions. III. The positivity of
  translation determinants with an application to the interpolation problem by spline curves",
  *Trans. Amer. Math. Soc.* 74 (1953), 246-259, (2.9), p. 257, and Theorem 2, p. 258.
  <https://doi.org/10.1090/S0002-9947-1953-0053177-X>
* C. de Boor and R. DeVore, "A geometric proof of total positivity for spline interpolation",
  *Math. Comp.* 45 (1985), no. 172, 497-504, Section 4, Theorem 2 and its proof, (4.2)-(4.9),
  pp. 500-502. <https://doi.org/10.1090/S0025-5718-1985-0804938-2>
* C. de Boor, *A Practical Guide to Splines*, revised edition, Applied Mathematical Sciences,
  Springer, 2001, Chapter XIII, Spline Interpolation, pp. 171-205.
  <https://doi.org/10.1007/978-1-4612-6333-3_13>
-/

@[expose] public section

namespace CAS.Splines

noncomputable section

/-- Shift an upper tail of an increasing finite index selection after one
new ambient coordinate is inserted. -/
private def shiftSelection {rowCount ambientCount : ℕ}
    (selection : Fin rowCount → Fin ambientCount) (cut : ℕ)
    (row : Fin rowCount) : Fin (ambientCount + 1) :=
  if row.val < cut then
    Fin.castSucc (selection row)
  else
    Fin.succ (selection row)

/-- Rows below the cut retain their selected index after an upper-tail shift. -/
@[simp]
private theorem shiftSelection_of_lt
    {rowCount ambientCount : ℕ}
    (selection : Fin rowCount → Fin ambientCount) (cut : ℕ)
    (row : Fin rowCount) (hrow : row.val < cut) :
    shiftSelection selection cut row =
      Fin.castSucc (selection row) := by
  simp [shiftSelection, hrow]

/-- Rows at or above the cut have their selected index incremented by an upper-tail shift. -/
@[simp]
private theorem shiftSelection_of_not_lt
    {rowCount ambientCount : ℕ}
    (selection : Fin rowCount → Fin ambientCount) (cut : ℕ)
    (row : Fin rowCount) (hrow : ¬row.val < cut) :
    shiftSelection selection cut row =
      Fin.succ (selection row) := by
  simp [shiftSelection, hrow]

/-- Shifting an upper tail by one preserves strict ordering. -/
private theorem shiftSelection_strictMono
    {rowCount ambientCount : ℕ}
    {selection : Fin rowCount → Fin ambientCount}
    (hselection : StrictMono selection) (cut : ℕ) :
    StrictMono (shiftSelection selection cut) := by
  intro left right hindex
  have hselected : (selection left).val < (selection right).val := hselection hindex
  have hindexVal : left.val < right.val := hindex
  change (shiftSelection selection cut left).val < (shiftSelection selection cut right).val
  unfold shiftSelection
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

/-- Numerical effect of shifting an upper selection tail. -/
private theorem shiftSelection_val
    {rowCount ambientCount : ℕ}
    (selection : Fin rowCount → Fin ambientCount) (cut : ℕ)
    (row : Fin rowCount) :
    (shiftSelection selection cut row).val =
      (selection row).val +
        if row.val < cut then 0 else 1 := by
  unfold shiftSelection
  split_ifs <;> simp

/-- Row shift accumulated after several repeated insertions around a pivot.

Rows below the pivot never move, rows above it move after every insertion,
and the pivot starts moving only after `diagonalCount` insertions. -/
private def clampingShift {count : ℕ}
    (pivot diagonalCount repetitions : ℕ)
    (row : Fin count) : ℕ :=
  if row.val < pivot then
    0
  else if row.val = pivot then
    repetitions - diagonalCount
  else
    repetitions

/-- Cut used at one step of the repeated-insertion schedule. -/
private def clampingCut
    (pivot diagonalCount repetitions : ℕ) : ℕ :=
  if repetitions < diagonalCount then pivot + 1 else pivot

/-- The accumulated shift obeys the one-step upper-tail schedule. -/
private theorem clampingShift_succ
    {count pivot diagonalCount repetitions : ℕ}
    (row : Fin count) :
    clampingShift pivot diagonalCount (repetitions + 1) row =
      clampingShift pivot diagonalCount repetitions row +
        if row.val < clampingCut pivot diagonalCount repetitions
        then 0 else 1 := by
  unfold clampingShift clampingCut
  split_ifs <;> omega

/-- A degree-`degree` support is fully clamped on the left at `x`. -/
private def LeftClampedAt
    (knots : KnotSequence) (degree index : ℕ) (x : ℝ) : Prop :=
  (∀ offset ≤ degree, knots (index + offset) = x) ∧
    x < knots (index + degree + 1)

/-- A point lies strictly inside the canonical support at `index`. -/
private def InteriorSupportAt
    (knots : KnotSequence) (degree index : ℕ) (x : ℝ) : Prop :=
  knots index < x ∧
    x < knots (index + degree + 1)

/-- At any interior support point there is a knot span crossing the point
between the support's first and last knots. -/
private theorem exists_crossingKnotPosition
    (knots : KnotSequence) :
    ∀ degree index x,
      InteriorSupportAt knots degree index x →
      ∃ position,
        index ≤ position ∧
          position ≤ index + degree ∧
          knots position ≤ x ∧
          x < knots (position + 1) := by
  suffices h : ∀ degree index x, knots index ≤ x → x < knots (index + degree + 1) →
      ∃ position, index ≤ position ∧ position ≤ index + degree ∧ knots position ≤ x ∧
        x < knots (position + 1) from
    fun degree index x hsupport ↦ h degree index x hsupport.1.le hsupport.2
  intro degree
  induction degree with
  | zero => exact fun index x hleft hright ↦ ⟨index, le_rfl, by omega, hleft, hright⟩
  | succ degree ih =>
    intro index x hleft hright
    by_cases hnext : x < knots (index + 1)
    · exact ⟨index, le_rfl, by omega, hleft, hnext⟩
    · obtain ⟨position, hindex, hposition, hpositionLeft, hpositionRight⟩ :=
        ih (index + 1) x (le_of_not_gt hnext) (by rwa [Nat.add_right_comm index 1 degree])
      exact ⟨position, by omega, by omega, hpositionLeft, hpositionRight⟩

/-- Refinement invariant after clamping the first `processed` sample
points. -/
private structure SchoenbergWhitneyRefinementState
    (coarseKnots : KnotSequence) (degree count : ℕ)
    (points : Fin count → ℝ) (processed : ℕ) where
  /-- Current iterated knot refinement. -/
  refinement : KnotRefinement coarseKnots degree count
  /-- Increasing refined rows carrying a positive refinement minor. -/
  positive : refinement.PositiveSelection
  /-- Processed points are fully left-clamped at their tracked rows. -/
  clamped_of_lt :
    ∀ index, index.val < processed →
      LeftClampedAt refinement.refinedKnots degree
        (positive.selection index).val (points index)
  /-- Unprocessed points remain in the interiors of their tracked supports. -/
  interior_of_le :
    ∀ index, processed ≤ index.val →
      InteriorSupportAt refinement.refinedKnots degree
        (positive.selection index).val (points index)

namespace SchoenbergWhitneyRefinementState

/-- Auxiliary data for a partially completed repeated insertion at one
sample point. -/
private structure RepeatedPositiveRefinement
    {coarseKnots : KnotSequence} {degree count : ℕ}
    (base : KnotRefinement coarseKnots degree count)
    (basePositive : base.PositiveSelection)
    (position : ℕ) (value : ℝ)
    (hleft : base.refinedKnots position ≤ value)
    (hright : value ≤ base.refinedKnots (position + 1))
    (pivot diagonalCount repetitions : ℕ) where
  /-- Refinement after `repetitions` copies. -/
  refinement : KnotRefinement coarseKnots degree count
  /-- Positive selected minor after those copies. -/
  positive : refinement.PositiveSelection
  /-- The recursive knot sequence agrees with the explicit repeated block. -/
  knots_eq :
    refinement.refinedKnots =
      insertKnotRepeatedlyAfter base.refinedKnots position value
        hleft hright repetitions
  /-- Every insertion adds one retained refined basis function. -/
  count_eq :
    refinement.refinedCount = base.refinedCount + repetitions
  /-- Selected row indices follow the clamping shift schedule. -/
  selection_val :
    ∀ row,
      (positive.selection row).val =
        (basePositive.selection row).val +
          clampingShift pivot diagonalCount repetitions row

namespace RepeatedPositiveRefinement

/-- Initial partial repeated refinement, before any copy is inserted. -/
private def zero
    {coarseKnots : KnotSequence} {degree count : ℕ}
    (base : KnotRefinement coarseKnots degree count)
    (basePositive : base.PositiveSelection)
    (position : ℕ) (value : ℝ)
    (hleft : base.refinedKnots position ≤ value)
    (hright : value ≤ base.refinedKnots (position + 1))
    (pivot diagonalCount : ℕ) :
    RepeatedPositiveRefinement base basePositive position value
      hleft hright pivot diagonalCount 0 where
  refinement := base
  positive := basePositive
  knots_eq := (insertKnotRepeatedlyAfter_zero
    base.refinedKnots position value hleft hright).symm
  count_eq := by simp
  selection_val := fun row ↦ by simp [clampingShift]

/-- Extend a partial repeated refinement by one copy, once positivity of
the selected one-step bidiagonal entries has been established. -/
private def next
    {coarseKnots : KnotSequence} {degree count : ℕ}
    {base : KnotRefinement coarseKnots degree count}
    {basePositive : base.PositiveSelection}
    {position : ℕ} {value : ℝ}
    {hleft : base.refinedKnots position ≤ value}
    {hright : value ≤ base.refinedKnots (position + 1)}
    {pivot diagonalCount repetitions : ℕ}
    (data :
      RepeatedPositiveRefinement base basePositive position value
        hleft hright pivot diagonalCount repetitions)
    (hentry : ∀ row,
      0 <
        knotInsertionMatrix data.refinement.refinedKnots degree
          (position + repetitions) value data.refinement.refinedCount
          (shiftSelection data.positive.selection
            (clampingCut pivot diagonalCount repetitions) row)
          (data.positive.selection row)) :
    RepeatedPositiveRefinement base basePositive position value
      hleft hright pivot diagonalCount (repetitions + 1) :=
  let hcurrentLeft : data.refinement.refinedKnots (position + repetitions) ≤ value := by
    rw [data.knots_eq]
    exact insertKnotRepeatedlyAfter_left_admissible _ _ _ hleft hright repetitions
  let hcurrentRight : value ≤ data.refinement.refinedKnots (position + repetitions + 1) := by
    rw [data.knots_eq]
    exact insertKnotRepeatedlyAfter_right_admissible _ _ _ hleft hright repetitions
  let nextSelection :=
    shiftSelection data.positive.selection (clampingCut pivot diagonalCount repetitions)
  let nextPositive :=
    data.positive.insertKnot (position + repetitions) value hcurrentLeft hcurrentRight
      nextSelection
      (shiftSelection_strictMono data.positive.strictMono
        (clampingCut pivot diagonalCount repetitions))
      hentry
  { refinement :=
      data.refinement.insertKnot (position + repetitions) value hcurrentLeft hcurrentRight
    positive := nextPositive
    knots_eq := (insertKnotAfter_congr _ _ data.knots_eq _ _ hcurrentLeft hcurrentRight _ _).trans
      (insertKnotRepeatedlyAfter_succ base.refinedKnots position value hleft hright
        repetitions).symm
    count_eq := by
      change data.refinement.refinedCount + 1 = _
      rw [data.count_eq]
      omega
    selection_val := fun row ↦ by
      change (shiftSelection data.positive.selection _ row).val = _
      rw [shiftSelection_val, data.selection_val, clampingShift_succ]
      omega }

end RepeatedPositiveRefinement

/-- The unrefined family is the initial geometric state. -/
private def initial
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (condition : SchoenbergWhitneyCondition knots degree count points) :
    SchoenbergWhitneyRefinementState
      knots degree count points 0 where
  refinement := KnotRefinement.refl knots degree count
  positive := KnotRefinement.PositiveSelection.refl knots degree count
  clamped_of_lt := fun _ hindex ↦ absurd hindex (Nat.not_lt_zero _)
  interior_of_le := fun index _ ↦ by
    simpa [KnotRefinement.PositiveSelection.refl, KnotRefinement.refl, InteriorSupportAt] using
      condition.mem_support_interior index

/-- Result of inserting the next sample point `degree + 1` times while
tracking a strictly positive refinement minor. -/
private structure PointClampingResult
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    (state :
      SchoenbergWhitneyRefinementState
        knots degree count points processed)
    (hprocessed : processed < count) where
  /-- Original knot span crossing the point being clamped. -/
  position : ℕ
  /-- The tracked support starts no later than that span. -/
  tracked_le_position :
    (state.positive.selection ⟨processed, hprocessed⟩).val ≤ position
  /-- The crossing span lies inside the tracked support. -/
  position_le_tracked_add_degree :
    position ≤
      (state.positive.selection ⟨processed, hprocessed⟩).val + degree
  /-- Left endpoint admissibility. -/
  left :
    state.refinement.refinedKnots position ≤
      points ⟨processed, hprocessed⟩
  /-- The point lies strictly before the span's right endpoint. -/
  right_strict :
    points ⟨processed, hprocessed⟩ <
      state.refinement.refinedKnots (position + 1)
  /-- Complete repeated refinement and its positive tracked minor. -/
  repeated :
    RepeatedPositiveRefinement
      state.refinement state.positive position
      (points ⟨processed, hprocessed⟩)
      left right_strict.le processed
      ((state.positive.selection ⟨processed, hprocessed⟩).val +
        degree - position)
      (degree + 1)

/-- Selected rows below the pivot stay on unit diagonal entries. -/
private theorem clampingEntry_pos_of_lt
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    {state : SchoenbergWhitneyRefinementState knots degree count points processed}
    {hprocessed : processed < count} {position repetitions : ℕ}
    {hleft : state.refinement.refinedKnots position ≤ points ⟨processed, hprocessed⟩}
    {hright : points ⟨processed, hprocessed⟩ <
      state.refinement.refinedKnots (position + 1)}
    (data : RepeatedPositiveRefinement state.refinement state.positive position
      (points ⟨processed, hprocessed⟩) hleft hright.le processed
      ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
      repetitions) (hpoints : StrictMono points)
    (row : Fin count) (hrowLower : row.val < processed) :
    0 < knotInsertionMatrix data.refinement.refinedKnots degree
      (position + repetitions) (points ⟨processed, hprocessed⟩)
      data.refinement.refinedCount
      (shiftSelection data.positive.selection
        (clampingCut processed
          ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
          repetitions) row)
      (data.positive.selection row) := by
  have hrowCut (d : ℕ) : row.val < clampingCut processed d repetitions := by
    unfold clampingCut
    split_ifs <;> omega
  rw [shiftSelection_of_lt _ _ row (hrowCut _), knotInsertionMatrix_castSucc_self]
  have hclamped := state.clamped_of_lt row hrowLower
  have hselectedBefore : (state.positive.selection row).val + degree ≤ position := by
    by_contra hnot
    have hknotLe := state.refinement.refinedKnots.monotone
      (show position + 1 ≤ (state.positive.selection row).val + degree by omega)
    rw [hclamped.1 degree le_rfl] at hknotLe
    exact not_lt_of_ge hknotLe
      ((hpoints (show row < ⟨processed, hprocessed⟩ from hrowLower)).trans hright)
  have hselection : (data.positive.selection row).val = (state.positive.selection row).val := by
    rw [data.selection_val]
    simp [clampingShift, hrowLower]
  rw [knotInsertionAlpha_eq_one_of_add_le _ _ _ _ (by omega)]
  exact zero_lt_one

/-- The pivot uses positive diagonal entries, then positive subdiagonal entries. -/
private theorem clampingEntry_pos_pivot
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    {state : SchoenbergWhitneyRefinementState knots degree count points processed}
    {hprocessed : processed < count} {position repetitions : ℕ}
    {hleft : state.refinement.refinedKnots position ≤ points ⟨processed, hprocessed⟩}
    {hright : points ⟨processed, hprocessed⟩ <
      state.refinement.refinedKnots (position + 1)}
    (data : RepeatedPositiveRefinement state.refinement state.positive position
      (points ⟨processed, hprocessed⟩) hleft hright.le processed
      ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
      repetitions)
    (htracked : (state.positive.selection ⟨processed, hprocessed⟩).val ≤ position)
    (hposition : position ≤
      (state.positive.selection ⟨processed, hprocessed⟩).val + degree) :
    0 < knotInsertionMatrix data.refinement.refinedKnots degree
      (position + repetitions) (points ⟨processed, hprocessed⟩)
      data.refinement.refinedCount
      (shiftSelection data.positive.selection
        (clampingCut processed
          ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
          repetitions) ⟨processed, hprocessed⟩)
      (data.positive.selection ⟨processed, hprocessed⟩) := by
  let pivot : Fin count := ⟨processed, hprocessed⟩
  let tracked := (state.positive.selection pivot).val
  let diagonalCount := tracked + degree - position
  change 0 < knotInsertionMatrix data.refinement.refinedKnots degree
    (position + repetitions) (points pivot) data.refinement.refinedCount
    (shiftSelection data.positive.selection
      (clampingCut processed diagonalCount repetitions) pivot)
    (data.positive.selection pivot)
  change tracked ≤ position at htracked
  change position ≤ tracked + degree at hposition
  have hcurrentLeft : data.refinement.refinedKnots (position + repetitions) ≤ points pivot := by
    rw [data.knots_eq]
    exact insertKnotRepeatedlyAfter_left_admissible _ _ _ hleft hright.le repetitions
  have hcurrentRight :
      points pivot ≤ data.refinement.refinedKnots (position + repetitions + 1) := by
    rw [data.knots_eq]
    exact insertKnotRepeatedlyAfter_right_admissible _ _ _ hleft hright.le repetitions
  by_cases hdiagonal : repetitions < diagonalCount
  · rw [shiftSelection_of_lt _ _ pivot (by simp [clampingCut, hdiagonal, pivot]),
      knotInsertionMatrix_castSucc_self]
    have hzero : repetitions - diagonalCount = 0 := Nat.sub_eq_zero_of_le hdiagonal.le
    dsimp only [diagonalCount, tracked, pivot] at hzero
    have hselection : (data.positive.selection pivot).val = tracked := by
      rw [data.selection_val]
      simp [clampingShift, pivot, tracked, hzero]
    refine knotInsertionAlpha_pos_of_le_position_of_lt _ _ _ _ hcurrentRight (by omega) ?_
    rw [data.knots_eq, hselection,
      insertKnotRepeatedlyAfter_knot_of_le _ _ _ hleft hright.le repetitions htracked]
    exact (state.interior_of_le pivot le_rfl).1
  · rw [shiftSelection_of_not_lt _ _ pivot (by simp [clampingCut, hdiagonal, pivot]),
      knotInsertionMatrix_succ_self]
    have hdiagIdentity : diagonalCount + position = tracked + degree :=
      Nat.sub_add_cancel hposition
    have hselection :
        (data.positive.selection pivot).val = tracked + (repetitions - diagonalCount) := by
      rw [data.selection_val]
      simp [clampingShift, pivot, tracked, diagonalCount]
    refine one_sub_knotInsertionAlpha_pos_of_position_lt_add _ _ _ _ hcurrentLeft (by omega) ?_
    rw [show (data.positive.selection pivot).val + 1 + degree = position + repetitions + 1 by
      omega, data.knots_eq, insertKnotRepeatedlyAfter_knot_after_block]
    exact hright

/-- Selected rows above the pivot follow strictly positive subdiagonal entries. -/
private theorem clampingEntry_pos_of_gt
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    {state : SchoenbergWhitneyRefinementState knots degree count points processed}
    {hprocessed : processed < count} {position repetitions : ℕ}
    {hleft : state.refinement.refinedKnots position ≤ points ⟨processed, hprocessed⟩}
    {hright : points ⟨processed, hprocessed⟩ <
      state.refinement.refinedKnots (position + 1)}
    (data : RepeatedPositiveRefinement state.refinement state.positive position
      (points ⟨processed, hprocessed⟩) hleft hright.le processed
      ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
      repetitions) (hpoints : StrictMono points)
    (row : Fin count) (hrowUpper : processed < row.val) :
    0 < knotInsertionMatrix data.refinement.refinedKnots degree
      (position + repetitions) (points ⟨processed, hprocessed⟩)
      data.refinement.refinedCount
      (shiftSelection data.positive.selection
        (clampingCut processed
          ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
          repetitions) row)
      (data.positive.selection row) := by
  have hcurrentLeft :
      data.refinement.refinedKnots (position + repetitions) ≤ points ⟨processed, hprocessed⟩ := by
    rw [data.knots_eq]
    exact insertKnotRepeatedlyAfter_left_admissible _ _ _ hleft hright.le repetitions
  have hrowCut (d : ℕ) : ¬row.val < clampingCut processed d repetitions := by
    unfold clampingCut
    split_ifs <;> omega
  rw [shiftSelection_of_not_lt _ _ row (hrowCut _), knotInsertionMatrix_succ_self]
  have hinterior := state.interior_of_le row (by omega)
  have hpointUpper : points ⟨processed, hprocessed⟩ < points row :=
    hpoints (show ⟨processed, hprocessed⟩ < row from hrowUpper)
  have hpositionBefore : position < (state.positive.selection row).val + degree + 1 := by
    by_contra hnot
    have hknotLe := state.refinement.refinedKnots.monotone
      (show (state.positive.selection row).val + degree + 1 ≤ position by omega)
    exact not_lt_of_ge (hknotLe.trans hleft) (hpointUpper.trans hinterior.2)
  have hselection :
      (data.positive.selection row).val = (state.positive.selection row).val + repetitions := by
    rw [data.selection_val]
    simp [clampingShift, show ¬row.val < processed by omega, show row.val ≠ processed by omega]
  refine one_sub_knotInsertionAlpha_pos_of_position_lt_add _ _ _ _ hcurrentLeft (by omega) ?_
  rw [show (data.positive.selection row).val + 1 + degree =
      (state.positive.selection row).val + degree + 1 + repetitions by omega, data.knots_eq,
    insertKnotRepeatedlyAfter_knot_of_gt _ _ _ hleft hright.le repetitions (by omega),
    Nat.add_sub_cancel]
  exact hpointUpper.trans hinterior.2

/-- Every selected entry in the insertion schedule is strictly positive. -/
private theorem clampingEntry_pos
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    {state : SchoenbergWhitneyRefinementState knots degree count points processed}
    {hprocessed : processed < count} {position repetitions : ℕ}
    {hleft : state.refinement.refinedKnots position ≤ points ⟨processed, hprocessed⟩}
    {hright : points ⟨processed, hprocessed⟩ <
      state.refinement.refinedKnots (position + 1)}
    (data : RepeatedPositiveRefinement state.refinement state.positive position
      (points ⟨processed, hprocessed⟩) hleft hright.le processed
      ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
      repetitions) (hpoints : StrictMono points)
    (htracked : (state.positive.selection ⟨processed, hprocessed⟩).val ≤ position)
    (hposition : position ≤
      (state.positive.selection ⟨processed, hprocessed⟩).val + degree)
    (row : Fin count) :
    0 < knotInsertionMatrix data.refinement.refinedKnots degree
      (position + repetitions) (points ⟨processed, hprocessed⟩)
      data.refinement.refinedCount
      (shiftSelection data.positive.selection
        (clampingCut processed
          ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
          repetitions) row)
      (data.positive.selection row) := by
  rcases lt_trichotomy row.val processed with hrow | hrow | hrow
  · exact clampingEntry_pos_of_lt (hright := hright) data hpoints row hrow
  · obtain rfl : row = ⟨processed, hprocessed⟩ := Fin.ext hrow
    exact clampingEntry_pos_pivot (hright := hright) data htracked hposition
  · exact clampingEntry_pos_of_gt (hright := hright) data hpoints row hrow


/-- Repeatedly insert one admissible crossing point along the positive selection schedule. -/
private def repeatAtSpan
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    (state : SchoenbergWhitneyRefinementState knots degree count points processed)
    (hprocessed : processed < count) (hpoints : StrictMono points)
    (position : ℕ)
    (htracked : (state.positive.selection ⟨processed, hprocessed⟩).val ≤ position)
    (hposition : position ≤
      (state.positive.selection ⟨processed, hprocessed⟩).val + degree)
    (hleft : state.refinement.refinedKnots position ≤ points ⟨processed, hprocessed⟩)
    (hright : points ⟨processed, hprocessed⟩ <
      state.refinement.refinedKnots (position + 1)) :
    (repetitions : ℕ) →
      RepeatedPositiveRefinement state.refinement state.positive position
        (points ⟨processed, hprocessed⟩) hleft hright.le processed
        ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
        repetitions
  | 0 => RepeatedPositiveRefinement.zero state.refinement state.positive position
      (points ⟨processed, hprocessed⟩) hleft hright.le processed
      ((state.positive.selection ⟨processed, hprocessed⟩).val + degree - position)
  | repetitions + 1 =>
      let data := repeatAtSpan state hprocessed hpoints position
        htracked hposition hleft hright repetitions
      data.next (clampingEntry_pos (hright := hright) data hpoints htracked hposition)

/-- Repeatedly insert the next sample point, using diagonal selected entries
before the tracked row reaches the crossing span and subdiagonal entries
afterward. -/
private def clampNextPoint
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    (state :
      SchoenbergWhitneyRefinementState
        knots degree count points processed)
    (hprocessed : processed < count)
    (hpoints : StrictMono points) :
    PointClampingResult state hprocessed :=
  let pivot : Fin count := ⟨processed, hprocessed⟩
  let crossing := exists_crossingKnotPosition state.refinement.refinedKnots degree
    (state.positive.selection pivot).val (points pivot) (state.interior_of_le pivot le_rfl)
  let position := crossing.choose
  let hcrossing := crossing.choose_spec
  { position := position
    tracked_le_position := hcrossing.1
    position_le_tracked_add_degree := hcrossing.2.1
    left := hcrossing.2.2.1
    right_strict := hcrossing.2.2.2
    repeated := repeatAtSpan state hprocessed hpoints position hcrossing.1 hcrossing.2.1
      hcrossing.2.2.1 hcrossing.2.2.2 (degree + 1) }

/-- Repeated insertion clamps the pivot and preserves all previously clamped rows. -/
private theorem PointClampingResult.clamped_of_lt
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    {state : SchoenbergWhitneyRefinementState knots degree count points processed}
    {hprocessed : processed < count}
    (result : PointClampingResult state hprocessed)
    (hpoints : StrictMono points) (row : Fin count) (hrow : row.val < processed + 1) :
    LeftClampedAt result.repeated.refinement.refinedKnots degree
      (result.repeated.positive.selection row).val (points row) := by
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ hrow) with hrowLower | hrowPivot
  · have hclamped := state.clamped_of_lt row hrowLower
    have hpointLower : points row < points ⟨processed, hprocessed⟩ :=
      hpoints (show row < ⟨processed, hprocessed⟩ from hrowLower)
    have hselectedBefore : (state.positive.selection row).val + degree ≤ result.position := by
      by_contra hnot
      have hknotLe := state.refinement.refinedKnots.monotone
        (show result.position + 1 ≤ (state.positive.selection row).val + degree by omega)
      rw [hclamped.1 degree le_rfl] at hknotLe
      exact not_lt_of_ge hknotLe (hpointLower.trans result.right_strict)
    have hselection :
        (result.repeated.positive.selection row).val = (state.positive.selection row).val := by
      rw [result.repeated.selection_val]
      simp [clampingShift, hrowLower]
    refine ⟨fun offset hoffset ↦ ?_, ?_⟩
    · rw [result.repeated.knots_eq, hselection, insertKnotRepeatedlyAfter_knot_of_le _ _ _
        result.left result.right_strict.le (degree + 1) (by omega)]
      exact hclamped.1 offset hoffset
    · rw [result.repeated.knots_eq, hselection]
      by_cases hbefore : (state.positive.selection row).val + degree + 1 ≤ result.position
      · rw [insertKnotRepeatedlyAfter_knot_of_le _ _ _ result.left result.right_strict.le
          (degree + 1) hbefore]
        exact hclamped.2
      · rw [show (state.positive.selection row).val + degree + 1 = result.position + 1 by omega,
          insertKnotRepeatedlyAfter_knot_of_mem_block _ _ _ result.left result.right_strict.le
            (degree + 1) (by omega) (by omega)]
        exact hpointLower
  · obtain rfl : row = ⟨processed, hprocessed⟩ := Fin.ext hrowPivot
    have htracked := result.tracked_le_position
    have hposition := result.position_le_tracked_add_degree
    have hselection :
        (result.repeated.positive.selection ⟨processed, hprocessed⟩).val =
          result.position + 1 := by
      rw [result.repeated.selection_val]
      simp only [clampingShift, lt_self_iff_false, ite_false, ite_true]
      omega
    refine ⟨fun offset hoffset ↦ ?_, ?_⟩
    · rw [result.repeated.knots_eq, hselection, insertKnotRepeatedlyAfter_knot_of_mem_block _ _ _
        result.left result.right_strict.le (degree + 1) (by omega) (by omega)]
    · rw [result.repeated.knots_eq, hselection,
        show result.position + 1 + degree + 1 = result.position + (degree + 1) + 1 by omega,
        insertKnotRepeatedlyAfter_knot_after_block]
      exact result.right_strict

/-- Rows above the new clamped pivot remain strictly inside their selected supports. -/
private theorem PointClampingResult.interior_of_le
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    {state : SchoenbergWhitneyRefinementState knots degree count points processed}
    {hprocessed : processed < count}
    (result : PointClampingResult state hprocessed)
    (hpoints : StrictMono points) (row : Fin count) (hrow : processed + 1 ≤ row.val) :
    InteriorSupportAt result.repeated.refinement.refinedKnots degree
      (result.repeated.positive.selection row).val (points row) := by
  have hselection : (result.repeated.positive.selection row).val =
      (state.positive.selection row).val + (degree + 1) := by
    rw [result.repeated.selection_val]
    simp [clampingShift, show ¬row.val < processed by omega, show row.val ≠ processed by omega]
  have hinterior := state.interior_of_le row (by omega)
  have hpointUpper : points ⟨processed, hprocessed⟩ < points row :=
    hpoints (show ⟨processed, hprocessed⟩ < row from hrow)
  have hpositionBefore : result.position < (state.positive.selection row).val + degree + 1 := by
    by_contra hnot
    have hknotLe := state.refinement.refinedKnots.monotone
      (show (state.positive.selection row).val + degree + 1 ≤ result.position by omega)
    exact not_lt_of_ge (hknotLe.trans result.left) (hpointUpper.trans hinterior.2)
  rw [result.repeated.knots_eq, hselection]
  constructor
  · by_cases hselected : (state.positive.selection row).val ≤ result.position
    · rw [insertKnotRepeatedlyAfter_knot_of_mem_block _ _ _ result.left result.right_strict.le
        (degree + 1) (by omega) (by omega)]
      exact hpointUpper
    · rw [insertKnotRepeatedlyAfter_knot_of_gt _ _ _ result.left result.right_strict.le
        (degree + 1) (by omega), Nat.add_sub_cancel]
      exact hinterior.1
  · rw [insertKnotRepeatedlyAfter_knot_of_gt _ _ _ result.left result.right_strict.le
      (degree + 1) (by omega),
      show (state.positive.selection row).val + (degree + 1) + degree + 1 - (degree + 1) =
        (state.positive.selection row).val + degree + 1 by omega]
    exact hinterior.2

/-- Clamp the next sampling point and preserve the geometric invariant for
all earlier and later rows. -/
private def advance
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ} {processed : ℕ}
    (state :
      SchoenbergWhitneyRefinementState
        knots degree count points processed)
    (hprocessed : processed < count)
    (hpoints : StrictMono points) :
    SchoenbergWhitneyRefinementState
      knots degree count points (processed + 1) :=
  let result := clampNextPoint state hprocessed hpoints
  { refinement := result.repeated.refinement
    positive := result.repeated.positive
    clamped_of_lt := result.clamped_of_lt hpoints
    interior_of_le := result.interior_of_le hpoints }

/-- Iteratively clamp the first `processed` sampling points. -/
private def build
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (condition :
      SchoenbergWhitneyCondition knots degree count points) :
    (processed : ℕ) → processed ≤ count →
      SchoenbergWhitneyRefinementState
        knots degree count points processed
  | 0, _ => initial condition
  | processed + 1, hprocessed =>
      (build condition processed (by omega)).advance
        (by omega) condition.strictMono

/-- Refine until every Schoenberg–Whitney sampling point is fully
clamped, while retaining a strictly positive ordered refinement minor. -/
private def complete
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (condition :
      SchoenbergWhitneyCondition knots degree count points) :
    SchoenbergWhitneyRefinementState
      knots degree count points count :=
  build condition count le_rfl

/-- A completely clamped state evaluates row by row as an increasing
Kronecker selector. -/
private theorem evaluation_eq_ite
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (state :
      SchoenbergWhitneyRefinementState
        knots degree count points count)
    (row : Fin count) (column : Fin state.refinement.refinedCount) :
    finiteCoxDeBoorBasis state.refinement.refinedKnots degree
        state.refinement.refinedCount column (points row) =
      if column = state.positive.selection row then 1 else 0 := by
  have hclamped := state.clamped_of_lt row row.isLt
  by_cases hcolumn : column = state.positive.selection row
  · subst column
    rw [ite_eq_left rfl]
    exact coxDeBoorBasis_eq_one_of_left_clamped _ degree _ (points row) hclamped.1 hclamped.2
  rw [ite_eq_right hcolumn]
  change coxDeBoorBasis state.refinement.refinedKnots degree column.val (points row) = 0
  have hmono := state.refinement.refinedKnots.monotone
  rcases lt_or_gt_of_ne hcolumn with hless | hgreater
  · refine coxDeBoorBasis_eq_zero_of_right_le _ _ _ ?_
    exact (hmono (show column.val + degree + 1 ≤ (state.positive.selection row).val + degree by
      omega)).trans_eq (hclamped.1 degree le_rfl)
  have hcolumnLower : points row ≤ state.refinement.refinedKnots column.val :=
    (hclamped.1 0 (Nat.zero_le degree)).symm.trans_le (hmono (by simpa using hgreater.le))
  rcases hcolumnLower.lt_or_eq with hstrict | hcolumnKnot
  · exact coxDeBoorBasis_eq_zero_of_lt_left _ degree column.val hstrict
  · refine coxDeBoorBasis_eq_zero_of_left_eq_of_lt_last_left_knot _ degree column.val (points row)
      hcolumnKnot.symm ?_
    exact hclamped.2.trans_le
      (hmono (show (state.positive.selection row).val + degree + 1 ≤ column.val + degree by omega))

/-- A completely clamped positive refinement proves the strict
Schoenberg–Whitney determinant inequality. -/
private theorem det_collocation_pos
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (state :
      SchoenbergWhitneyRefinementState
        knots degree count points count) :
    0 <
      (collocationMatrix
        (finiteCoxDeBoorBasis knots degree count) points).det :=
  state.positive.det_collocation_pos_of_eq_ite
    points state.evaluation_eq_ite

end SchoenbergWhitneyRefinementState

namespace SchoenbergWhitneyCondition

/-- The strict Schoenberg–Whitney inequalities, with strictly increasing sample points,
make the collocation determinant positive for any nondecreasing knot sequence, including
repeated knots. These strict inequalities are not necessary for nonsingularity under the
half-open endpoint convention: a left-clamped B-spline can take value one at its left endpoint. -/
theorem det_collocation_pos
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (condition :
      SchoenbergWhitneyCondition knots degree count points) :
    0 <
      (collocationMatrix
        (finiteCoxDeBoorBasis knots degree count) points).det :=
  (SchoenbergWhitneyRefinementState.complete condition).det_collocation_pos

/-- Schoenberg–Whitney collocation is nonsingular. -/
theorem det_collocation_ne_zero
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (condition :
      SchoenbergWhitneyCondition knots degree count points) :
    (collocationMatrix
      (finiteCoxDeBoorBasis knots degree count) points).det ≠ 0 :=
  ne_of_gt condition.det_collocation_pos

/-- Every finite Cox–de Boor family satisfying the
Schoenberg–Whitney inequalities is linearly independent. -/
theorem linearIndependent
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (condition :
      SchoenbergWhitneyCondition knots degree count points) :
    LinearIndependent ℝ
      (finiteCoxDeBoorBasis knots degree count) :=
  linearIndependent_of_collocation_det_ne_zero
    condition.det_collocation_ne_zero

end SchoenbergWhitneyCondition

end

end CAS.Splines
