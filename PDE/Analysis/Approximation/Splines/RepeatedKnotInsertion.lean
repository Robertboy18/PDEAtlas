/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.KnotInsertion
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Positivity.Finset

/-!
# Repeated insertion of one knot value

Inserting the same value `repetitions` times immediately after knot position
`position` has a simple closed form: knots up to `position` are unchanged, a
constant block of `repetitions` copies of the value follows, and the original
right segment is shifted by `repetitions`.  Raising the multiplicity of a knot
to the degree plus one in this way makes the B-splines interpolatory there,
which is how support windows are tracked in the strict total-positivity
argument for collocation matrices.  We prove the closed form and show that
it agrees, one step at a time, with the ordinary single insertion
`insertKnotAfter`.

## Main results

* `insertKnotRepeatedlyAfter`: the knot sequence with the repeated block,
  with the monotonicity proof.
* `insertKnotRepeatedlyAfter_knot_of_le`,
  `insertKnotRepeatedlyAfter_knot_of_mem_block`,
  `insertKnotRepeatedlyAfter_knot_of_gt`: the three regimes of the closed
  form.
* `insertKnotRepeatedlyAfter_left_admissible`,
  `insertKnotRepeatedlyAfter_right_admissible`: the next copy can always be
  inserted admissibly at the end of the current block.
* `insertKnotRepeatedlyAfter_zero`, `insertKnotRepeatedlyAfter_succ`: zero
  repetitions is the identity, and one more repetition is one ordinary
  insertion.

## References

* C. de Boor, *A Practical Guide to Splines*, revised edition, Applied Mathematical Sciences,
  Springer, 2001, Chapter XI, The B-Spline Series, Control Points, and Knot Insertion,
  pp. 131-144. <https://doi.org/10.1007/978-1-4612-6333-3_11>
-/

@[expose] public section

namespace CAS.Splines

noncomputable section

/-- Knot values after inserting `repetitions` copies of `value` immediately
after `position`. -/
def insertKnotRepeatedlyAfterValue
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (repetitions index : ℕ) : ℝ :=
  if index ≤ position then
    knots index
  else if index ≤ position + repetitions then
    value
  else
    knots (index - repetitions)

/-- Insert the same admissible knot value a prescribed number of times. -/
def insertKnotRepeatedlyAfter
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (repetitions : ℕ) :
    KnotSequence :=
  OrderHom.mk
      (insertKnotRepeatedlyAfterValue knots position value repetitions) <|
    monotone_nat_of_le_succ fun index ↦ by
    change
      insertKnotRepeatedlyAfterValue
          knots position value repetitions index ≤
        insertKnotRepeatedlyAfterValue
          knots position value repetitions (index + 1)
    simp only [insertKnotRepeatedlyAfterValue]
    by_cases hbefore : index < position
    · have hindex : index ≤ position := hbefore.le
      have hnext : index + 1 ≤ position := by omega
      rw [ite_eq_left hindex, ite_eq_left hnext]
      exact knots.monotone (Nat.le_succ index)
    · by_cases hat : index = position
      · subst index
        by_cases hzero : repetitions = 0
        · subst repetitions
          rw [ite_eq_left le_rfl, ite_eq_right (by omega),
            ite_eq_right (by omega)]
          simp only [Nat.sub_zero]
          simpa using knots.monotone
            (Nat.le_succ position)
        · rw [ite_eq_left le_rfl, ite_eq_right (by omega),
            ite_eq_left (by omega)]
          exact hleft
      · have hafter : position < index := by omega
        by_cases hinside : index < position + repetitions
        · rw [ite_eq_right (by omega), ite_eq_left hinside.le,
            ite_eq_right (by omega), ite_eq_left (by omega)]
        · by_cases hboundary : index = position + repetitions
          · subst index
            have hpositive : 0 < repetitions := by omega
            rw [ite_eq_right (by omega), ite_eq_left le_rfl,
              ite_eq_right (by omega), ite_eq_right (by omega)]
            have hsub :
                position + repetitions + 1 - repetitions =
                  position + 1 := by
              omega
            rw [hsub]
            simpa using hright
          · have hfar : position + repetitions < index := by omega
            rw [ite_eq_right (by omega), ite_eq_right (by omega),
              ite_eq_right (by omega), ite_eq_right (by omega)]
            have hsub :
                index + 1 - repetitions =
                  (index - repetitions) + 1 := by
              omega
            rw [hsub]
            exact knots.monotone
              (Nat.le_succ (index - repetitions))

/-- Repeated insertion leaves every knot at or before the insertion position unchanged. -/
@[simp]
theorem insertKnotRepeatedlyAfter_knot_of_le
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (repetitions : ℕ) {index : ℕ} (hindex : index ≤ position) :
    (insertKnotRepeatedlyAfter knots position value hleft hright
      repetitions) index =
      knots index := by
  change
    insertKnotRepeatedlyAfterValue
        knots position value repetitions index =
      knots index
  rw [insertKnotRepeatedlyAfterValue, ite_eq_left hindex]

/-- Every index in the newly inserted block evaluates to the inserted knot value. -/
@[simp]
theorem insertKnotRepeatedlyAfter_knot_of_mem_block
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (repetitions : ℕ) {index : ℕ}
    (hposition : position < index)
    (hindex : index ≤ position + repetitions) :
    (insertKnotRepeatedlyAfter knots position value hleft hright
      repetitions) index =
      value := by
  change
    insertKnotRepeatedlyAfterValue
        knots position value repetitions index =
      value
  rw [insertKnotRepeatedlyAfterValue,
    ite_eq_right (not_le_of_gt hposition), ite_eq_left hindex]

/-- Beyond the inserted block, knot indices are shifted by the number of repetitions. -/
@[simp]
theorem insertKnotRepeatedlyAfter_knot_of_gt
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (repetitions : ℕ) {index : ℕ}
    (hindex : position + repetitions < index) :
    (insertKnotRepeatedlyAfter knots position value hleft hright
      repetitions) index =
      knots (index - repetitions) := by
  change
    insertKnotRepeatedlyAfterValue
        knots position value repetitions index =
      knots (index - repetitions)
  rw [insertKnotRepeatedlyAfterValue,
    ite_eq_right (by omega), ite_eq_right (not_le_of_gt hindex)]

/-- The knot immediately after the repeated block is the original right
neighbor. -/
theorem insertKnotRepeatedlyAfter_knot_after_block
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (repetitions : ℕ) :
    (insertKnotRepeatedlyAfter knots position value hleft hright
      repetitions) (position + repetitions + 1) =
      knots (position + 1) := by
  rw [insertKnotRepeatedlyAfter_knot_of_gt
    knots position value hleft hright repetitions (by omega)]
  congr 1
  omega

/-- At the right end of the current inserted block, the next copy can
always be inserted admissibly. -/
theorem insertKnotRepeatedlyAfter_left_admissible
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (repetitions : ℕ) :
    (insertKnotRepeatedlyAfter knots position value hleft hright
      repetitions) (position + repetitions) ≤ value := by
  by_cases hzero : repetitions = 0
  · subst repetitions
    simpa using hleft
  · rw [insertKnotRepeatedlyAfter_knot_of_mem_block
      knots position value hleft hright repetitions
      (by omega) le_rfl]

/-- The original right neighbor remains immediately after every partially
inserted block. -/
theorem insertKnotRepeatedlyAfter_right_admissible
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (repetitions : ℕ) :
    value ≤
      (insertKnotRepeatedlyAfter knots position value hleft hright
        repetitions) (position + repetitions + 1) := by
  rw [insertKnotRepeatedlyAfter_knot_after_block]
  exact hright

/-- Inserting zero copies leaves the knot sequence unchanged. -/
@[simp]
theorem insertKnotRepeatedlyAfter_zero
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1)) :
    insertKnotRepeatedlyAfter knots position value hleft hright 0 =
      knots := by
  unfold insertKnotRepeatedlyAfter
  apply OrderHom.ext
  funext index
  simp only [OrderHom.coe_mk, insertKnotRepeatedlyAfterValue, Nat.add_zero,
    Nat.sub_zero]
  by_cases hindex : index ≤ position
  · rw [ite_eq_left hindex]
  · rw [ite_eq_right hindex, ite_eq_right hindex]

/-- One further explicit repetition agrees with one ordinary insertion at
the end of the existing block. -/
theorem insertKnotRepeatedlyAfter_succ
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (repetitions : ℕ) :
    insertKnotRepeatedlyAfter knots position value hleft hright
        (repetitions + 1) =
      insertKnotAfter
        (insertKnotRepeatedlyAfter knots position value hleft hright
          repetitions)
        (position + repetitions) value
        (insertKnotRepeatedlyAfter_left_admissible
          knots position value hleft hright repetitions)
        (insertKnotRepeatedlyAfter_right_admissible
          knots position value hleft hright repetitions) := by
  unfold insertKnotRepeatedlyAfter insertKnotAfter
  apply OrderHom.ext
  funext index
  simp only [OrderHom.coe_mk, insertKnotRepeatedlyAfterValue,
    insertKnotAfterValue]
  by_cases hleftIndex : index ≤ position
  · rw [ite_eq_left hleftIndex, ite_eq_left (by omega),
      ite_eq_left hleftIndex]
  · by_cases hcurrentBlock : index ≤ position + repetitions
    · rw [ite_eq_right hleftIndex, ite_eq_left (by omega),
        ite_eq_left hcurrentBlock, ite_eq_right hleftIndex,
        ite_eq_left hcurrentBlock]
    · by_cases hnew : index = position + repetitions + 1
      · subst index
        rw [ite_eq_right (by omega), ite_eq_left (by omega),
          ite_eq_right (by omega), ite_eq_left rfl]
      · have hafter : position + repetitions + 1 < index := by omega
        rw [ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right hnew,
          ite_eq_right (by omega), ite_eq_right (by omega)]
        congr 1
        omega

end

end CAS.Splines
