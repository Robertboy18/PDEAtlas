/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.CoxDeBoor
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.Positivity.Finset

/-!
# Knot insertion for Cox–de Boor B-splines

We insert one knot into a nondecreasing knot sequence and define the
adjacent refinement coefficients, for arbitrary repeated knots; all quotients
use Lean's totalized division convention. The coefficients lie in `[0, 1]`.

The refinement identity `coxDeBoorBasis_eq_knotInsertion` writes each coarse
B-spline as a combination of two refined ones. It is Boehm's knot insertion formula, which
de Boor and DeVore write as (2.4), and the algebraic step behind total positivity and the
Schoenberg–Whitney theorem.

## References

* C. de Boor, "On calculating with B-splines", *J. Approximation Theory* 6 (1972), no. 1,
  50-62. <https://doi.org/10.1016/0021-9045(72)90080-9>
* W. Boehm, "Inserting new knots into B-spline curves", *Computer-Aided Design* 12 (1980),
  no. 4, 199-201. <https://doi.org/10.1016/0010-4485(80)90154-2>
* C. de Boor and R. DeVore, "A geometric proof of total positivity for spline interpolation",
  *Math. Comp.* 45 (1985), no. 172, 497-504, Section 2, (2.2)-(2.4), p. 498.
  <https://doi.org/10.1090/S0025-5718-1985-0804938-2>
-/

@[expose] public section

namespace CAS.Splines

noncomputable section

/-- Knot values after inserting `value` immediately after `position`. -/
def insertKnotAfterValue
    (knots : KnotSequence) (position : ℕ) (value : ℝ) (index : ℕ) : ℝ :=
  if index ≤ position then
    knots index
  else if index = position + 1 then
    value
  else
    knots (index - 1)

/-- Insert a value between two adjacent knots.

The hypotheses allow equality on either side, so insertion into an existing
repeated knot block is supported. -/
def insertKnotAfter
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1)) :
    KnotSequence :=
  OrderHom.mk (insertKnotAfterValue knots position value) <|
    monotone_nat_of_le_succ fun index ↦ by
    by_cases hbefore : index < position
    · have hindex : index ≤ position := hbefore.le
      have hnext : index + 1 ≤ position := by omega
      simp only [insertKnotAfterValue, ite_eq_left hindex, ite_eq_left hnext]
      exact knots.monotone (Nat.le_succ index)
    · by_cases hat : index = position
      · subst index
        simpa [insertKnotAfterValue] using hleft
      · by_cases hafter : index = position + 1
        · subst index
          simpa [insertKnotAfterValue] using hright
        · have hfar : position + 1 < index := by omega
          have hindexNotLe : ¬index ≤ position := by omega
          have hnextNotLe : ¬index + 1 ≤ position := by omega
          have hindexNotAt : index ≠ position + 1 := hafter
          have hnextNotAt : index + 1 ≠ position + 1 := by omega
          simp only [insertKnotAfterValue, ite_eq_right hindexNotLe,
            ite_eq_right hnextNotLe, ite_eq_right hindexNotAt, ite_eq_right hnextNotAt]
          exact knots.monotone (by omega)

/-- Knot insertion respects equality of the underlying knot sequence;
proofs of admissibility are irrelevant. -/
theorem insertKnotAfter_congr
    (leftKnots rightKnots : KnotSequence)
    (hknots : leftKnots = rightKnots)
    (position : ℕ) (value : ℝ)
    (leftLower : leftKnots position ≤ value)
    (leftUpper : value ≤ leftKnots (position + 1))
    (rightLower : rightKnots position ≤ value)
    (rightUpper : value ≤ rightKnots (position + 1)) :
    insertKnotAfter leftKnots position value leftLower leftUpper =
      insertKnotAfter rightKnots position value rightLower rightUpper := by
  subst rightKnots
  rfl

/-- Knot values at and before the insertion position are unchanged. -/
@[simp]
theorem insertKnotAfter_knot_of_le
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    {index : ℕ} (hindex : index ≤ position) :
    (insertKnotAfter knots position value hleft hright) index =
      knots index := by
  simp [insertKnotAfter, insertKnotAfterValue, hindex]

/-- The new knot occupies the position immediately after the insertion position. -/
@[simp]
theorem insertKnotAfter_knot_inserted
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1)) :
    (insertKnotAfter knots position value hleft hright)
        (position + 1) = value := by
  simp [insertKnotAfter, insertKnotAfterValue]

/-- Knot values beyond the inserted knot are shifted right by one index. -/
@[simp]
theorem insertKnotAfter_knot_of_add_two
    (knots : KnotSequence) (position offset : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1)) :
    (insertKnotAfter knots position value hleft hright)
        (position + offset + 2) =
      knots (position + offset + 1) := by
  change
    insertKnotAfterValue knots position value (position + offset + 2) =
      knots (position + offset + 1)
  rw [insertKnotAfterValue]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hindex :
      position + offset + 2 - 1 = position + offset + 1 := by
    omega
  rw [hindex]

/-- Every index at least two positions beyond the insertion slot is the
preceding coarse knot. -/
theorem insertKnotAfter_knot_of_two_le
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    {index : ℕ} (hindex : position + 2 ≤ index) :
    (insertKnotAfter knots position value hleft hright) index =
      knots (index - 1) := by
  change
    insertKnotAfterValue knots position value index =
      knots (index - 1)
  rw [insertKnotAfterValue]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Coefficient of the same-index refined B-spline after one knot
insertion.

For a degree-`degree` basis, coefficients strictly to the left of the
affected band are one, coefficients strictly to its right are zero, and the
intervening coefficients are the standard affine knot-insertion ratios. -/
def knotInsertionAlpha
    (knots : KnotSequence) (degree position : ℕ)
    (value : ℝ) (index : ℕ) : ℝ :=
  if index + degree ≤ position then
    1
  else if index ≤ position then
    (value - knots index) /
      (knots (index + degree) - knots index)
  else
    0

/-- Every knot-insertion coefficient is nonnegative when the inserted value lies
to the right of the insertion-position knot. -/
theorem knotInsertionAlpha_nonneg
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (index : ℕ) :
    0 ≤ knotInsertionAlpha knots degree position value index := by
  unfold knotInsertionAlpha
  split_ifs with hband hposition
  · exact zero_le_one
  · apply div_nonneg
    · exact sub_nonneg.mpr
        ((knots.monotone hposition).trans hleft)
    · exact sub_nonneg.mpr
        (knots.monotone (by omega))
  · exact le_rfl

/-- Every knot-insertion coefficient is at most one when the inserted value lies
to the left of the next knot. -/
theorem knotInsertionAlpha_le_one
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hright : value ≤ knots (position + 1))
    (index : ℕ) :
    knotInsertionAlpha knots degree position value index ≤ 1 := by
  unfold knotInsertionAlpha
  split_ifs with hband hposition
  · exact le_rfl
  · apply div_le_one_of_le₀
    · apply sub_le_sub_right
      exact hright.trans
        (knots.monotone (by omega))
    · exact sub_nonneg.mpr
        (knots.monotone (by omega))
  · exact zero_le_one

/-- The complementary adjacent refinement coefficient is nonnegative. -/
theorem one_sub_knotInsertionAlpha_nonneg
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hright : value ≤ knots (position + 1))
    (index : ℕ) :
    0 ≤ 1 - knotInsertionAlpha knots degree position value index :=
  sub_nonneg.mpr
    (knotInsertionAlpha_le_one knots degree position value
      hright index)

/-- A coefficient strictly to the unaffected left of an insertion is one. -/
theorem knotInsertionAlpha_eq_one_of_add_le
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    {index : ℕ} (hindex : index + degree ≤ position) :
    knotInsertionAlpha knots degree position value index = 1 := by
  simp [knotInsertionAlpha, hindex]

/-- A same-index knot-insertion coefficient is positive when its left knot
lies strictly below the inserted value. -/
theorem knotInsertionAlpha_pos_of_le_position_of_lt
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hright : value ≤ knots (position + 1))
    {index : ℕ} (hindex : index ≤ position)
    (hvalue : knots index < value) :
    0 < knotInsertionAlpha knots degree position value index := by
  unfold knotInsertionAlpha
  split_ifs with hband
  · exact zero_lt_one
  · apply div_pos
    · exact sub_pos.mpr hvalue
    · apply sub_pos.mpr
      have hendpoint :
          value ≤ knots (index + degree) := by
        exact hright.trans
          (knots.monotone (by omega))
      exact hvalue.trans_le hendpoint

/-- A subdiagonal knot-insertion coefficient is positive when the inserted
value lies strictly below the relevant right support knot. -/
theorem one_sub_knotInsertionAlpha_pos_of_position_lt_add
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    {index : ℕ} (hposition : position < index + degree)
    (hvalue : value < knots (index + degree)) :
    0 < 1 - knotInsertionAlpha knots degree position value index := by
  unfold knotInsertionAlpha
  split_ifs with hband hindex
  · exact (not_lt_of_ge hband hposition).elim
  · apply sub_pos.mpr
    have hleftIndex : knots index ≤ value :=
      (knots.monotone hindex).trans hleft
    have hdenominator :
        0 < knots (index + degree) - knots index :=
      sub_pos.mpr (hleftIndex.trans_lt hvalue)
    apply (div_lt_one hdenominator).2
    exact sub_lt_sub_right hvalue (knots index)
  · simp

private theorem knotInsertionAlpha_eq_zero_of_lt (knots : KnotSequence) (degree : ℕ)
    {position : ℕ} (value : ℝ) {index : ℕ} (hindex : position < index) :
    knotInsertionAlpha knots degree position value index = 0 := by
  rw [knotInsertionAlpha, ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem knotInsertionAlpha_eq_div (knots : KnotSequence) (degree : ℕ) {position : ℕ}
    (value : ℝ) {index : ℕ} (right : ℕ) (hband : position < right) (hindex : index ≤ position)
    (hright : index + degree = right := by omega) :
    knotInsertionAlpha knots degree position value index =
      (value - knots index) / (knots right - knots index) := by
  subst hright
  rw [knotInsertionAlpha, ite_eq_right (by omega), ite_eq_left hindex]

/-- A refined knot beyond the inserted one is the preceding coarse knot. -/
private theorem insertKnotAfter_knot_eq_of_lt {knots : KnotSequence} {position : ℕ}
    {value : ℝ} (hleft : knots position ≤ value) (hright : value ≤ knots (position + 1))
    {index shifted : ℕ} (hindex : position < index) (hshifted : shifted = index + 1 := by omega) :
    insertKnotAfter knots position value hleft hright shifted = knots index := by
  subst hshifted
  rw [insertKnotAfter_knot_of_two_le knots position value hleft hright (by omega),
    Nat.add_sub_cancel]

/-- Any two multiples of a B-spline whose support has collapsed are equal. -/
private theorem mul_coxDeBoorBasis_eq_of_support_eq {knots : KnotSequence} {degree index : ℕ}
    {x : ℝ} (a b : ℝ) (last : ℕ) (hsupport : knots last = knots index)
    (hlast : index + degree + 1 = last := by omega) :
    a * coxDeBoorBasis knots degree index x = b * coxDeBoorBasis knots degree index x := by
  subst hlast
  rw [coxDeBoorBasis_eq_zero_of_support_eq knots degree index hsupport, mul_zero, mul_zero]

/-- Degree-zero knot insertion splits exactly one half-open knot cell and
only shifts the cells to its right. -/
theorem coxDeBoorBasis_zero_eq_knotInsertion
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (index : ℕ) (x : ℝ) :
    coxDeBoorBasis knots 0 index x =
      knotInsertionAlpha knots 0 position value index *
          coxDeBoorBasis
            (insertKnotAfter knots position value hleft hright)
            0 index x +
        (1 - knotInsertionAlpha knots 0 position value (index + 1)) *
          coxDeBoorBasis
            (insertKnotAfter knots position value hleft hright)
            0 (index + 1) x := by
  rcases lt_trichotomy index position with hbefore | rfl | hafter
  · have hnext : index + 1 ≤ position := hbefore
    simp [coxDeBoorBasis, knotInsertionAlpha, hbefore.le, hnext]
  · have hknot : (insertKnotAfter knots index value hleft hright) (index + 1 + 1) =
        knots (index + 1) := insertKnotAfter_knot_eq_of_lt hleft hright (Nat.lt_succ_self index)
    rcases lt_or_ge x value with hx | hx
    · simp [knotInsertionAlpha, hknot, hx, hx.trans_le hright, not_le.2 hx]
    · simp [knotInsertionAlpha, hknot, hx, not_lt.2 hx, hleft.trans hx]
  · rw [knotInsertionAlpha_eq_zero_of_lt knots 0 value hafter,
      knotInsertionAlpha_eq_zero_of_lt knots 0 value (hafter.trans (Nat.lt_succ_self index)),
      zero_mul, zero_add, sub_zero, one_mul, coxDeBoorBasis_zero, coxDeBoorBasis_zero,
      insertKnotAfter_knot_eq_of_lt hleft hright (shifted := index + 1) hafter,
      insertKnotAfter_knot_eq_of_lt hleft hright (shifted := index + 1 + 1)
        (by omega : position < index + 1)]

private theorem leftBoundaryRefinementIdentity
    (left right inserted x : ℝ)
    (hcoarse : right - left ≠ 0)
    (hrefined : inserted - left ≠ 0) :
    (x - left) / (right - left) =
      (inserted - left) / (right - left) *
        ((x - left) / (inserted - left)) := by
  field_simp

private theorem leftEdgeMiddleRefinementIdentity
    (left right inserted x : ℝ)
    (hcoarse : right - left ≠ 0)
    (hrefined : right - inserted ≠ 0) :
    (x - left) / (right - left) =
      (inserted - left) / (right - left) *
          ((right - x) / (right - inserted)) +
        (x - inserted) / (right - inserted) := by
  field_simp
  ring

private theorem interiorMiddleRefinementIdentity
    (left next shared support inserted x : ℝ)
    (hleft : shared - left ≠ 0)
    (hshared : shared - next ≠ 0)
    (hright : support - next ≠ 0) :
    (x - left) / (shared - left) *
          (1 - (inserted - next) / (shared - next)) +
        (support - x) / (support - next) *
          ((inserted - next) / (shared - next)) =
      (inserted - left) / (shared - left) *
          ((shared - x) / (shared - next)) +
        (1 - (inserted - next) / (support - next)) *
          ((x - next) / (shared - next)) := by
  field_simp
  ring

private theorem rightEdgeMiddleRefinementIdentity
    (next support inserted x : ℝ)
    (hcoarse : support - next ≠ 0)
    (hrefined : inserted - next ≠ 0) :
    (support - x) / (support - next) =
      (inserted - x) / (inserted - next) +
        (1 - (inserted - next) / (support - next)) *
          ((x - next) / (inserted - next)) := by
  field_simp
  ring

private theorem rightBoundaryRefinementIdentity
    (next support inserted x : ℝ)
    (hcoarse : support - next ≠ 0)
    (hrefined : support - inserted ≠ 0) :
    (support - x) / (support - next) =
      (1 - (inserted - next) / (support - next)) *
        ((support - x) / (support - inserted)) := by
  field_simp
  ring

private theorem interiorRightRefinementIdentity
    (next child support inserted x : ℝ)
    (hnext : support - next ≠ 0)
    (hchild : support - child ≠ 0) :
    (support - x) / (support - next) *
          (1 - (inserted - child) / (support - child)) =
      (1 - (inserted - next) / (support - next)) *
        ((support - x) / (support - child)) := by
  field_simp
  ring


/-- The left-child coefficient in the Cox–de Boor recursion is preserved
by knot insertion.  The B-spline factor is part of the statement because
the bare rational identity need not hold across a collapsed knot span,
where that child spline is identically zero. -/
private theorem leftRefinementCoefficient_mul_basis
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (index : ℕ) (x : ℝ) :
    let refined :=
      insertKnotAfter knots position value hleft hright
    (leftBlendWeight knots degree index x *
        knotInsertionAlpha knots degree position value index) *
          coxDeBoorBasis refined degree index x =
      (knotInsertionAlpha knots (degree + 1) position value index *
        leftBlendWeight refined degree index x) *
          coxDeBoorBasis refined degree index x := by
  intro refined
  unfold leftBlendWeight
  rcases lt_or_ge position index with hafter | hindex
  · rw [knotInsertionAlpha_eq_zero_of_lt knots degree value hafter,
      knotInsertionAlpha_eq_zero_of_lt knots (degree + 1) value hafter]
    ring
  have hstart : refined index = knots index :=
    insertKnotAfter_knot_of_le knots position value hleft hright hindex
  rcases lt_trichotomy (index + degree) position with hbefore | rfl | hband
  · have hend : refined (index + degree + 1) = knots (index + degree + 1) :=
      insertKnotAfter_knot_of_le knots position value hleft hright hbefore
    rw [knotInsertionAlpha_eq_one_of_add_le knots degree position value hbefore.le,
      knotInsertionAlpha_eq_one_of_add_le knots (degree + 1) position value
        (by omega : index + (degree + 1) ≤ position), hstart, hend]
    ring
  · have hend : refined (index + degree + 1) = value :=
      insertKnotAfter_knot_inserted knots (index + degree) value hleft hright
    rcases eq_or_ne value (knots index) with hcollapsed | hcollapsed
    · exact mul_coxDeBoorBasis_eq_of_support_eq _ _ _ (by rw [hend, hstart, hcollapsed])
    have hvalue : knots index < value :=
      ((knots.monotone (by omega)).trans hleft).lt_of_ne' hcollapsed
    rw [knotInsertionAlpha_eq_one_of_add_le knots degree _ value le_rfl,
      knotInsertionAlpha_eq_div knots (degree + 1) value (index + degree + 1) (by omega) hindex,
      hstart, hend, leftBoundaryRefinementIdentity (knots index) (knots (index + degree + 1))
        value x (sub_ne_zero.mpr (hvalue.trans_le hright).ne') (sub_ne_zero.mpr hvalue.ne')]
    ring
  · have hend : refined (index + degree + 1) = knots (index + degree) :=
      insertKnotAfter_knot_eq_of_lt hleft hright hband
    rw [knotInsertionAlpha_eq_div knots degree value (index + degree) hband hindex,
      knotInsertionAlpha_eq_div knots (degree + 1) value (index + degree + 1) (by omega) hindex,
      hstart, hend]
    ring

/-- The coefficient of the shared middle child is preserved by knot
insertion.  As above, multiplying by the child basis is essential for
repeated-knot spans on which the rational coefficient itself is not
canonically determined. -/
private theorem middleRefinementCoefficient_mul_basis
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (index : ℕ) (x : ℝ) :
    let refined :=
      insertKnotAfter knots position value hleft hright
    (leftBlendWeight knots degree index x *
          (1 - knotInsertionAlpha knots degree position value (index + 1)) +
        rightBlendWeight knots degree index x *
          knotInsertionAlpha knots degree position value (index + 1)) *
        coxDeBoorBasis refined degree (index + 1) x =
      (knotInsertionAlpha knots (degree + 1) position value index *
            rightBlendWeight refined degree index x +
          (1 - knotInsertionAlpha knots (degree + 1) position value
              (index + 1)) *
            leftBlendWeight refined degree (index + 1) x) *
        coxDeBoorBasis refined degree (index + 1) x := by
  intro refined
  unfold leftBlendWeight rightBlendWeight
  rw [show index + 1 + degree + 1 = index + degree + 2 by omega]
  rcases lt_or_ge position index with hafter | hindex
  · have hstart : refined (index + 1) = knots index :=
      insertKnotAfter_knot_eq_of_lt hleft hright hafter
    have hend : refined (index + degree + 2) = knots (index + degree + 1) :=
      insertKnotAfter_knot_eq_of_lt hleft hright (by omega)
    rw [knotInsertionAlpha_eq_zero_of_lt knots degree value (by omega : position < index + 1),
      knotInsertionAlpha_eq_zero_of_lt knots (degree + 1) value hafter,
      knotInsertionAlpha_eq_zero_of_lt knots (degree + 1) value (by omega : position < index + 1),
      hstart, hend]
    ring
  rcases lt_or_ge (index + degree + 1) position with hbefore | hupper
  · have hstart : refined (index + 1) = knots (index + 1) :=
      insertKnotAfter_knot_of_le knots position value hleft hright (by omega)
    have hend : refined (index + degree + 2) = knots (index + degree + 2) :=
      insertKnotAfter_knot_of_le knots position value hleft hright hbefore
    rw [knotInsertionAlpha_eq_one_of_add_le knots degree position value
        (by omega : index + 1 + degree ≤ position),
      knotInsertionAlpha_eq_one_of_add_le knots (degree + 1) position value
        (by omega : index + (degree + 1) ≤ position),
      knotInsertionAlpha_eq_one_of_add_le knots (degree + 1) position value
        (by omega : index + 1 + (degree + 1) ≤ position), hstart, hend]
    ring
  rcases hindex.eq_or_lt with rfl | hindex
  · -- the new knot is the left end of the middle child's support
    have hstart : refined (index + 1) = value :=
      insertKnotAfter_knot_inserted knots index value hleft hright
    have hend : refined (index + degree + 2) = knots (index + degree + 1) :=
      insertKnotAfter_knot_eq_of_lt hleft hright (by omega)
    rcases eq_or_ne (knots (index + degree + 1)) value with hcollapsed | hcollapsed
    · exact mul_coxDeBoorBasis_eq_of_support_eq _ _ (index + degree + 2)
        (by rw [hend, hstart, hcollapsed])
    have hvalue : value < knots (index + degree + 1) :=
      (hright.trans (knots.monotone (by omega))).lt_of_ne' hcollapsed
    rw [knotInsertionAlpha_eq_zero_of_lt knots degree value (Nat.lt_succ_self index),
      knotInsertionAlpha_eq_div knots (degree + 1) value (index + degree + 1) (by omega) le_rfl,
      knotInsertionAlpha_eq_zero_of_lt knots (degree + 1) value (Nat.lt_succ_self index),
      hstart, hend, leftEdgeMiddleRefinementIdentity (knots index) (knots (index + degree + 1))
        value x (sub_ne_zero.mpr (hleft.trans_lt hvalue).ne') (sub_ne_zero.mpr hvalue.ne')]
    ring
  rcases hupper.eq_or_lt with rfl | hupper
  · -- the new knot is the right end of the middle child's support
    have hstart : refined (index + 1) = knots (index + 1) :=
      insertKnotAfter_knot_of_le knots _ value hleft hright (by omega)
    have hend : refined (index + degree + 2) = value :=
      insertKnotAfter_knot_inserted knots (index + degree + 1) value hleft hright
    rcases eq_or_ne value (knots (index + 1)) with hcollapsed | hcollapsed
    · exact mul_coxDeBoorBasis_eq_of_support_eq _ _ (index + degree + 2)
        (by rw [hend, hstart, hcollapsed])
    have hvalue : knots (index + 1) < value :=
      ((knots.monotone (by omega)).trans hleft).lt_of_ne' hcollapsed
    rw [knotInsertionAlpha_eq_one_of_add_le knots degree _ value
        (by omega : index + 1 + degree ≤ index + degree + 1),
      knotInsertionAlpha_eq_one_of_add_le knots (degree + 1) _ value
        (by omega : index + (degree + 1) ≤ index + degree + 1),
      knotInsertionAlpha_eq_div knots (degree + 1) value (index + degree + 2) (by omega) hindex,
      hstart, hend, rightEdgeMiddleRefinementIdentity (knots (index + 1))
        (knots (index + degree + 2)) value x (sub_ne_zero.mpr (hvalue.trans_le hright).ne')
        (sub_ne_zero.mpr hvalue.ne')]
    ring
  -- the new knot is interior to the middle child's support
  have hstart : refined (index + 1) = knots (index + 1) :=
    insertKnotAfter_knot_of_le knots position value hleft hright hindex
  have hend : refined (index + degree + 2) = knots (index + degree + 1) :=
    insertKnotAfter_knot_eq_of_lt hleft hright hupper
  rcases eq_or_ne (knots (index + degree + 1)) (knots (index + 1)) with hcollapsed | hcollapsed
  · exact mul_coxDeBoorBasis_eq_of_support_eq _ _ (index + degree + 2)
      (by rw [hend, hstart, hcollapsed])
  have hshared : knots (index + 1) < knots (index + degree + 1) :=
    (knots.monotone (by omega)).lt_of_ne' hcollapsed
  rw [knotInsertionAlpha_eq_div knots degree value (index + degree + 1) hupper hindex,
    knotInsertionAlpha_eq_div knots (degree + 1) value (index + degree + 1) hupper hindex.le,
    knotInsertionAlpha_eq_div knots (degree + 1) value (index + degree + 2) (by omega) hindex,
    hstart, hend, interiorMiddleRefinementIdentity (knots index) (knots (index + 1))
      (knots (index + degree + 1)) (knots (index + degree + 2)) value x
      (sub_ne_zero.mpr ((knots.monotone (Nat.le_succ index)).trans_lt hshared).ne')
      (sub_ne_zero.mpr hshared.ne')
      (sub_ne_zero.mpr (hshared.trans_le (knots.monotone (by omega))).ne')]

/-- The right-child coefficient in the Cox–de Boor recursion is preserved
by knot insertion, with collapsed repeated-knot spans discharged by the
vanishing of the child spline. -/
private theorem rightRefinementCoefficient_mul_basis
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (index : ℕ) (x : ℝ) :
    let refined :=
      insertKnotAfter knots position value hleft hright
    (rightBlendWeight knots degree index x *
        (1 - knotInsertionAlpha knots degree position value (index + 2))) *
          coxDeBoorBasis refined degree (index + 2) x =
      ((1 - knotInsertionAlpha knots (degree + 1) position value
          (index + 1)) *
        rightBlendWeight refined degree (index + 1) x) *
          coxDeBoorBasis refined degree (index + 2) x := by
  intro refined
  unfold rightBlendWeight
  rw [show index + 1 + degree + 2 = index + degree + 3 by omega,
    show index + 1 + 1 = index + 2 by omega]
  rcases lt_or_ge index position with hnext | hbefore
  swap
  · have hstart : refined (index + 2) = knots (index + 1) :=
      insertKnotAfter_knot_eq_of_lt hleft hright (by omega)
    have hend : refined (index + degree + 3) = knots (index + degree + 2) :=
      insertKnotAfter_knot_eq_of_lt hleft hright (by omega)
    rw [knotInsertionAlpha_eq_zero_of_lt knots degree value (by omega : position < index + 2),
      knotInsertionAlpha_eq_zero_of_lt knots (degree + 1) value
        (by omega : position < index + 1), hstart, hend]
    ring
  rcases lt_or_ge (index + degree + 1) position with hafter | hupper
  · rw [knotInsertionAlpha_eq_one_of_add_le knots degree position value
        (by omega : index + 2 + degree ≤ position),
      knotInsertionAlpha_eq_one_of_add_le knots (degree + 1) position value
        (by omega : index + 1 + (degree + 1) ≤ position)]
    ring
  rcases (Nat.succ_le_of_lt hnext).eq_or_lt with rfl | hchild
  · -- the new knot is the left end of the right child's support
    have hstart : refined (index + 2) = value :=
      insertKnotAfter_knot_inserted knots (index + 1) value hleft hright
    have hend : refined (index + degree + 3) = knots (index + degree + 2) :=
      insertKnotAfter_knot_eq_of_lt hleft hright (by omega)
    rcases eq_or_ne (knots (index + degree + 2)) value with hcollapsed | hcollapsed
    · exact mul_coxDeBoorBasis_eq_of_support_eq _ _ (index + degree + 3)
        (by rw [hend, hstart, hcollapsed])
    have hvalue : value < knots (index + degree + 2) :=
      (hright.trans (knots.monotone (by omega))).lt_of_ne' hcollapsed
    rw [knotInsertionAlpha_eq_zero_of_lt knots degree value (Nat.lt_succ_self (index + 1)),
      knotInsertionAlpha_eq_div knots (degree + 1) value (index + degree + 2) (by omega) le_rfl,
      hstart, hend, rightBoundaryRefinementIdentity (knots (index + 1))
        (knots (index + degree + 2)) value x (sub_ne_zero.mpr (hleft.trans_lt hvalue).ne')
        (sub_ne_zero.mpr hvalue.ne')]
    ring
  -- the new knot is interior to the right child's support
  have hstart : refined (index + 2) = knots (index + 2) :=
    insertKnotAfter_knot_of_le knots position value hleft hright hchild
  have hend : refined (index + degree + 3) = knots (index + degree + 2) :=
    insertKnotAfter_knot_eq_of_lt hleft hright (by omega)
  rcases eq_or_ne (knots (index + degree + 2)) (knots (index + 2)) with hcollapsed | hcollapsed
  · exact mul_coxDeBoorBasis_eq_of_support_eq _ _ (index + degree + 3)
      (by rw [hend, hstart, hcollapsed])
  have hspan : knots (index + 2) < knots (index + degree + 2) :=
    (knots.monotone (by omega)).lt_of_ne' hcollapsed
  rw [knotInsertionAlpha_eq_div knots degree value (index + degree + 2) (by omega) hchild,
    knotInsertionAlpha_eq_div knots (degree + 1) value (index + degree + 2) (by omega) hnext,
    hstart, hend, interiorRightRefinementIdentity (knots (index + 1)) (knots (index + 2))
      (knots (index + degree + 2)) value x
      (sub_ne_zero.mpr ((knots.monotone (Nat.le_succ (index + 1))).trans_lt hspan).ne')
      (sub_ne_zero.mpr hspan.ne')]

/-- One-knot refinement identity for Cox–de Boor B-splines of every
degree.

The theorem allows arbitrary repeated knots and insertion at either end of
the admissible knot interval.  Thus it is suitable for iterated refinement
without any hidden strict-knot hypothesis. -/
theorem coxDeBoorBasis_eq_knotInsertion
    (knots : KnotSequence) (position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1)) :
    ∀ degree index x,
      coxDeBoorBasis knots degree index x =
        knotInsertionAlpha knots degree position value index *
            coxDeBoorBasis
              (insertKnotAfter knots position value hleft hright)
              degree index x +
          (1 - knotInsertionAlpha knots degree position value (index + 1)) *
            coxDeBoorBasis
              (insertKnotAfter knots position value hleft hright)
              degree (index + 1) x := by
  intro degree
  induction degree with
  | zero => exact coxDeBoorBasis_zero_eq_knotInsertion knots position value hleft hright
  | succ degree ih =>
    intro index x
    rw [coxDeBoorBasis_succ, ih index x, ih (index + 1) x, coxDeBoorBasis_succ,
      coxDeBoorBasis_succ]
    linear_combination
      leftRefinementCoefficient_mul_basis knots degree position value hleft hright index x +
        middleRefinementCoefficient_mul_basis knots degree position value hleft hright index x +
        rightRefinementCoefficient_mul_basis knots degree position value hleft hright index x

end

end CAS.Splines
