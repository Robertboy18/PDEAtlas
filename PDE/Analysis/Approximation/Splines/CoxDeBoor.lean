/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import CAS.ExactTactic

/-!
# Cox–de Boor B-splines

The Cox–de Boor recursion defines B-splines on a nondecreasing knot sequence.  Repeated
knots are allowed: Lean's totalized division makes a quotient with zero denominator equal to
zero, which is exactly the standard convention in the recursion.

The two first structural theorems are proved directly from the recursion:

* a degree-`p` basis function with index `i` vanishes outside
  `[tᵢ, tᵢ₊ₚ₊₁)`;
* every basis function is nonnegative.

Partition of unity and linear independence require a finite active family and boundary
conditions on the knot vector; see `NormalizedBasis` and `SchoenbergWhitneyRefinement`.

## References

* C. de Boor, "On calculating with B-splines", *J. Approximation Theory* 6 (1972), no. 1,
  50-62. <https://doi.org/10.1016/0021-9045(72)90080-9>
* M. G. Cox, "The numerical evaluation of B-splines", *IMA J. Appl. Math.* 10 (1972), no. 2,
  134-149. <https://doi.org/10.1093/imamat/10.2.134>
* I. J. Schoenberg, "Contributions to the problem of approximation of equidistant data by
  analytic functions. Part A. On the problem of smoothing or graduation. A first class of
  analytic approximation formulae", *Quart. Appl. Math.* 4 (1946), no. 1, 45-99.
  <https://doi.org/10.1090/qam/15914>
* I. J. Schoenberg, "Contributions to the problem of approximation of equidistant data by
  analytic functions. Part B. On the problem of osculatory interpolation. A second class of
  analytic approximation formulae", *Quart. Appl. Math.* 4 (1946), no. 2, 112-141.
  <https://doi.org/10.1090/qam/16705>
-/

@[expose] public section

namespace CAS.Splines

open Set

noncomputable section

/-- A one-sided nondecreasing knot sequence.  Finite knot vectors can be represented by
extending their final knot with the desired endpoint multiplicity. -/
abbrev KnotSequence := ℕ →o ℝ

/-- Left Cox–de Boor blending weight for a degree successor. -/
def leftBlendWeight (knots : KnotSequence) (degree index : ℕ) (x : ℝ) : ℝ :=
  (x - knots index) /
    (knots (index + degree + 1) - knots index)

/-- Right Cox–de Boor blending weight for a degree successor. -/
def rightBlendWeight (knots : KnotSequence) (degree index : ℕ) (x : ℝ) : ℝ :=
  (knots (index + degree + 2) - x) /
    (knots (index + degree + 2) - knots (index + 1))

/-- Cox–de Boor B-spline basis function of a given degree and index.

At degree zero this is the indicator of the half-open knot interval.  At successor degree it
is the standard two-term recurrence. -/
def coxDeBoorBasis (knots : KnotSequence) : ℕ → ℕ → ℝ → ℝ
  | 0, index, x =>
      if x ∈ Ico (knots index) (knots (index + 1)) then 1 else 0
  | degree + 1, index, x =>
      leftBlendWeight knots degree index x *
          coxDeBoorBasis knots degree index x +
        rightBlendWeight knots degree index x *
          coxDeBoorBasis knots degree (index + 1) x

/-- The degree-zero basis function is the indicator of its half-open knot cell. -/
@[simp]
theorem coxDeBoorBasis_zero (knots : KnotSequence) (index : ℕ) (x : ℝ) :
    coxDeBoorBasis knots 0 index x =
      if x ∈ Ico (knots index) (knots (index + 1)) then 1 else 0 :=
  rfl

/-- The successor-degree basis function satisfies the Cox–de Boor recurrence. -/
@[simp]
theorem coxDeBoorBasis_succ (knots : KnotSequence)
    (degree index : ℕ) (x : ℝ) :
    coxDeBoorBasis knots (degree + 1) index x =
      leftBlendWeight knots degree index x *
          coxDeBoorBasis knots degree index x +
        rightBlendWeight knots degree index x *
          coxDeBoorBasis knots degree (index + 1) x :=
  rfl

/-- Cox–de Boor evaluation depends only on the `degree + 2` knots in its
canonical local knot window. -/
theorem coxDeBoorBasis_congr_knots
    (leftKnots rightKnots : KnotSequence) :
    ∀ degree index x,
      (∀ offset ≤ degree + 1,
        leftKnots (index + offset) =
          rightKnots (index + offset)) →
      coxDeBoorBasis leftKnots degree index x =
        coxDeBoorBasis rightKnots degree index x := by
  intro degree
  induction degree with
  | zero =>
      intro index x hknots
      simp only [coxDeBoorBasis_zero]
      rw [show leftKnots index = rightKnots index by simpa using hknots 0 (by omega),
        hknots 1 (by omega)]
  | succ degree ih =>
      intro index x hknots
      simp only [coxDeBoorBasis_succ, leftBlendWeight, rightBlendWeight]
      rw [show leftKnots index = rightKnots index by simpa using hknots 0 (by omega),
        hknots 1 (by omega),
        show leftKnots (index + degree + 1) = rightKnots (index + degree + 1) from
          hknots (degree + 1) (by omega),
        show leftKnots (index + degree + 2) = rightKnots (index + degree + 2) from
          hknots (degree + 2) (by omega),
        ih index x fun offset hoffset ↦ hknots offset (by omega),
        ih (index + 1) x fun offset hoffset ↦ by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hknots (offset + 1) (by omega)]

/-- A nonzero degree-`p` B-spline lies in its canonical half-open support interval
`[tᵢ, tᵢ₊ₚ₊₁)`. -/
theorem coxDeBoorBasis_mem_support (knots : KnotSequence) :
    ∀ degree index x,
      coxDeBoorBasis knots degree index x ≠ 0 →
        x ∈ Ico (knots index)
          (knots (index + degree + 1)) := by
  intro degree
  induction degree with
  | zero =>
      intro index x hx
      simp only [coxDeBoorBasis_zero] at hx
      split at hx
      · assumption
      · simp at hx
  | succ degree ih =>
      intro index x hx
      rw [coxDeBoorBasis_succ] at hx
      by_cases hleft :
          leftBlendWeight knots degree index x * coxDeBoorBasis knots degree index x = 0
      · have hchild :=
          ih (index + 1) x (right_ne_zero_of_mul (by simpa only [hleft, zero_add] using hx))
        exact ⟨(knots.monotone (Nat.le_succ index)).trans hchild.1,
          by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchild.2⟩
      · have hchild := ih index x (right_ne_zero_of_mul hleft)
        exact ⟨hchild.1, hchild.2.trans_le (knots.monotone (by omega))⟩

/-- A B-spline vanishes strictly to the left of its canonical support. -/
theorem coxDeBoorBasis_eq_zero_of_lt_left (knots : KnotSequence)
    (degree index : ℕ) {x : ℝ} (hx : x < knots index) :
    coxDeBoorBasis knots degree index x = 0 := by
  by_contra hne
  exact (not_le_of_gt hx)
    (coxDeBoorBasis_mem_support knots degree index x hne).1

/-- A B-spline vanishes at and to the right of the upper endpoint of its canonical
half-open support. -/
theorem coxDeBoorBasis_eq_zero_of_right_le (knots : KnotSequence)
    (degree index : ℕ) {x : ℝ}
    (hx : knots (index + degree + 1) ≤ x) :
    coxDeBoorBasis knots degree index x = 0 := by
  by_contra hne
  exact (not_lt_of_ge hx)
    (coxDeBoorBasis_mem_support knots degree index x hne).2

/-- A collapsed canonical support gives the identically zero B-spline. -/
theorem coxDeBoorBasis_eq_zero_of_support_eq
    (knots : KnotSequence) (degree index : ℕ) {x : ℝ}
    (hsupport :
      knots (index + degree + 1) = knots index) :
    coxDeBoorBasis knots degree index x = 0 := by
  by_cases hx : x < knots index
  · exact coxDeBoorBasis_eq_zero_of_lt_left knots degree index hx
  · apply coxDeBoorBasis_eq_zero_of_right_le knots degree index
    rw [hsupport]
    exact le_of_not_gt hx

/-- Every Cox–de Boor B-spline on a nondecreasing knot sequence is nonnegative. -/
theorem coxDeBoorBasis_nonneg (knots : KnotSequence) :
    ∀ degree index x, 0 ≤ coxDeBoorBasis knots degree index x := by
  intro degree
  induction degree with
  | zero =>
      intro index x
      simp only [coxDeBoorBasis_zero]
      split <;> norm_num
  | succ degree ih =>
      intro index x
      rw [coxDeBoorBasis_succ]
      refine add_nonneg ?_ ?_
      · by_cases hzero : coxDeBoorBasis knots degree index x = 0
        · simp [hzero]
        · exact mul_nonneg (div_nonneg (sub_nonneg.mpr
            (coxDeBoorBasis_mem_support knots degree index x hzero).1)
            (sub_nonneg.mpr (knots.monotone (by omega)))) (ih index x)
      · by_cases hzero : coxDeBoorBasis knots degree (index + 1) x = 0
        · simp [hzero]
        · have hs := coxDeBoorBasis_mem_support knots degree (index + 1) x hzero
          exact mul_nonneg (div_nonneg (sub_nonneg.mpr (by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs.2.le))
            (sub_nonneg.mpr (knots.monotone (by omega)))) (ih (index + 1) x)

/-- The degree-zero B-spline is one on its knot cell. -/
theorem coxDeBoorBasis_zero_eq_one (knots : KnotSequence)
    (index : ℕ) {x : ℝ}
    (hx : x ∈ Ico (knots index) (knots (index + 1))) :
    coxDeBoorBasis knots 0 index x = 1 := by
  simp [hx]

/-- The degree-zero B-spline is zero off its knot cell. -/
theorem coxDeBoorBasis_zero_eq_zero (knots : KnotSequence)
    (index : ℕ) {x : ℝ}
    (hx : x ∉ Ico (knots index) (knots (index + 1))) :
    coxDeBoorBasis knots 0 index x = 0 := by
  simp [hx]

/-- A fully repeated left endpoint selects the first right-continuous
B-spline value exactly.

More precisely, if the first `degree + 1` knots in the support all equal
`x`, while the final support knot lies strictly to its right, then the
degree-`degree` basis function takes the value one at `x`.  This is the
endpoint case needed when an interior point coincides with a repeated knot
block in the strict-positivity proof below. -/
theorem coxDeBoorBasis_eq_one_of_left_clamped (knots : KnotSequence) :
    ∀ degree index x,
      (∀ offset ≤ degree, knots (index + offset) = x) →
      x < knots (index + degree + 1) →
      coxDeBoorBasis knots degree index x = 1 := by
  intro degree
  induction degree with
  | zero =>
      intro index x hclamped hright
      apply coxDeBoorBasis_zero_eq_one
      constructor
      · simpa using (hclamped 0 (Nat.zero_le 0)).le
      · simpa using hright
  | succ degree ih =>
      intro index x hclamped hright
      have hx : x < knots (index + degree + 2) := hright
      have hleftWeight : leftBlendWeight knots degree index x = 0 := by
        simp [leftBlendWeight, show knots index = x by simpa using hclamped 0 (Nat.zero_le _)]
      have hrightWeight : rightBlendWeight knots degree index x = 1 := by
        rw [rightBlendWeight, show knots (index + 1) = x by simpa using hclamped 1 (by omega)]
        exact div_self (sub_ne_zero.mpr hx.ne')
      have hchild : ∀ offset ≤ degree, knots (index + 1 + offset) = x := fun offset hoffset ↦ by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hclamped (offset + 1) (by omega)
      rw [coxDeBoorBasis_succ, hleftWeight, hrightWeight, ih (index + 1) x hchild
        (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright)]
      ring

/-- A B-spline vanishes at its left endpoint when one of the first
`degree + 1` knots in its local window already lies strictly to the right.

Equivalently, the only degree-`degree` B-spline that can be nonzero at a
left knot is the one whose first `degree + 1` local knots are all repeated
there. -/
theorem coxDeBoorBasis_eq_zero_of_left_eq_of_lt_last_left_knot
    (knots : KnotSequence) :
    ∀ degree index x,
      knots index = x →
      x < knots (index + degree) →
      coxDeBoorBasis knots degree index x = 0 := by
  intro degree
  induction degree with
  | zero =>
      intro index x hleft hright
      rw [Nat.add_zero, hleft] at hright
      exact (lt_irrefl x hright).elim
  | succ degree ih =>
      intro index x hleft hright
      have hrightChild : coxDeBoorBasis knots degree (index + 1) x = 0 := by
        rcases (hleft ▸ knots.monotone (Nat.le_succ index)).eq_or_lt with hnext | hnext
        · exact ih (index + 1) x hnext.symm
            (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright)
        · exact coxDeBoorBasis_eq_zero_of_lt_left knots degree (index + 1) hnext
      rw [coxDeBoorBasis_succ, show leftBlendWeight knots degree index x = 0 by
        simp [leftBlendWeight, hleft], hrightChild]
      ring

/-- A Cox–de Boor B-spline is strictly positive throughout the open
interior of its canonical support, even when internal knots are repeated.

The proof follows the recursion.  Away from a repeated knot block, one of
the two child splines is positive by induction and its blending weight is
positive.  If the point coincides with the entire shared knot block, the
right-continuous convention is resolved by
`coxDeBoorBasis_eq_one_of_left_clamped`. -/
theorem coxDeBoorBasis_pos_of_mem_support_interior
    (knots : KnotSequence) :
    ∀ degree index x,
      knots index < x →
      x < knots (index + degree + 1) →
      0 < coxDeBoorBasis knots degree index x := by
  intro degree
  induction degree with
  | zero =>
      intro index x hleft hright
      rw [coxDeBoorBasis_zero_eq_one knots index ⟨hleft.le, by simpa using hright⟩]
      exact zero_lt_one
  | succ degree ih =>
      intro index x hleft hright
      have hx : x < knots (index + degree + 2) := hright
      have hx₁ : x < knots (index + 1 + degree + 1) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright
      rw [coxDeBoorBasis_succ]
      have hL : 0 ≤ leftBlendWeight knots degree index x * coxDeBoorBasis knots degree index x :=
        mul_nonneg (div_nonneg (sub_nonneg.mpr hleft.le)
          (sub_nonneg.mpr (knots.monotone (by omega)))) (coxDeBoorBasis_nonneg knots degree index x)
      have hR : 0 ≤ rightBlendWeight knots degree index x *
          coxDeBoorBasis knots degree (index + 1) x :=
        mul_nonneg (div_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr (knots.monotone (by omega))))
          (coxDeBoorBasis_nonneg knots degree (index + 1) x)
      by_cases hleftChild : x < knots (index + degree + 1)
      · exact add_pos_of_pos_of_nonneg (mul_pos (div_pos (sub_pos.mpr hleft)
          (sub_pos.mpr (hleft.trans hleftChild))) (ih index x hleft hleftChild)) hR
      by_cases hrightChild : knots (index + 1) < x
      · exact add_pos_of_nonneg_of_pos hL (mul_pos (div_pos (sub_pos.mpr hx)
          (sub_pos.mpr (hrightChild.trans hx))) (ih (index + 1) x hrightChild hx₁))
      have hsharedUpper : knots (index + degree + 1) ≤ x := le_of_not_gt hleftChild
      have hsharedLower : x ≤ knots (index + 1) := le_of_not_gt hrightChild
      have hnextKnot : knots (index + 1) = x :=
        le_antisymm ((knots.monotone (by omega)).trans hsharedUpper) hsharedLower
      have hrightBasis : coxDeBoorBasis knots degree (index + 1) x = 1 :=
        coxDeBoorBasis_eq_one_of_left_clamped knots degree (index + 1) x (fun offset hoffset ↦
          le_antisymm ((knots.monotone (by omega)).trans hsharedUpper)
            (hsharedLower.trans (knots.monotone (by omega)))) hx₁
      have hrightWeight : rightBlendWeight knots degree index x = 1 := by
        rw [rightBlendWeight, hnextKnot]
        exact div_self (sub_ne_zero.mpr hx.ne')
      rw [hrightBasis, hrightWeight, mul_one]
      linarith

/-- Derivative of the left affine blending weight. -/
def leftBlendWeightDerivative (knots : KnotSequence)
    (degree index : ℕ) : ℝ :=
  1 / (knots (index + degree + 1) - knots index)

/-- Derivative of the right affine blending weight. -/
def rightBlendWeightDerivative (knots : KnotSequence)
    (degree index : ℕ) : ℝ :=
  -1 / (knots (index + degree + 2) - knots (index + 1))

/-- The left Cox–de Boor blending weight has its expected constant derivative.

The statement remains valid when the denominator vanishes because division is
totalized: both the weight and its declared derivative are then zero. -/
theorem hasDerivAt_leftBlendWeight (knots : KnotSequence)
    (degree index : ℕ) (x : ℝ) :
    HasDerivAt (leftBlendWeight knots degree index)
      (leftBlendWeightDerivative knots degree index) x := by
  change HasDerivAt
    (fun y : ℝ ↦
      (y - knots index) /
        (knots (index + degree + 1) - knots index))
    (1 / (knots (index + degree + 1) - knots index)) x
  simpa only [id_eq, one_div] using
    ((hasDerivAt_id x).sub_const (knots index)).div_const
      (knots (index + degree + 1) - knots index)

/-- The right Cox–de Boor blending weight has its expected constant derivative. -/
theorem hasDerivAt_rightBlendWeight (knots : KnotSequence)
    (degree index : ℕ) (x : ℝ) :
    HasDerivAt (rightBlendWeight knots degree index)
      (rightBlendWeightDerivative knots degree index) x := by
  change HasDerivAt
    (fun y : ℝ ↦
      (knots (index + degree + 2) - y) /
        (knots (index + degree + 2) - knots (index + 1)))
    (-1 / (knots (index + degree + 2) - knots (index + 1))) x
  simpa only [id_eq, Pi.sub_apply, zero_sub] using
    ((hasDerivAt_const x (knots (index + degree + 2))).sub
      (hasDerivAt_id x)).div_const
        (knots (index + degree + 2) - knots (index + 1))

/-- A degree-zero B-spline is differentiable away from its two knot endpoints. -/
theorem hasDerivAt_coxDeBoorBasis_zero_of_ne_knots
    (knots : KnotSequence) (index : ℕ) {x : ℝ}
    (hleft : x ≠ knots index)
    (hright : x ≠ knots (index + 1)) :
    HasDerivAt (coxDeBoorBasis knots 0 index) 0 x := by
  by_cases hxleft : x < knots index
  · apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hxleft] with y hy
    simp [coxDeBoorBasis, not_le_of_gt hy]
  · have hleftx : knots index < x :=
      lt_of_le_of_ne (le_of_not_gt hxleft) hleft.symm
    by_cases hxright : x < knots (index + 1)
    · apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hleftx,
        eventually_lt_nhds hxright] with y hlefty hrighty
      simp [coxDeBoorBasis, hlefty.le, hrighty]
    · have hrightx : knots (index + 1) < x :=
        lt_of_le_of_ne (le_of_not_gt hxright) hright.symm
      apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hrightx] with y hy
      simp [coxDeBoorBasis, not_lt_of_ge hy.le]

/-- Recursive derivative expression obtained by differentiating the Cox–de Boor recurrence.

At knots this is only an algebraic expression.  Away from every knot it is the
derivative on each open knot interval, as proved by
`hasDerivAt_coxDeBoorBasis_of_mem_Ioo` in `LocalBranches`. -/
def coxDeBoorBasisDerivative (knots : KnotSequence) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | degree + 1, index, x =>
      (leftBlendWeightDerivative knots degree index *
          coxDeBoorBasis knots degree index x +
        leftBlendWeight knots degree index x *
          coxDeBoorBasisDerivative knots degree index x) +
      (rightBlendWeightDerivative knots degree index *
          coxDeBoorBasis knots degree (index + 1) x +
        rightBlendWeight knots degree index x *
          coxDeBoorBasisDerivative knots degree (index + 1) x)

/-- The recursive derivative expression vanishes in degree zero. -/
@[simp]
theorem coxDeBoorBasisDerivative_zero (knots : KnotSequence)
    (index : ℕ) (x : ℝ) :
    coxDeBoorBasisDerivative knots 0 index x = 0 :=
  rfl

/-- The recursive derivative expression obeys the differentiated Cox–de Boor recurrence. -/
@[simp]
theorem coxDeBoorBasisDerivative_succ (knots : KnotSequence)
    (degree index : ℕ) (x : ℝ) :
    coxDeBoorBasisDerivative knots (degree + 1) index x =
      (leftBlendWeightDerivative knots degree index *
          coxDeBoorBasis knots degree index x +
        leftBlendWeight knots degree index x *
          coxDeBoorBasisDerivative knots degree index x) +
      (rightBlendWeightDerivative knots degree index *
          coxDeBoorBasis knots degree (index + 1) x +
        rightBlendWeight knots degree index x *
          coxDeBoorBasisDerivative knots degree (index + 1) x) :=
  rfl

end

end CAS.Splines
