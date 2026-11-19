/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.KnotInsertion
public import PDE.Analysis.Approximation.Splines.NormalizedBasis
public import PDE.Analysis.Approximation.Splines.OrderedMinors
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Positivity.Finset

/-!
# Finite matrix form of B-spline knot insertion

Inserting one knot `value ∈ [t_position, t_(position+1)]` into a knot sequence
expresses each coarse B-spline as a nonnegative combination of two adjacent
refined B-splines, with coefficients `α_i` and `1 - α_(i+1)` (Boehm's knot
insertion formula, `coxDeBoorBasis_eq_knotInsertion`).  We arrange those
coefficients in a rectangular bidiagonal matrix, rows indexed by the
refined family and columns by the coarse family, and prove exact
factorizations for evaluation vectors and collocation matrices.  Because the
matrix is bidiagonal with nonnegative entries, every ordered minor is the
product of its diagonal entries, so the matrix is totally nonnegative in the
sense of `CAS.Splines.Matrix.IsOrderedMinorNonnegative`.  Composing such matrices is the
elementary step behind total positivity of B-spline collocation matrices.

## Main results

* `knotInsertionMatrix`: the `(count + 1) × count` refinement matrix built
  from `knotInsertionAlpha`.
* `knotInsertionMatrix_nonneg`: all entries are nonnegative when the inserted
  value lies in the prescribed knot interval.
* `det_submatrix_knotInsertionMatrix`: every ordered square minor equals the
  product of the selected diagonal entries.
* `knotInsertionMatrix_isOrderedMinorNonnegative`: total nonnegativity on
  ordered minors.
* `sum_refinedBasis_mul_knotInsertionMatrix` and
  `rectangularCollocationMatrix_eq_mul_knotInsertionMatrix`: a coarse
  B-spline is the refined basis paired with the corresponding column, and
  every collocation matrix factors as the refined collocation matrix times
  the refinement matrix.

The entries are the coefficients of (2.4) in de Boor and DeVore, who observe on p. 499 that a
product of bidiagonal matrices with nonnegative entries is totally positive by the Cauchy–Binet
formula.

## References

* W. Boehm, "Inserting new knots into B-spline curves", *Computer-Aided Design* 12 (1980),
  no. 4, 199-201. <https://doi.org/10.1016/0010-4485(80)90154-2>
* C. de Boor, *A Practical Guide to Splines*, revised edition, Applied Mathematical Sciences,
  Springer, 2001, Chapter XI, The B-Spline Series, Control Points, and Knot Insertion,
  pp. 131-144. <https://doi.org/10.1007/978-1-4612-6333-3_11>
* C. de Boor and R. DeVore, "A geometric proof of total positivity for spline interpolation",
  *Math. Comp.* 45 (1985), no. 172, 497-504, Section 2, (2.4) and (2.6), pp. 498-499.
  <https://doi.org/10.1090/S0025-5718-1985-0804938-2>
* S. Karlin, *Total Positivity*, Vol. I, Stanford University Press, 1968.
-/

@[expose] public section

namespace CAS.Splines

noncomputable section

open scoped BigOperators

/-- Evaluation matrix with independent row and basis index types. -/
def rectangularCollocationMatrix {𝕜 X rowIndex basisIndex : Type*}
    (basis : basisIndex → X → 𝕜) (points : rowIndex → X) :
    Matrix rowIndex basisIndex 𝕜 :=
  fun row column ↦ basis column (points row)

/-- Rectangular bidiagonal refinement matrix for one knot insertion.

Rows index the refined family and columns index the coarse family. -/
def knotInsertionMatrix
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (count : ℕ) :
    Matrix (Fin (count + 1)) (Fin count) ℝ :=
  fun refined coarse ↦
    (if refined = Fin.castSucc coarse then
        knotInsertionAlpha knots degree position value coarse.val
      else 0) +
      if refined = Fin.succ coarse then
        1 - knotInsertionAlpha knots degree position value (coarse.val + 1)
      else 0

/-- A diagonal refinement-matrix entry is the corresponding insertion coefficient. -/
@[simp]
theorem knotInsertionMatrix_castSucc_self
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (count : ℕ) (coarse : Fin count) :
    knotInsertionMatrix knots degree position value count
        (Fin.castSucc coarse) coarse =
      knotInsertionAlpha knots degree position value coarse.val := by
  have hne : Fin.castSucc coarse ≠ Fin.succ coarse := by
    intro heq
    have hval := congrArg Fin.val heq
    simp at hval
  simp [knotInsertionMatrix, hne]

/-- A subdiagonal refinement-matrix entry is the complementary insertion coefficient. -/
@[simp]
theorem knotInsertionMatrix_succ_self
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (count : ℕ) (coarse : Fin count) :
    knotInsertionMatrix knots degree position value count
        (Fin.succ coarse) coarse =
      1 -
        knotInsertionAlpha knots degree position value
          (coarse.val + 1) := by
  have hne : Fin.succ coarse ≠ Fin.castSucc coarse := by
    intro heq
    have hval := congrArg Fin.val heq
    simp at hval
  simp [knotInsertionMatrix, hne]

/-- Every entry of a one-knot refinement matrix is nonnegative. -/
theorem knotInsertionMatrix_nonneg
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (count : ℕ) (refined : Fin (count + 1)) (coarse : Fin count) :
    0 ≤ knotInsertionMatrix knots degree position value count refined coarse := by
  unfold knotInsertionMatrix
  apply add_nonneg
  · split_ifs
    · exact knotInsertionAlpha_nonneg
        knots degree position value hleft coarse.val
    · exact le_rfl
  · split_ifs
    · exact one_sub_knotInsertionAlpha_nonneg
        knots degree position value hright (coarse.val + 1)
    · exact le_rfl

/-- Every ordered square minor of a one-knot refinement matrix is the
product of its selected diagonal entries. -/
theorem det_submatrix_knotInsertionMatrix
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (count size : ℕ)
    (rows : Fin size → Fin (count + 1))
    (columns : Fin size → Fin count)
    (hrows : StrictMono rows)
    (hcolumns : StrictMono columns) :
    (knotInsertionMatrix knots degree position value count
        |>.submatrix rows columns).det =
      ∏ index,
        knotInsertionMatrix knots degree position value count
          (rows index) (columns index) := by
  rw [Matrix.det_apply']
  refine (Finset.sum_eq_single (1 : Equiv.Perm (Fin size)) ?_ ?_).trans ?_
  · intro permutation _ hpermutation
    have hproduct :
        (∏ index,
          knotInsertionMatrix knots degree position value count
            (rows (permutation index)) (columns index)) = 0 := by
      by_contra hproduct
      have hentry (index : Fin size) :
          knotInsertionMatrix knots degree position value count
              (rows (permutation index)) (columns index) ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mp hproduct index
          (Finset.mem_univ index)
      have hsupport (index : Fin size) :
          rows (permutation index) = Fin.castSucc (columns index) ∨
            rows (permutation index) = Fin.succ (columns index) := by
        by_contra hsupport
        rw [not_or] at hsupport
        exact hentry index (by
          simp [knotInsertionMatrix, hsupport.1, hsupport.2])
      have hpermutationMono : StrictMono (fun index ↦ permutation index) := by
        intro left right hindex
        by_contra hnot
        have hne : permutation right ≠ permutation left := by
          intro heq
          exact (ne_of_gt hindex) (permutation.injective heq)
        have hreverse : permutation right < permutation left :=
          lt_of_le_of_ne (le_of_not_gt hnot) hne
        have hrowReverse :
            (rows (permutation right)).val <
              (rows (permutation left)).val :=
          hrows hreverse
        have hcolumnForward :
            (columns left).val < (columns right).val :=
          hcolumns hindex
        have hleftUpper :
            (rows (permutation left)).val ≤
              (columns left).val + 1 := by
          rcases hsupport left with hsame | hnext
          · rw [hsame]
            simp
          · rw [hnext]
            simp
        have hrightLower :
            (columns right).val ≤
              (rows (permutation right)).val := by
          rcases hsupport right with hsame | hnext
          · rw [hsame]
            simp
          · rw [hnext]
            simp
        omega
      have hpermutationEq : permutation = 1 := by
        apply Equiv.ext
        intro index
        exact hpermutationMono.apply_eq
      exact hpermutation hpermutationEq
    have hsubmatrixProduct :
        (∏ index,
          (knotInsertionMatrix knots degree position value count
              |>.submatrix rows columns)
            (permutation index) index) = 0 := by
      simpa only [Matrix.submatrix_apply] using hproduct
    rw [hsubmatrixProduct, mul_zero]
  · simp
  · simp [Matrix.submatrix]

/-- One-knot refinement matrices are totally nonnegative on ordered
minors. -/
theorem knotInsertionMatrix_isOrderedMinorNonnegative
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (count : ℕ) :
    CAS.Splines.Matrix.IsOrderedMinorNonnegative
      (knotInsertionMatrix knots degree position value count) := by
  intro size rows columns hrows hcolumns
  rw [det_submatrix_knotInsertionMatrix
    knots degree position value count size rows columns hrows hcolumns]
  exact Finset.prod_nonneg fun index _ ↦
    knotInsertionMatrix_nonneg
      knots degree position value hleft hright count
        (rows index) (columns index)

/-- A refinement-matrix column evaluates to the corresponding coarse
B-spline. -/
theorem sum_refinedBasis_mul_knotInsertionMatrix
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (count : ℕ) (coarse : Fin count) (x : ℝ) :
    (∑ refined : Fin (count + 1),
          finiteCoxDeBoorBasis
            (insertKnotAfter knots position value hleft hright)
            degree (count + 1) refined x *
          knotInsertionMatrix knots degree position value count refined coarse) =
      finiteCoxDeBoorBasis knots degree count coarse x := by
  change
    (∑ refined : Fin (count + 1),
        coxDeBoorBasis
            (insertKnotAfter knots position value hleft hright)
            degree refined.val x *
          knotInsertionMatrix knots degree position value count refined coarse) =
      coxDeBoorBasis knots degree coarse.val x
  rw [coxDeBoorBasis_eq_knotInsertion
    knots position value hleft hright degree coarse.val x]
  simp only [knotInsertionMatrix, mul_add, Finset.sum_add_distrib]
  simp [mul_comm]

/-- Inserting one knot factors every rectangular collocation matrix through
the nonnegative bidiagonal refinement matrix. -/
theorem rectangularCollocationMatrix_eq_mul_knotInsertionMatrix
    (knots : KnotSequence) (degree position : ℕ) (value : ℝ)
    (hleft : knots position ≤ value)
    (hright : value ≤ knots (position + 1))
    (count rowCount : ℕ) (points : Fin rowCount → ℝ) :
    rectangularCollocationMatrix
        (finiteCoxDeBoorBasis knots degree count) points =
      rectangularCollocationMatrix
          (finiteCoxDeBoorBasis
            (insertKnotAfter knots position value hleft hright)
            degree (count + 1))
          points *
        knotInsertionMatrix knots degree position value count := by
  ext row coarse
  simp only [rectangularCollocationMatrix, Matrix.mul_apply]
  exact
    (sum_refinedBasis_mul_knotInsertionMatrix
      knots degree position value hleft hright count coarse (points row)).symm

end

end CAS.Splines
