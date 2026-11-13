/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.KnotInsertionMatrix
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Positivity.Finset

/-!
# Iterated finite B-spline knot refinement

A finite sequence of knot insertions composes the bidiagonal matrices of
`KnotInsertionMatrix` into one rectangular basis-change matrix from a fixed
coarse B-spline family to the refined family.  `KnotRefinement` records that
matrix together with the two properties that survive composition: the exact
collocation factorization (coarse collocation equals refined collocation times
the matrix) and total nonnegativity of every ordered minor, the latter through
the Cauchy–Binet formula `CAS.Splines.Matrix.IsOrderedMinorNonnegative.mul`.  A companion
structure tracks a strictly positive square minor through the refinement.
Once the refined knots are dense enough that the refined basis evaluates as a
Kronecker delta at the chosen points, this gives strict positivity of the
original collocation determinant.

## Main definitions and results

* `KnotRefinement`: refined knots, refined count, the basis-change matrix,
  and proofs of the collocation factorization and ordered-minor
  nonnegativity.
* `KnotRefinement.refl`, `KnotRefinement.insertKnot`: the empty refinement
  and extension by one admissible insertion.
* `KnotRefinement.PositiveSelection`: increasing refined rows whose minor
  against all coarse columns is positive, with `refl` and `insertKnot`
  transport (`CAS.Splines.Matrix.orderedMinor_mul_pos_of_witness`).
* `KnotRefinement.PositiveSelection.det_collocation_pos_of_eq_ite`: if the
  refined basis is the Kronecker row selector at the tracked indices, the
  coarse collocation determinant is strictly positive.

The composition is (2.6) of de Boor and DeVore, and the positivity criterion is the last step
of their proof of Theorem 2, where the knots are refined until (4.9) holds and the coarse minor
is expanded by (4.4a).

## References

* C. de Boor, *A Practical Guide to Splines*, revised edition, Applied Mathematical Sciences,
  Springer, 2001, Chapter XI, The B-Spline Series, Control Points, and Knot Insertion,
  pp. 131-144. <https://doi.org/10.1007/978-1-4612-6333-3_11>
* C. de Boor and R. DeVore, "A geometric proof of total positivity for spline interpolation",
  *Math. Comp.* 45 (1985), no. 172, 497-504, (2.6), p. 499, (4.4a), p. 500, and Theorem 2 and
  its proof, (4.9), p. 502. <https://doi.org/10.1090/S0025-5718-1985-0804938-2>
* S. Karlin, *Total Positivity*, Vol. I, Stanford University Press, 1968.
-/

@[expose] public section

namespace CAS.Splines

noncomputable section

open scoped BigOperators

/-- A refined knot sequence together with its exact finite basis-change
matrix back to a fixed coarse B-spline family. -/
structure KnotRefinement
    (coarseKnots : KnotSequence) (degree coarseCount : ℕ) where
  /-- Knot sequence after finitely many insertions. -/
  refinedKnots : KnotSequence
  /-- Number of basis functions retained after refinement. -/
  refinedCount : ℕ
  /-- Rows are refined basis indices and columns are coarse basis indices. -/
  matrix : Matrix (Fin refinedCount) (Fin coarseCount) ℝ
  /-- Every finite collocation matrix factors through the refinement matrix. -/
  collocation_factorization :
    ∀ (rowCount : ℕ) (points : Fin rowCount → ℝ),
      rectangularCollocationMatrix
          (finiteCoxDeBoorBasis coarseKnots degree coarseCount) points =
        rectangularCollocationMatrix
            (finiteCoxDeBoorBasis refinedKnots degree refinedCount) points *
          matrix
  /-- Refinement preserves nonnegativity of all ordered minors. -/
  isOrderedMinorNonnegative : CAS.Splines.Matrix.IsOrderedMinorNonnegative matrix

namespace KnotRefinement

/-- The empty refinement. -/
def refl (knots : KnotSequence) (degree count : ℕ) :
    KnotRefinement knots degree count where
  refinedKnots := knots
  refinedCount := count
  matrix := 1
  collocation_factorization := by
    intro rowCount points
    exact (Matrix.mul_one
      (rectangularCollocationMatrix
        (finiteCoxDeBoorBasis knots degree count) points)).symm
  isOrderedMinorNonnegative := CAS.Splines.Matrix.isOrderedMinorNonnegative_one count

/-- Extend a refinement by one admissible knot insertion. -/
def insertKnot
    {coarseKnots : KnotSequence} {degree coarseCount : ℕ}
    (refinement : KnotRefinement coarseKnots degree coarseCount)
    (position : ℕ) (value : ℝ)
    (hleft : refinement.refinedKnots position ≤ value)
    (hright : value ≤ refinement.refinedKnots (position + 1)) :
    KnotRefinement coarseKnots degree coarseCount where
  refinedKnots :=
    insertKnotAfter refinement.refinedKnots position value hleft hright
  refinedCount := refinement.refinedCount + 1
  matrix :=
    knotInsertionMatrix refinement.refinedKnots degree position value
        refinement.refinedCount *
      refinement.matrix
  collocation_factorization := by
    intro rowCount points
    calc
      rectangularCollocationMatrix
          (finiteCoxDeBoorBasis coarseKnots degree coarseCount) points =
          rectangularCollocationMatrix
              (finiteCoxDeBoorBasis refinement.refinedKnots degree
                refinement.refinedCount) points *
            refinement.matrix :=
        refinement.collocation_factorization rowCount points
      _ =
          (rectangularCollocationMatrix
              (finiteCoxDeBoorBasis
                (insertKnotAfter refinement.refinedKnots position value
                  hleft hright)
                degree (refinement.refinedCount + 1))
              points *
            knotInsertionMatrix refinement.refinedKnots degree position value
              refinement.refinedCount) *
            refinement.matrix := by
        rw [← rectangularCollocationMatrix_eq_mul_knotInsertionMatrix
          refinement.refinedKnots degree position value hleft hright
          refinement.refinedCount rowCount points]
      _ =
          rectangularCollocationMatrix
              (finiteCoxDeBoorBasis
                (insertKnotAfter refinement.refinedKnots position value
                  hleft hright)
                degree (refinement.refinedCount + 1))
              points *
            (knotInsertionMatrix refinement.refinedKnots degree position value
                refinement.refinedCount *
              refinement.matrix) := by
        rw [Matrix.mul_assoc]
  isOrderedMinorNonnegative :=
    CAS.Splines.Matrix.IsOrderedMinorNonnegative.mul
      (knotInsertionMatrix_isOrderedMinorNonnegative
        refinement.refinedKnots degree position value hleft hright
        refinement.refinedCount)
      refinement.isOrderedMinorNonnegative

/-- A strictly increasing set of refined rows whose minor against all coarse
columns is strictly positive. -/
structure PositiveSelection
    {coarseKnots : KnotSequence} {degree coarseCount : ℕ}
    (refinement : KnotRefinement coarseKnots degree coarseCount) where
  /-- Selected refined basis indices, in ambient order. -/
  selection : Fin coarseCount → Fin refinement.refinedCount
  /-- The selected indices retain their ambient order. -/
  strictMono : StrictMono selection
  /-- The corresponding square refinement minor is strictly positive. -/
  minor_pos :
    0 <
      (refinement.matrix.submatrix selection
        (id : Fin coarseCount → Fin coarseCount)).det

/-- The identity refinement has the evident positive selection. -/
def PositiveSelection.refl
    (knots : KnotSequence) (degree count : ℕ) :
    PositiveSelection (KnotRefinement.refl knots degree count) where
  selection := id
  strictMono := strictMono_id
  minor_pos := by
    simp [KnotRefinement.refl]

/-- Transport a positive selection through one knot insertion.

It suffices to choose increasing refined rows for which every selected entry
of the one-step bidiagonal matrix is positive. -/
def PositiveSelection.insertKnot
    {coarseKnots : KnotSequence} {degree coarseCount : ℕ}
    {refinement : KnotRefinement coarseKnots degree coarseCount}
    (positive : PositiveSelection refinement)
    (position : ℕ) (value : ℝ)
    (hleft : refinement.refinedKnots position ≤ value)
    (hright : value ≤ refinement.refinedKnots (position + 1))
    (nextSelection :
      Fin coarseCount → Fin (refinement.refinedCount + 1))
    (hnext : StrictMono nextSelection)
    (hentry : ∀ index,
      0 <
        knotInsertionMatrix refinement.refinedKnots degree position value
          refinement.refinedCount
          (nextSelection index) (positive.selection index)) :
    PositiveSelection
      (refinement.insertKnot position value hleft hright) where
  selection := nextSelection
  strictMono := hnext
  minor_pos := by
    apply CAS.Splines.Matrix.orderedMinor_mul_pos_of_witness
      (knotInsertionMatrix_isOrderedMinorNonnegative
        refinement.refinedKnots degree position value hleft hright
        refinement.refinedCount)
      refinement.isOrderedMinorNonnegative
      nextSelection
      (id : Fin coarseCount → Fin coarseCount)
      (OrderEmbedding.ofStrictMono positive.selection positive.strictMono)
    · rw [OrderEmbedding.coe_ofStrictMono, det_submatrix_knotInsertionMatrix
        refinement.refinedKnots degree position value
        refinement.refinedCount coarseCount
        nextSelection positive.selection hnext positive.strictMono]
      exact Finset.prod_pos fun index _ ↦ hentry index
    · exact positive.minor_pos

/-- If the refined basis evaluates as the Kronecker row selector at the
tracked indices, the original collocation determinant is strictly positive. -/
theorem PositiveSelection.det_collocation_pos_of_eq_ite
    {coarseKnots : KnotSequence} {degree coarseCount : ℕ}
    {refinement : KnotRefinement coarseKnots degree coarseCount}
    (positive : PositiveSelection refinement)
    (points : Fin coarseCount → ℝ)
    (hevaluation : ∀ row column,
      finiteCoxDeBoorBasis refinement.refinedKnots degree
          refinement.refinedCount column (points row) =
        if column = positive.selection row then 1 else 0) :
    0 <
      (collocationMatrix
        (finiteCoxDeBoorBasis coarseKnots degree coarseCount)
        points).det := by
  have hfactorization :=
    refinement.collocation_factorization coarseCount points
  have hrectangular :
      rectangularCollocationMatrix
          (finiteCoxDeBoorBasis coarseKnots degree coarseCount) points =
        collocationMatrix
          (finiteCoxDeBoorBasis coarseKnots degree coarseCount) points :=
    rfl
  rw [hrectangular] at hfactorization
  rw [hfactorization]
  have hproduct :
      rectangularCollocationMatrix
            (finiteCoxDeBoorBasis refinement.refinedKnots degree
              refinement.refinedCount)
            points *
          refinement.matrix =
        refinement.matrix.submatrix positive.selection
          (id : Fin coarseCount → Fin coarseCount) := by
    ext row column
    simp only [Matrix.mul_apply, rectangularCollocationMatrix,
      Matrix.submatrix_apply, id_eq, hevaluation]
    simp
  rw [hproduct]
  exact positive.minor_pos

end KnotRefinement

end

end CAS.Splines
