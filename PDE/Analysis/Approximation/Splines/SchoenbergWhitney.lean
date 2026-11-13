/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Vandermonde
public import PDE.Analysis.Approximation.Splines.NormalizedBasis
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Positivity.Finset

/-!
# Schoenberg–Whitney collocation certificates

Positive spline collocation determinants can be certified by finite algebra.  A validated
backend may provide an exact `LDU` factorization.  Lean checks the factorization, triangular
structure, unit diagonals, and positivity of every pivot before deriving strict positivity
of the determinant and linear independence of the sampled basis.

The geometric Schoenberg–Whitney theorem, which connects knot geometry to
positive collocation determinants, is proved in `SchoenbergWhitneyRefinement`.

## References

* I. J. Schoenberg and A. Whitney, "On Pólya frequency functions. III. The positivity of
  translation determinants with an application to the interpolation problem by spline curves",
  *Trans. Amer. Math. Soc.* 74 (1953), 246-259, (2.9), p. 257, and Theorem 2, p. 258.
  <https://doi.org/10.1090/S0002-9947-1953-0053177-X>
* C. de Boor, *A Practical Guide to Splines*, revised edition, Applied Mathematical Sciences,
  Springer, 2001, Chapter XIII, Spline Interpolation, pp. 171-205.
  <https://doi.org/10.1007/978-1-4612-6333-3_13>
-/

@[expose] public section

noncomputable section

namespace CAS.Splines

open scoped BigOperators

/-- The classical Schoenberg–Whitney point inequalities for a finite B-spline family. -/
def SchoenbergWhitneyCondition
    (knots : KnotSequence) (degree count : ℕ)
    (points : Fin count → ℝ) : Prop :=
  StrictMono points ∧
    ∀ index : Fin count,
      knots index.val < points index ∧
        points index < knots (index.val + degree + 1)

namespace SchoenbergWhitneyCondition

/-- Schoenberg–Whitney points are strictly ordered. -/
theorem strictMono
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (condition :
      SchoenbergWhitneyCondition knots degree count points) :
    StrictMono points :=
  condition.1

/-- Every sampling point lies in the interior of its canonical B-spline support. -/
theorem mem_support_interior
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (condition :
      SchoenbergWhitneyCondition knots degree count points)
    (index : Fin count) :
    points index ∈
      Set.Ioo (knots index.val)
        (knots (index.val + degree + 1)) :=
  condition.2 index

/-- The diagonal entry selected by every Schoenberg–Whitney inequality is
strictly positive, including at repeated internal knots. -/
theorem diagonal_pos
    {knots : KnotSequence} {degree count : ℕ}
    {points : Fin count → ℝ}
    (condition :
      SchoenbergWhitneyCondition knots degree count points)
    (index : Fin count) :
    0 <
      collocationMatrix
        (finiteCoxDeBoorBasis knots degree count) points
        index index :=
  coxDeBoorBasis_pos_of_mem_support_interior knots degree index.val
    (points index) (condition.2 index).1 (condition.2 index).2

end SchoenbergWhitneyCondition

/-- Exact positive `LDU` data for a square matrix.

The certificate stores no determinant assertion.  Its soundness theorem derives determinant
positivity from matrix multiplication, triangular determinant formulas, and positive pivots. -/
structure PositiveLDUCertificate {𝕜 : Type*}
    [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {count : ℕ} (matrix : Matrix (Fin count) (Fin count) 𝕜) where
  /-- Unit lower-triangular factor. -/
  lower : Matrix (Fin count) (Fin count) 𝕜
  /-- Positive diagonal pivots. -/
  pivot : Fin count → Set.Ioi (0 : 𝕜)
  /-- Unit upper-triangular factor. -/
  upper : Matrix (Fin count) (Fin count) 𝕜
  /-- Exact checked factorization. -/
  factorization :
    matrix = lower * Matrix.diagonal (fun index ↦ (pivot index : 𝕜)) * upper
  /-- Entries above the lower factor's diagonal vanish. -/
  lower_triangular : lower.IsLowerTriangular
  /-- The lower factor has unit diagonal. -/
  lower_diagonal : ∀ index, lower index index = 1
  /-- Entries below the upper factor's diagonal vanish. -/
  upper_triangular : upper.IsUpperTriangular
  /-- The upper factor has unit diagonal. -/
  upper_diagonal : ∀ index, upper index index = 1

namespace PositiveLDUCertificate

/-- A valid positive `LDU` certificate proves strict determinant positivity. -/
theorem det_pos {count : ℕ}
    {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {matrix : Matrix (Fin count) (Fin count) 𝕜}
    (certificate : PositiveLDUCertificate matrix) :
    0 < matrix.det := by
  rw [certificate.factorization, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal,
    Matrix.det_of_isLowerTriangular certificate.lower
      certificate.lower_triangular,
    Matrix.det_of_isUpperTriangular certificate.upper_triangular]
  simp_rw [certificate.lower_diagonal, certificate.upper_diagonal]
  simp only [Finset.prod_const_one, one_mul, mul_one]
  exact Finset.prod_pos fun index _ ↦ (certificate.pivot index).property

/-- A valid positive `LDU` certificate proves nonsingularity. -/
theorem det_ne_zero {count : ℕ}
    {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {matrix : Matrix (Fin count) (Fin count) 𝕜}
    (certificate : PositiveLDUCertificate matrix) :
    matrix.det ≠ 0 :=
  ne_of_gt certificate.det_pos

/-- Positive factorization of a collocation matrix proves linear independence of the family. -/
theorem linearIndependent
    {𝕜 X : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {count : ℕ}
    {basis : Fin count → X → 𝕜} {points : Fin count → X}
    (certificate :
      PositiveLDUCertificate (collocationMatrix basis points)) :
    LinearIndependent 𝕜 basis :=
  linearIndependent_of_collocation_det_ne_zero certificate.det_ne_zero

end PositiveLDUCertificate

/-- Collocation matrix of the degree-`degree` Bernstein basis at `degree + 1` points. -/
def bernsteinCollocationMatrix (degree : ℕ)
    (points : Fin (degree + 1) → ℝ) :
    Matrix (Fin (degree + 1)) (Fin (degree + 1)) ℝ :=
  fun row column ↦
    (bernsteinPolynomial ℝ degree column.val).eval (points row)

/-- Bernstein collocation is a projective Vandermonde matrix followed by positive
binomial column scaling. -/
theorem bernsteinCollocationMatrix_eq_projVandermonde_mul_diagonal
    (degree : ℕ) (points : Fin (degree + 1) → ℝ) :
    bernsteinCollocationMatrix degree points =
      Matrix.projVandermonde points (fun index ↦ 1 - points index) *
      Matrix.diagonal
          (fun index : Fin (degree + 1) ↦
            (degree.choose index.val : ℝ)) := by
  ext row column
  simp [bernsteinCollocationMatrix, Matrix.projVandermonde_apply,
    bernsteinPolynomial]
  ring

/-- Exact determinant formula for Bernstein collocation. -/
theorem det_bernsteinCollocationMatrix
    (degree : ℕ) (points : Fin (degree + 1) → ℝ) :
    (bernsteinCollocationMatrix degree points).det =
      (∏ row : Fin (degree + 1),
        ∏ column ∈ Finset.Ioi row,
          (points column - points row)) *
      ∏ index : Fin (degree + 1),
        (degree.choose index.val : ℝ) := by
  rw [bernsteinCollocationMatrix_eq_projVandermonde_mul_diagonal,
    Matrix.det_mul, Matrix.det_projVandermonde, Matrix.det_diagonal]
  congr 1
  apply Finset.prod_congr rfl
  intro row _
  apply Finset.prod_congr rfl
  intro column _
  ring

/-- Strictly ordered points give a strictly positive Bernstein collocation determinant. -/
theorem det_bernsteinCollocationMatrix_pos
    (degree : ℕ) {points : Fin (degree + 1) → ℝ}
    (hpoints : StrictMono points) :
    0 < (bernsteinCollocationMatrix degree points).det := by
  rw [det_bernsteinCollocationMatrix]
  apply mul_pos
  · exact Finset.prod_pos fun row _ ↦
      Finset.prod_pos fun column hcolumn ↦
        sub_pos.mpr (hpoints (Finset.mem_Ioi.mp hcolumn))
  · exact Finset.prod_pos fun index _ ↦ by
      exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ index.isLt)

/-- The Bernstein basis is linearly independent as real-valued functions, witnessed by
any strictly increasing family of `degree + 1` collocation points. -/
theorem bernsteinFunction_linearIndependent_of_strictMono
    (degree : ℕ) {points : Fin (degree + 1) → ℝ}
    (hpoints : StrictMono points) :
    LinearIndependent ℝ
      (fun index : Fin (degree + 1) ↦
        fun x : ℝ ↦
          (bernsteinPolynomial ℝ degree index.val).eval x) := by
  apply linearIndependent_of_collocation_det_ne_zero
    (points := points)
  exact ne_of_gt (det_bernsteinCollocationMatrix_pos degree hpoints)

/-- Affine transport to a positively oriented panel preserves strict point ordering. -/
theorem strictMono_panelCoordinate
    {a b : ℝ} (hab : a < b) {count : ℕ}
    {points : Fin count → ℝ} (hpoints : StrictMono points) :
    StrictMono (fun index ↦ panelCoordinate a b (points index)) := by
  intro left right hindex
  apply (div_lt_div_iff_of_pos_right (sub_pos.mpr hab)).mpr
  exact sub_lt_sub_right (hpoints hindex) a

/-- Panel points reduce the closed-endpoint, one-panel spline realization exactly to
Bernstein collocation in the affine panel coordinate. -/
theorem collocationMatrix_clampedSinglePanel_eq_bernstein
    {a b : ℝ} (degree : ℕ)
    {points : Fin (degree + 1) → ℝ}
    (hpoints : ∀ index, points index ∈ Set.Icc a b) :
    collocationMatrix
        (clampedSinglePanelBSpline a b degree) points =
      bernsteinCollocationMatrix degree
        (fun index ↦ panelCoordinate a b (points index)) := by
  ext row column
  simp [collocationMatrix, clampedSinglePanelBSpline,
    bernsteinCollocationMatrix, hpoints row]

/-- Strict positivity of one-panel Bernstein collocation.

Any strictly increasing family of `degree + 1` points in the closed panel gives a strictly
positive collocation determinant. Unlike the strict Cox–de Boor theorem, this closed-endpoint
realization also permits sampling at `a` or `b`. -/
theorem det_clampedSinglePanel_collocation_pos
    {a b : ℝ} (hab : a < b) (degree : ℕ)
    {points : Fin (degree + 1) → ℝ}
    (hmono : StrictMono points)
    (hinside : ∀ index, points index ∈ Set.Icc a b) :
    0 <
      (collocationMatrix
        (clampedSinglePanelBSpline a b degree) points).det := by
  rw [collocationMatrix_clampedSinglePanel_eq_bernstein degree
    hinside]
  exact det_bernsteinCollocationMatrix_pos degree
    (strictMono_panelCoordinate hab hmono)

/-- The one-panel normalized Bernstein realization, certified by the
Vandermonde determinant formula for Bernstein collocation. -/
def clampedSinglePanelCertifiedNormalizedBasis
    (a b : ℝ) (degree : ℕ) (hab : a < b)
    (points : Fin (degree + 1) → ℝ)
    (hmono : StrictMono points)
    (hinside : ∀ index, points index ∈ Set.Icc a b) :
    CertifiedNormalizedBasis ℝ (Fin (degree + 1)) :=
  (clampedSinglePanelNormalizedBasis a b degree hab).certifyByCollocation
    points
    (ne_of_gt
      (det_clampedSinglePanel_collocation_pos
        hab degree hmono hinside))

end CAS.Splines
