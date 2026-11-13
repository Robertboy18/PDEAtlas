/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Positive
public import PDE.Analysis.Stability.FiniteTail
public import CAS.Continuum.Krawczyk.Interval

/-!
# Exact coercivity certificates for finite matrices

A real matrix `A` is dissipative with rate `rate ≥ 0` when `⟪A x, x⟫ ≤ -rate ‖x‖ ‖x‖` for all
`x`. A `RationalDissipativityCandidate` proposes a rational reference matrix `A`, a rate, a
rational matrix `L` and pivots `d` with

`-A - rate • 1 = L * diagonal d * Lᵀ`.

The rate and the pivots have type `ℚ≥0`, so their signs hold by construction, and
`certifyDissipativity` checks the matrix identity exactly. The identity makes `-A - rate • 1`
positive semidefinite over `ℝ`, which is the energy estimate for `A`. An interval matrix
enclosing the difference between a real target matrix and the reference bounds the operator norm
of that difference, and the two facts together form a `ValidatedDissipativityEstimate`.

## Main results

* `certifyDissipativity_sound`, `shifted_posSemidef_of_rational`: a successful check gives the
  factorization over `ℚ`, and hence positive semidefiniteness of the real shifted matrix.
* `matrixOperator_pairing_le_of_shift_posSemidef`, `reference_pairing_le`: the energy estimate
  `⟪A x, x⟫ ≤ -rate * ‖x‖ * ‖x‖`.
* `matrixOperator_sub_norm_le_of_intervals`: an entrywise enclosure of `target - reference` with
  a `CertifiesOperatorNorm` bound gives `‖target - reference‖ ≤ bound` for the operators.
* `validatedEstimateOfIntervals`: the resulting `ValidatedDissipativityEstimate`.
-/

@[expose] public section

noncomputable section

namespace CAS.Continuum.Coercivity

open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open PDE.Analysis.Stability
open CAS.Continuum.Krawczyk

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact-rational proposal for a dissipative reference matrix. -/
structure RationalDissipativityCandidate (n : Type*) where
  /-- Rational matrix used as the exactly certified reference operator. -/
  reference : Matrix n n ℚ
  /-- Proposed dissipation rate, intrinsically constrained to be nonnegative. -/
  rate : ℚ≥0
  /-- Congruence factor in the exact positive-semidefinite factorization. -/
  factor : Matrix n n ℚ
  /-- Nonnegative diagonal entries in the exact positive-semidefinite factorization. -/
  pivot : n → ℚ≥0

namespace RationalDissipativityCandidate

/-- Shifted matrix whose positive semidefiniteness proves dissipativity. -/
def shifted (candidate : RationalDissipativityCandidate n) : Matrix n n ℚ :=
  -candidate.reference - (candidate.rate : ℚ) • (1 : Matrix n n ℚ)

/-- Real cast of the rational reference matrix. -/
def realReference (candidate : RationalDissipativityCandidate n) : Matrix n n ℝ :=
  candidate.reference.map ((↑) : ℚ → ℝ)

/-- Real cast of the rational factor matrix. -/
def realFactor (candidate : RationalDissipativityCandidate n) : Matrix n n ℝ :=
  candidate.factor.map ((↑) : ℚ → ℝ)

/-- Real cast of the rational pivot vector. -/
def realPivot (candidate : RationalDissipativityCandidate n) : n → ℝ :=
  fun index ↦ (candidate.pivot index : ℝ)

end RationalDissipativityCandidate

/-- Decides the rational identity `-A - rate • 1 = L * diagonal d * Lᵀ`. -/
def certifyDissipativity
    (candidate : RationalDissipativityCandidate n) : Bool :=
  decide
    (candidate.shifted =
      candidate.factor *
        Matrix.diagonal (fun index ↦ (candidate.pivot index : ℚ)) *
        candidate.factor.transpose)

/-- If `certifyDissipativity candidate = true`, then `-A - rate • 1 = L * diagonal d * Lᵀ`
over `ℚ`. -/
theorem certifyDissipativity_sound
    {candidate : RationalDissipativityCandidate n}
    (hcertificate : certifyDissipativity candidate = true) :
    candidate.shifted =
      candidate.factor *
        Matrix.diagonal (fun index ↦ (candidate.pivot index : ℚ)) *
        candidate.factor.transpose := by
  simpa [certifyDissipativity] using hcertificate

/-- Rational factorization remains exact after casting every entry to the reals. -/
theorem real_factorization_of_rational
    (candidate : RationalDissipativityCandidate n)
    (hfactorization :
      candidate.shifted =
        candidate.factor *
          Matrix.diagonal (fun index ↦ (candidate.pivot index : ℚ)) *
          candidate.factor.transpose) :
    -candidate.realReference -
        (candidate.rate : ℝ) • (1 : Matrix n n ℝ) =
      candidate.realFactor *
        Matrix.diagonal candidate.realPivot *
          candidate.realFactor.transpose := by
  ext i j
  have hentry := congr_fun (congr_fun hfactorization i) j
  have hcast := congr_arg (fun value : ℚ ↦ (value : ℝ)) hentry
  by_cases hij : i = j <;>
    simpa [hij, RationalDissipativityCandidate.shifted,
      RationalDissipativityCandidate.realReference,
      RationalDissipativityCandidate.realFactor,
      RationalDissipativityCandidate.realPivot,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply] using hcast

/-- The checked rational congruence factorization proves positive semidefiniteness of the shifted
real reference matrix. -/
theorem shifted_posSemidef_of_rational
    (candidate : RationalDissipativityCandidate n)
    (hfactorization :
      candidate.shifted =
        candidate.factor *
          Matrix.diagonal (fun index ↦ (candidate.pivot index : ℚ)) *
          candidate.factor.transpose) :
    (-candidate.realReference -
      (candidate.rate : ℝ) • (1 : Matrix n n ℝ)).PosSemidef := by
  have hpivotReal : 0 ≤ candidate.realPivot := by
    intro index
    change (0 : ℝ) ≤ (candidate.pivot index : ℝ)
    exact_mod_cast (candidate.pivot index).property
  have hdiagonal :
      (Matrix.diagonal candidate.realPivot).PosSemidef :=
    Matrix.PosSemidef.diagonal hpivotReal
  have hproduct :=
    hdiagonal.mul_mul_conjTranspose_same candidate.realFactor
  have hconjTranspose :
      candidate.realFactor.conjTranspose =
        candidate.realFactor.transpose := by
    ext i j
    simp [Matrix.conjTranspose]
  have hproductTranspose :
      (candidate.realFactor *
        Matrix.diagonal candidate.realPivot *
          candidate.realFactor.transpose).PosSemidef := by
    rw [← hconjTranspose]
    exact hproduct
  rw [real_factorization_of_rational candidate hfactorization]
  exact hproductTranspose

/-- A positive semidefinite shifted matrix gives the corresponding Euclidean energy estimate. -/
theorem matrixOperator_pairing_le_of_shift_posSemidef
    (matrix : Matrix n n ℝ) (rate : ℝ)
    (hshift :
      (-matrix - rate • (1 : Matrix n n ℝ)).PosSemidef)
    (state : EuclideanSpace ℝ n) :
    ⟪matrixOperator matrix state, state⟫ ≤
      -rate * ‖state‖ * ‖state‖ := by
  have hpositive :
      ((-matrix - rate • (1 : Matrix n n ℝ)).toEuclideanLin).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hshift
  have hnonneg := hpositive.inner_nonneg_left state
  have haction :
      (-matrix - rate • (1 : Matrix n n ℝ)).toEuclideanLin state =
        -matrix.toEuclideanLin state - rate • state := by
    simp
  rw [haction, inner_sub_left, inner_neg_left, real_inner_smul_left,
    real_inner_self_eq_norm_mul_norm] at hnonneg
  change
    ⟪matrix.toEuclideanLin state, state⟫ ≤
      -rate * ‖state‖ * ‖state‖
  linarith

/-- A successful exact-rational certificate proves dissipativity of its real reference matrix. -/
theorem reference_pairing_le
    (candidate : RationalDissipativityCandidate n)
    (hcertificate : certifyDissipativity candidate = true)
    (state : EuclideanSpace ℝ n) :
    ⟪matrixOperator candidate.realReference state, state⟫ ≤
      -(candidate.rate : ℝ) * ‖state‖ * ‖state‖ := by
  have hsound := certifyDissipativity_sound hcertificate
  exact matrixOperator_pairing_le_of_shift_posSemidef
    candidate.realReference (candidate.rate : ℝ)
    (shifted_posSemidef_of_rational candidate hsound)
    state

/-- An interval enclosure of a matrix difference gives the corresponding continuous-operator
norm bound. -/
theorem matrixOperator_sub_norm_le_of_intervals
    {target reference : Matrix n n ℝ}
    {bounds : Matrix n n RationalInterval}
    {bound : NNReal}
    (hencloses :
      ∀ i j, (bounds i j).MemReal ((target - reference) i j))
    (hnorm : CertifiesOperatorNorm bounds bound) :
    ‖matrixOperator target - matrixOperator reference‖ ≤ (bound : ℝ) := by
  have hmatrixNN :
      ‖target - reference‖₊ ≤ bound :=
    hnorm (target - reference) hencloses
  have hmatrix : ‖target - reference‖ ≤ (bound : ℝ) := by
    exact_mod_cast hmatrixNN
  rw [Matrix.cstar_norm_def] at hmatrix
  simpa only [matrixOperator, map_sub] using hmatrix

/-- Build the abstract validated dissipativity estimate from an exact rational factorization and
an interval enclosure of the target-reference difference. -/
def validatedEstimateOfIntervals
    (candidate : RationalDissipativityCandidate n)
    (hcertificate : certifyDissipativity candidate = true)
    (target : Matrix n n ℝ)
    (differenceBounds : Matrix n n RationalInterval)
    (errorBound : NNReal)
    (hencloses :
      ∀ i j,
        (differenceBounds i j).MemReal
          ((target - candidate.realReference) i j))
    (hnorm :
      CertifiesOperatorNorm differenceBounds errorBound) :
    ValidatedDissipativityEstimate (EuclideanSpace ℝ n) where
  target := matrixOperator target
  reference := matrixOperator candidate.realReference
  referenceRate := candidate.rate
  errorBound := errorBound
  reference_pairing_le := reference_pairing_le candidate hcertificate
  difference_norm_le :=
    matrixOperator_sub_norm_le_of_intervals hencloses hnorm

end CAS.Continuum.Coercivity
