/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.RingTheory.Polynomial.Bernstein
public import PDE.Analysis.Approximation.Splines.CoxDeBoor
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.Positivity.Finset

/-!
# Normalized positive spline bases

A finite B-spline family is especially useful for certified approximation because its basis
functions are nonnegative and form a partition of unity.  Those two facts turn coefficient
bounds into pointwise bounds without estimating cancellation.  `NormalizedPositiveBasis`
records these two facts, and we prove the resulting enclosure and perturbation theorems.
`CertifiedNormalizedBasis` additionally records linear independence, obtained
from a nonsingular collocation matrix by `certifyByCollocation`;
`clampedSinglePanelCertifiedNormalizedBasis` in `SchoenbergWhitney` constructs this
certificate for the clamped one-panel basis. Positivity and partition of unity alone suffice
for the enclosure estimates.

We also define the standard open-clamped, one-panel B-spline family.  On one panel the
degree-`p` B-splines are exactly the Bernstein polynomials after affine transport to `[0,1]`.
The definition uses that closed form; the arbitrary-knot family is `coxDeBoorBasis`.

## References

* C. de Boor, *A Practical Guide to Splines*, revised edition, Applied Mathematical Sciences,
  Springer, 2001, Chapter IX, The Representation of PP Functions by B-Splines, pp. 87-107.
  <https://doi.org/10.1007/978-1-4612-6333-3_9>
* R. T. Farouki, "The Bernstein polynomial basis: a centennial retrospective",
  *Comput. Aided Geom. Design* 29 (2012), no. 6, 379-419.
  <https://doi.org/10.1016/j.cagd.2012.03.001>
-/

@[expose] public section

noncomputable section

namespace CAS.Splines

open Set
open scoped BigOperators _root_.Polynomial

/-- A finite family of nonnegative functions forming a partition of unity on a carrier. -/
structure NormalizedPositiveBasis
    (X : Type*) (ι : Type*) [Fintype ι] where
  /-- Region on which normalization is certified. -/
  carrier : Set X
  /-- Basis function family. -/
  basis : ι → X → ℝ
  /-- Basis functions are nonnegative on the carrier. -/
  nonneg_on : ∀ i x, x ∈ carrier → 0 ≤ basis i x
  /-- Basis functions sum to one on the carrier. -/
  sum_eq_one_on : ∀ x, x ∈ carrier → ∑ i, basis i x = 1

/-- A normalized positive basis together with a linear-independence certificate. -/
structure CertifiedNormalizedBasis
    (X : Type*) (ι : Type*) [Fintype ι]
    extends NormalizedPositiveBasis X ι where
  /-- The basis functions are linearly independent as real-valued functions. -/
  linearIndependent_basis : LinearIndependent ℝ basis

/-- Evaluation matrix of a function family at a matching family of points. -/
def collocationMatrix {𝕜 X ι : Type*}
    (basis : ι → X → 𝕜) (points : ι → X) : Matrix ι ι 𝕜 :=
  fun row column ↦ basis column (points row)

/-- A nonsingular collocation matrix certifies linear independence of a finite function
family. -/
theorem linearIndependent_of_collocation_det_ne_zero
    {𝕜 X ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]
    {basis : ι → X → 𝕜} {points : ι → X}
    (hdet : (collocationMatrix basis points).det ≠ 0) :
    LinearIndependent 𝕜 basis := by
  rw [Fintype.linearIndependent_iff]
  intro coefficient hcombination
  have hmul :
      Matrix.mulVec (collocationMatrix basis points) coefficient = 0 := by
    funext row
    have hrow := congrFun hcombination (points row)
    have hrow' : (∑ i, coefficient i * basis i (points row)) = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] using hrow
    simpa [collocationMatrix, Matrix.mulVec, dotProduct, mul_comm] using hrow'
  have hzero := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  exact fun i ↦ congrFun hzero i

namespace NormalizedPositiveBasis

variable {X : Type*} {ι : Type*} [Fintype ι]

/-- A normalized positive basis becomes certified once one collocation determinant is
proved nonzero. -/
def certifyByCollocation (B : NormalizedPositiveBasis X ι)
    [DecidableEq ι] (points : ι → X)
    (hdet : (collocationMatrix B.basis points).det ≠ 0) :
    CertifiedNormalizedBasis X ι where
  toNormalizedPositiveBasis := B
  linearIndependent_basis :=
    linearIndependent_of_collocation_det_ne_zero hdet

/-- Linear expansion in a normalized positive basis. -/
def expansion (B : NormalizedPositiveBasis X ι)
    (coefficient : ι → ℝ) (x : X) : ℝ :=
  ∑ i, coefficient i * B.basis i x

/-- Constant coefficients reproduce the same constant on the carrier. -/
theorem expansion_const (B : NormalizedPositiveBasis X ι)
    (constant : ℝ) {x : X} (hx : x ∈ B.carrier) :
    B.expansion (fun _ ↦ constant) x = constant := by
  unfold expansion
  rw [← Finset.mul_sum, B.sum_eq_one_on x hx, mul_one]

/-- Coefficientwise upper bounds pass directly to the spline expansion. -/
theorem expansion_le (B : NormalizedPositiveBasis X ι)
    {coefficient : ι → ℝ} {upper : ℝ} {x : X}
    (hcoefficient : ∀ i, coefficient i ≤ upper)
    (hx : x ∈ B.carrier) :
    B.expansion coefficient x ≤ upper := by
  unfold expansion
  calc
    (∑ i, coefficient i * B.basis i x) ≤
        ∑ i, upper * B.basis i x :=
      Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right (hcoefficient i)
          (B.nonneg_on i x hx)
    _ = upper * ∑ i, B.basis i x := by rw [Finset.mul_sum]
    _ = upper := by rw [B.sum_eq_one_on x hx, mul_one]

/-- Coefficientwise lower bounds pass directly to the spline expansion. -/
theorem le_expansion (B : NormalizedPositiveBasis X ι)
    {coefficient : ι → ℝ} {lower : ℝ} {x : X}
    (hcoefficient : ∀ i, lower ≤ coefficient i)
    (hx : x ∈ B.carrier) :
    lower ≤ B.expansion coefficient x := by
  unfold expansion
  calc
    lower = lower * ∑ i, B.basis i x := by
      rw [B.sum_eq_one_on x hx, mul_one]
    _ = ∑ i, lower * B.basis i x := by rw [Finset.mul_sum]
    _ ≤ ∑ i, coefficient i * B.basis i x :=
      Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right (hcoefficient i)
          (B.nonneg_on i x hx)

/-- A coefficient interval encloses the whole spline expansion pointwise. -/
theorem expansion_mem_Icc (B : NormalizedPositiveBasis X ι)
    {coefficient : ι → ℝ} {lower upper : ℝ} {x : X}
    (hlower : ∀ i, lower ≤ coefficient i)
    (hupper : ∀ i, coefficient i ≤ upper)
    (hx : x ∈ B.carrier) :
    B.expansion coefficient x ∈ Icc lower upper :=
  ⟨B.le_expansion hlower hx, B.expansion_le hupper hx⟩

/-- A uniform absolute coefficient bound is a pointwise absolute bound for the expansion. -/
theorem abs_expansion_le (B : NormalizedPositiveBasis X ι)
    {coefficient : ι → ℝ} {bound : ℝ} {x : X}
    (hcoefficient : ∀ i, |coefficient i| ≤ bound)
    (hx : x ∈ B.carrier) :
    |B.expansion coefficient x| ≤ bound := by
  rw [abs_le]
  constructor
  · exact B.le_expansion (fun i ↦ (abs_le.mp (hcoefficient i)).1) hx
  · exact B.expansion_le (fun i ↦ (abs_le.mp (hcoefficient i)).2) hx

/-- Expansion commutes with coefficient subtraction. -/
theorem expansion_sub (B : NormalizedPositiveBasis X ι)
    (left right : ι → ℝ) (x : X) :
    B.expansion left x - B.expansion right x =
      B.expansion (fun i ↦ left i - right i) x := by
  unfold expansion
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Uniform coefficient perturbations produce the same uniform pointwise error bound. -/
theorem abs_expansion_sub_expansion_le
    (B : NormalizedPositiveBasis X ι)
    {left right : ι → ℝ} {error : ℝ} {x : X}
    (hcoefficient : ∀ i, |left i - right i| ≤ error)
    (hx : x ∈ B.carrier) :
    |B.expansion left x - B.expansion right x| ≤ error := by
  rw [B.expansion_sub]
  exact B.abs_expansion_le hcoefficient hx

end NormalizedPositiveBasis

/-- A finite initial segment of the Cox–de Boor family. -/
def finiteCoxDeBoorBasis (knots : KnotSequence)
    (degree count : ℕ) (index : Fin count) (x : ℝ) : ℝ :=
  coxDeBoorBasis knots degree index.val x

/-- Every member of a finite Cox–de Boor family is nonnegative. -/
theorem finiteCoxDeBoorBasis_nonneg
    (knots : KnotSequence) (degree count : ℕ)
    (index : Fin count) (x : ℝ) :
    0 ≤ finiteCoxDeBoorBasis knots degree count index x :=
  coxDeBoorBasis_nonneg knots degree index.val x

/-- Consecutive degree-zero Cox–de Boor indicators sum to one between the
first and final knot. -/
theorem sum_finiteCoxDeBoorBasis_zero_eq_one
    (knots : KnotSequence) (count : ℕ) {x : ℝ}
    (hx : x ∈ Ico (knots 0) (knots count)) :
    (∑ index : Fin count,
      finiteCoxDeBoorBasis knots 0 count index x) = 1 := by
  induction count with
  | zero =>
      exact (not_lt_of_ge hx.1 hx.2).elim
  | succ count ih =>
      rw [Fin.sum_univ_castSucc]
      by_cases hbefore : x < knots count
      · have hsum := ih ⟨hx.1, hbefore⟩
        have hlast :
            finiteCoxDeBoorBasis knots 0 (count + 1)
                (Fin.last count) x = 0 := by
          simp [finiteCoxDeBoorBasis, coxDeBoorBasis,
            not_le_of_gt hbefore]
        rw [hlast, add_zero]
        simpa [finiteCoxDeBoorBasis] using hsum
      · have hcount : knots count ≤ x :=
          le_of_not_gt hbefore
        have hfirst :
            (∑ index : Fin count,
              finiteCoxDeBoorBasis knots 0 (count + 1)
                index.castSucc x) = 0 := by
          apply Finset.sum_eq_zero
          intro index _
          apply coxDeBoorBasis_zero_eq_zero
          intro hcell
          have hindex : index.val + 1 ≤ count := by
            omega
          have hupper :
              knots (index.val + 1) ≤ knots count :=
            knots.monotone hindex
          exact (not_lt_of_ge (hupper.trans hcount)) hcell.2
        have hlast :
            finiteCoxDeBoorBasis knots 0 (count + 1)
                (Fin.last count) x = 1 := by
          apply coxDeBoorBasis_zero_eq_one
          constructor
          · simpa only [Fin.val_last] using hcount
          · simpa only [Fin.val_last, Nat.succ_eq_add_one] using hx.2
        rw [hfirst, hlast, zero_add]

/-- Adjacent Cox–de Boor weights sum to one when their shared knot span is
nondegenerate. -/
theorem leftBlendWeight_succ_add_rightBlendWeight
    (knots : KnotSequence) (degree index : ℕ) (x : ℝ)
    (hspan :
      knots (index + degree + 2) ≠
        knots (index + 1)) :
    leftBlendWeight knots degree (index + 1) x +
        rightBlendWeight knots degree index x = 1 := by
  unfold leftBlendWeight rightBlendWeight
  have hindex :
      (index + 1) + degree + 1 = index + degree + 2 := by
    omega
  rw [hindex, ← add_div]
  apply (div_eq_one_iff_eq (sub_ne_zero.mpr hspan)).2
  ring

/-- An interior Cox–de Boor parent is reproduced by its two successor
weights whenever the corresponding knot span is nondegenerate. -/
theorem coxDeBoorBasis_mul_add_adjacent_weights
    (knots : KnotSequence) (degree index : ℕ) (x : ℝ)
    (hspan :
      knots (index + degree + 2) ≠
        knots (index + 1)) :
    (leftBlendWeight knots degree (index + 1) x +
        rightBlendWeight knots degree index x) *
          coxDeBoorBasis knots degree (index + 1) x =
      coxDeBoorBasis knots degree (index + 1) x := by
  rw [leftBlendWeight_succ_add_rightBlendWeight
    knots degree index x hspan, one_mul]

/-- Finite summation of one Cox–de Boor refinement step.

The three hypotheses are exactly the left boundary, interior-column, and
right boundary reproduction conditions. -/
theorem sum_finiteCoxDeBoorBasis_succ_eq_sum
    (knots : KnotSequence) (degree count : ℕ) (x : ℝ)
    (hleft :
      leftBlendWeight knots degree 0 x *
          coxDeBoorBasis knots degree 0 x =
        coxDeBoorBasis knots degree 0 x)
    (hmiddle :
      ∀ index : Fin count,
        (leftBlendWeight knots degree (index.val + 1) x +
            rightBlendWeight knots degree index.val x) *
              coxDeBoorBasis knots degree (index.val + 1) x =
          coxDeBoorBasis knots degree (index.val + 1) x)
    (hright :
      rightBlendWeight knots degree count x *
          coxDeBoorBasis knots degree (count + 1) x =
        coxDeBoorBasis knots degree (count + 1) x) :
    (∑ index : Fin (count + 1),
        finiteCoxDeBoorBasis knots (degree + 1) (count + 1)
          index x) =
      ∑ index : Fin (count + 2),
        finiteCoxDeBoorBasis knots degree (count + 2) index x := by
  simp only [finiteCoxDeBoorBasis, coxDeBoorBasis_succ]
  rw [Finset.sum_add_distrib]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
  rw [add_assoc]
  rw [← add_assoc
    (∑ index : Fin count,
      leftBlendWeight knots degree (index.val + 1) x *
        coxDeBoorBasis knots degree (index.val + 1) x)]
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_mul]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
  rw [hleft, hright]
  simp_rw [hmiddle]

/-- A finite Cox–de Boor family with a certified partition of unity on a
carrier. -/
structure FiniteCoxDeBoorPartition
    (knots : KnotSequence) (degree count : ℕ) where
  /-- Region on which the finite family sums to one. -/
  carrier : Set ℝ
  /-- Partition-of-unity certificate on the carrier. -/
  sum_eq_one_on :
    ∀ x, x ∈ carrier →
      ∑ index : Fin count,
        finiteCoxDeBoorBasis knots degree count index x = 1

namespace FiniteCoxDeBoorPartition

/-- Package a finite Cox–de Boor partition as a normalized positive basis. -/
def toNormalizedPositiveBasis
    {knots : KnotSequence} {degree count : ℕ}
    (partition : FiniteCoxDeBoorPartition knots degree count) :
    NormalizedPositiveBasis ℝ (Fin count) where
  carrier := partition.carrier
  basis := finiteCoxDeBoorBasis knots degree count
  nonneg_on := fun index x _ ↦
    finiteCoxDeBoorBasis_nonneg knots degree count index x
  sum_eq_one_on := partition.sum_eq_one_on

end FiniteCoxDeBoorPartition

/-- Affine coordinate carrying `[a,b]` to `[0,1]`. -/
def panelCoordinate (a b x : ℝ) : ℝ :=
  (x - a) / (b - a)

/-- The panel coordinate is nonnegative to the right of a positively oriented panel's left end. -/
theorem panelCoordinate_nonneg {a b x : ℝ}
    (hab : a < b) (hx : a ≤ x) :
    0 ≤ panelCoordinate a b x :=
  div_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hab.le)

/-- The panel coordinate is at most one to the left of a positively oriented panel's right end. -/
theorem panelCoordinate_le_one {a b x : ℝ}
    (hab : a < b) (hx : x ≤ b) :
    panelCoordinate a b x ≤ 1 := by
  apply (div_le_one (sub_pos.mpr hab)).2
  linarith

/-- Bernstein polynomials are nonnegative on the unit interval. -/
theorem bernsteinPolynomial_eval_nonneg
    (degree index : ℕ) {x : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    0 ≤ (bernsteinPolynomial ℝ degree index).eval x := by
  simp only [bernsteinPolynomial, Polynomial.eval_mul,
    Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx₀ _))
    (pow_nonneg (sub_nonneg.mpr hx₁) _)

/-- The degree-`p` Bernstein realization of a one-panel open-clamped spline basis on `[a,b]`.

On the closed panel this is the affine pullback of the Bernstein basis, including the usual
endpoint values. Outside the panel it is set to zero. Consequently, this definition uses a
closed-endpoint convention and does not coincide at `b` with the raw half-open degree-zero
Cox–de Boor convention from `coxDeBoorBasis`. The zero extension is not generally continuous at
the panel endpoints; differential applications should work on the open panel or separately prove
the required endpoint compatibility. -/
def clampedSinglePanelBSpline (a b : ℝ) (degree : ℕ)
    (index : Fin (degree + 1)) (x : ℝ) : ℝ :=
  if x ∈ Icc a b then
    (bernsteinPolynomial ℝ degree index).eval (panelCoordinate a b x)
  else
    0

/-- A one-panel clamped B-spline vanishes outside its panel. -/
theorem clampedSinglePanelBSpline_eq_zero_of_not_mem
    (a b : ℝ) (degree : ℕ) (index : Fin (degree + 1))
    {x : ℝ} (hx : x ∉ Icc a b) :
    clampedSinglePanelBSpline a b degree index x = 0 := by
  simp [clampedSinglePanelBSpline, hx]

/-- One-panel clamped B-splines are nonnegative on their panel. -/
theorem clampedSinglePanelBSpline_nonneg
    {a b : ℝ} (hab : a < b) (degree : ℕ)
    (index : Fin (degree + 1)) {x : ℝ} (hx : x ∈ Icc a b) :
    0 ≤ clampedSinglePanelBSpline a b degree index x := by
  rw [clampedSinglePanelBSpline, ite_eq_left hx]
  exact bernsteinPolynomial_eval_nonneg degree index
    (panelCoordinate_nonneg hab hx.1)
    (panelCoordinate_le_one hab hx.2)

/-- One-panel clamped B-splines form a partition of unity on the panel. -/
theorem sum_clampedSinglePanelBSpline_eq_one
    {a b : ℝ} (degree : ℕ)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ∑ index : Fin (degree + 1),
        clampedSinglePanelBSpline a b degree index x = 1 := by
  simp only [clampedSinglePanelBSpline, ite_eq_left hx]
  change
    (∑ index : Fin (degree + 1),
      (fun j : ℕ ↦
        (bernsteinPolynomial ℝ degree j).eval
          (panelCoordinate a b x)) index.val) = 1
  have hsum := congrArg
    (fun polynomial : ℝ[X] ↦ polynomial.eval (panelCoordinate a b x))
    (bernsteinPolynomial.sum ℝ degree)
  calc
    (∑ index : Fin (degree + 1),
      (fun j : ℕ ↦
        (bernsteinPolynomial ℝ degree j).eval
          (panelCoordinate a b x)) index.val) =
        ∑ index ∈ Finset.range (degree + 1),
          (bernsteinPolynomial ℝ degree index).eval
            (panelCoordinate a b x) :=
      Fin.sum_univ_eq_sum_range
        (fun index : ℕ ↦
          (bernsteinPolynomial ℝ degree index).eval
            (panelCoordinate a b x))
        (degree + 1)
    _ = 1 := by
      simpa only [Polynomial.eval_finsetSum, Polynomial.eval_one] using hsum

/-- The one-panel Bernstein realization as a normalized positive basis. -/
def clampedSinglePanelNormalizedBasis
    (a b : ℝ) (degree : ℕ) (hab : a < b) :
    NormalizedPositiveBasis ℝ (Fin (degree + 1)) where
  carrier := Icc a b
  basis := clampedSinglePanelBSpline a b degree
  nonneg_on := fun index x hx ↦
    clampedSinglePanelBSpline_nonneg hab degree index (x := x) hx
  sum_eq_one_on := fun x hx ↦
    sum_clampedSinglePanelBSpline_eq_one degree (x := x) hx

end CAS.Splines
