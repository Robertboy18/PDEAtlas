/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.TensorBranchEnclosure
public import PDE.Analysis.Approximation.Splines.Locality
public import PDE.Analysis.Approximation.Splines.TensorHorner

/-!
# Staged tensor polynomial identities

Small checked univariate identities assemble a tensor polynomial without
normalizing the full bivariate Cox–de Boor expression at once.
-/

@[expose] public section

namespace CAS.Splines

open CAS.Verified CAS.Polynomial

/-- Each checked univariate row identity denotes an exact linear combination. -/
theorem checked_horner_linear_combination
    (count : ℕ) (coefficients : ℕ → ℚ) (basis : ℕ → List ℚ)
    (result : List ℚ)
    (hcheck : polynomialIdentityCheck
      (exprRangeSum (fun j ↦ .mul (Expr.mkRatConst (coefficients j))
        (hornerExpr (.var (0 : Fin 1)) (basis j))) count)
      (hornerExpr (.var 0) result) = true) (x : ℝ) :
    ∑ j ∈ Finset.range count,
      (coefficients j : ℝ) * listHornerEval x ((basis j).map Rat.cast) =
        listHornerEval x (result.map Rat.cast) := by
  have h := polynomialIdentityCheck_sound _ _ hcheck (WithLp.toLp 2 (fun _ : Fin 1 ↦ x))
  simpa only [exprRangeSum_eval, Expr.eval, Expr.eval_mkRatConst, hornerExpr_eval] using h

/-- Assemble the first stage using independent checked identities for each row. -/
theorem checked_tensor_rows
    (rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ)
    (xBasis yBasis rowTable : ℕ → List ℚ)
    (hrows : ∀ i < rows, polynomialIdentityCheck
      (exprRangeSum (fun j ↦ .mul (Expr.mkRatConst (coefficient i j))
        (hornerExpr (.var (0 : Fin 1)) (yBasis j))) cols)
      (hornerExpr (.var 0) (rowTable i)) = true) (x y : ℝ) :
    (∑ i ∈ Finset.range rows, listHornerEval x ((xBasis i).map Rat.cast) *
      ∑ j ∈ Finset.range cols, (coefficient i j : ℝ) *
        listHornerEval y ((yBasis j).map Rat.cast)) =
      ∑ i ∈ Finset.range rows, listHornerEval x ((xBasis i).map Rat.cast) *
        listHornerEval y ((rowTable i).map Rat.cast) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [checked_horner_linear_combination cols (coefficient i) yBasis (rowTable i)
    (hrows i (Finset.mem_range.mp hi)) y]

/-- On a knot cell, monotonicity alone identifies the finite active basis window. -/
theorem rationalTensorSpline_eq_active_sum
    (kx ky : KnotSequence) (degreeX degreeY rows cols startX startY : ℕ)
    (coefficient : ℕ → ℕ → ℚ) (x y : ℝ)
    (hrows : startX + degreeX + 1 ≤ rows) (hcols : startY + degreeY + 1 ≤ cols)
    (hx : x ∈ Set.Ico (kx (startX + degreeX)) (kx (startX + degreeX + 1)))
    (hy : y ∈ Set.Ico (ky (startY + degreeY)) (ky (startY + degreeY + 1))) :
    rationalTensorSpline kx ky degreeX degreeY rows cols coefficient x y =
      ∑ i ∈ Finset.range (degreeX + 1), coxDeBoorBasis kx degreeX (startX + i) x *
        ∑ j ∈ Finset.range (degreeY + 1), coxDeBoorBasis ky degreeY (startY + j) y *
          (coefficient (startX + i) (startY + j) : ℝ) := by
  have hlocal := tensor_coxDeBoorBasis_eq_local kx ky degreeX degreeY
    (Finset.range rows) (Finset.range cols)
    (Finset.Ico startX (startX + (degreeX + 1)))
    (Finset.Ico startY (startY + (degreeY + 1)))
    (fun i j ↦ (coefficient i j : ℝ)) (x := x) (z := y)
  unfold rationalTensorSpline
  rw [hlocal]
  · rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
  · intro i hi
    simp only [Finset.mem_Ico, Finset.mem_range] at *
    omega
  · intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at *
    omega
  · intro i _ hi
    simp only [Finset.mem_Ico] at hi
    by_cases hleft : i < startX
    · exact Or.inr ((kx.monotone (by omega)).trans hx.1)
    · exact Or.inl (hx.2.trans_le (kx.monotone (by omega)))
  · intro j _ hj
    simp only [Finset.mem_Ico] at hj
    by_cases hleft : j < startY
    · exact Or.inr ((ky.monotone (by omega)).trans hy.1)
    · exact Or.inl (hy.2.trans_le (ky.monotone (by omega)))

/-- Two families of small exact checks identify the complete tensor power sum.
The row lengths specify the finite coefficient range; no coefficient equality
or bivariate normalization is assumed. -/
theorem checked_tensor_stages
    (rows cols powers : ℕ) (coefficient : ℕ → ℕ → ℚ)
    (xBasis yBasis rowTable columnTable : ℕ → List ℚ)
    (hlength : ∀ i < rows, (rowTable i).length = powers)
    (hrows : ∀ i < rows, polynomialIdentityCheck
      (exprRangeSum (fun j ↦ .mul (Expr.mkRatConst (coefficient i j))
        (hornerExpr (.var (0 : Fin 1)) (yBasis j))) cols)
      (hornerExpr (.var 0) (rowTable i)) = true)
    (hcolumns : ∀ k < powers, polynomialIdentityCheck
      (exprRangeSum (fun i ↦ .mul (Expr.mkRatConst ((rowTable i).getD k 0))
        (hornerExpr (.var (0 : Fin 1)) (xBasis i))) rows)
      (hornerExpr (.var 0) (columnTable k)) = true) (x y : ℝ) :
    (∑ i ∈ Finset.range rows, listHornerEval x ((xBasis i).map Rat.cast) *
      ∑ j ∈ Finset.range cols, (coefficient i j : ℝ) *
        listHornerEval y ((yBasis j).map Rat.cast)) =
      ∑ k ∈ Finset.range powers,
        listHornerEval x ((columnTable k).map Rat.cast) * y ^ k := by
  rw [checked_tensor_rows rows cols coefficient xBasis yBasis rowTable hrows x y]
  calc
    _ = ∑ i ∈ Finset.range rows, ∑ k ∈ Finset.range powers,
        ((rowTable i).getD k 0 : ℝ) *
          listHornerEval x ((xBasis i).map Rat.cast) * y ^ k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [listHornerEval_eq_sum y ((rowTable i).map Rat.cast), List.length_map,
        hlength i (Finset.mem_range.mp hi),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hc : ((rowTable i).map (Rat.cast : ℚ → ℝ)).getD k 0 =
          ((rowTable i).getD k 0 : ℝ) := by
        simpa only [Rat.cast_zero] using
          (List.getD_map (l := rowTable i) (d := (0 : ℚ)) (n := k) (Rat.cast : ℚ → ℝ))
      rw [hc]
      ring
    _ = ∑ k ∈ Finset.range powers, ∑ i ∈ Finset.range rows,
        ((rowTable i).getD k 0 : ℝ) *
          listHornerEval x ((xBasis i).map Rat.cast) * y ^ k := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_mul,
        checked_horner_linear_combination rows (fun i ↦ (rowTable i).getD k 0)
          xBasis (columnTable k) (hcolumns k (Finset.mem_range.mp hk)) x]

/-- Exact basis, row, and column checks identify a tensor spline with
its staged polynomial on the active cell. Only knots, coefficients, and
coordinate membership enter the analytic side of the statement. -/
theorem rationalTensorSpline_eq_staged_polynomial
    (qx qy : ℕ → ℚ) (kx ky : KnotSequence)
    (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (degreeX degreeY rows cols startX startY powers : ℕ)
    (coefficient : ℕ → ℕ → ℚ)
    (xBasis yBasis rowTable columnTable : ℕ → List ℚ)
    (hlength : ∀ i < degreeX + 1, (rowTable i).length = powers)
    (hxbasis : ∀ i < degreeX + 1,
      branchHornerCheck qx (startX + degreeX) degreeX (startX + i) 0 (xBasis i) = true)
    (hybasis : ∀ j < degreeY + 1,
      branchHornerCheck qy (startY + degreeY) degreeY (startY + j) 0 (yBasis j) = true)
    (hrowChecks : ∀ i < degreeX + 1, polynomialIdentityCheck
      (exprRangeSum (fun j ↦ .mul (Expr.mkRatConst (coefficient (startX + i) (startY + j)))
        (hornerExpr (.var (0 : Fin 1)) (yBasis j))) (degreeY + 1))
      (hornerExpr (.var 0) (rowTable i)) = true)
    (hcolumnChecks : ∀ k < powers, polynomialIdentityCheck
      (exprRangeSum (fun i ↦ .mul (Expr.mkRatConst ((rowTable i).getD k 0))
        (hornerExpr (.var (0 : Fin 1)) (xBasis i))) (degreeX + 1))
      (hornerExpr (.var 0) (columnTable k)) = true)
    (x y : ℝ)
    (hrows : startX + degreeX + 1 ≤ rows) (hcols : startY + degreeY + 1 ≤ cols)
    (hx : x ∈ Set.Ico (kx (startX + degreeX)) (kx (startX + degreeX + 1)))
    (hy : y ∈ Set.Ico (ky (startY + degreeY)) (ky (startY + degreeY + 1))) :
    rationalTensorSpline kx ky degreeX degreeY rows cols coefficient x y =
      ∑ k ∈ Finset.range powers,
        listHornerEval x ((columnTable k).map Rat.cast) * y ^ k := by
  rw [rationalTensorSpline_eq_active_sum kx ky degreeX degreeY rows cols startX startY
    coefficient x y hrows hcols hx hy]
  have hbx (i : ℕ) (hi : i < degreeX + 1) :
      coxDeBoorBasis kx degreeX (startX + i) x =
        listHornerEval x ((xBasis i).map Rat.cast) := by
    rw [coxDeBoorBasis_eq_branch kx (startX + degreeX) degreeX (startX + i) hx]
    simpa only [Rat.cast_zero, sub_zero] using
      (branchHornerCheck_sound qx kx hxknots (startX + degreeX) degreeX (startX + i)
        0 (xBasis i) (hxbasis i hi) x).symm
  have hby (j : ℕ) (hj : j < degreeY + 1) :
      coxDeBoorBasis ky degreeY (startY + j) y =
        listHornerEval y ((yBasis j).map Rat.cast) := by
    rw [coxDeBoorBasis_eq_branch ky (startY + degreeY) degreeY (startY + j) hy]
    simpa only [Rat.cast_zero, sub_zero] using
      (branchHornerCheck_sound qy ky hyknots (startY + degreeY) degreeY (startY + j)
        0 (yBasis j) (hybasis j hj) y).symm
  rw [← checked_tensor_stages (degreeX + 1) (degreeY + 1) powers
    (fun i j ↦ coefficient (startX + i) (startY + j)) xBasis yBasis rowTable columnTable
    hlength hrowChecks hcolumnChecks x y]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hbx i (Finset.mem_range.mp hi)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hby j (Finset.mem_range.mp hj), mul_comm]

/-- Reassemble the checked column polynomials into the canonical tensor Horner
expression without duplicating the matrix coefficients. -/
theorem staged_polynomial_eq_tensorHorner
    (nx ny : ℕ) (columnTable : ℕ → List ℚ)
    (hlength : ∀ k < ny, (columnTable k).length = nx) (x y : ℝ) :
    (∑ k ∈ Finset.range ny,
      listHornerEval x ((columnTable k).map Rat.cast) * y ^ k) =
      tensorHornerValue (tensorCoefficients nx ny (fun i j ↦ (columnTable j).getD i 0)) x y := by
  rw [tensorHornerValue_tensorCoefficients, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [listHornerEval_rat_eq_sum, hlength k (Finset.mem_range.mp hk), Finset.sum_mul]

end CAS.Splines
