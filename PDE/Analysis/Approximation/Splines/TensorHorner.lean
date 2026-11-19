/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.BranchHorner

/-!
# Tensor Horner evaluation and its derivatives

The outer coefficient list is indexed by radial power and each inner list by
axial power. Horner evaluation is identified with an ordinary finite power sum;
Mathlib's iterated derivative of a monomial supplies the falling-factorial rule.
-/

@[expose] public section
namespace CAS.Splines
open CAS.Verified CAS.Polynomial
open scoped BigOperators

/-- Tensor Horner expression, with the first coordinate on the outside. -/
def tensorHornerExpr : List (List ℚ) → Expr (Fin 2)
  | [] => .nat 0
  | row :: rest => .add (hornerExpr (.var 1) row) (.mul (.var 0) (tensorHornerExpr rest))

/-- Exact real tensor Horner evaluation in the same order as the executable expression. -/
noncomputable def tensorHornerValue (coefficients : List (List ℚ)) (x y : ℝ) : ℝ :=
  listHornerEval x (coefficients.map fun row ↦ listHornerEval y (row.map Rat.cast))

/-- The expression and real tensor evaluator have identical semantics. -/
theorem tensorHornerExpr_eval (coefficients : List (List ℚ)) (ρ : Fin 2 → ℝ) :
    (tensorHornerExpr coefficients).eval ρ = tensorHornerValue coefficients (ρ 0) (ρ 1) := by
  induction coefficients with
  | nil => simp [tensorHornerExpr, Expr.eval, tensorHornerValue]
  | cons row rest ih =>
      simp [tensorHornerExpr, Expr.eval, tensorHornerValue,
        hornerExpr_eval, ih, mul_comm, add_comm]

/-- Rational coefficient casting commutes with list Horner evaluation's power-sum form. -/
theorem listHornerEval_rat_eq_sum (coefficients : List ℚ) (x : ℝ) :
    listHornerEval x (coefficients.map Rat.cast) =
      ∑ k ∈ Finset.range coefficients.length, (coefficients.getD k 0 : ℝ) * x ^ k := by
  rw [listHornerEval_eq_sum, List.length_map]
  apply Finset.sum_congr rfl
  intro k _
  have h := List.getD_map (l := coefficients) (d := (0 : ℚ)) (n := k) (Rat.cast : ℚ → ℝ)
  simpa only [Rat.cast_zero] using congrArg (fun c : ℝ ↦ c * x ^ k) h

/-- Tensor Horner evaluation is the finite bivariate power sum. -/
theorem tensorHornerValue_eq_sum (coefficients : List (List ℚ)) (x y : ℝ) :
    tensorHornerValue coefficients x y =
      ∑ i ∈ Finset.range coefficients.length,
        ∑ j ∈ Finset.range (coefficients.getD i []).length,
          ((coefficients.getD i []).getD j 0 : ℝ) * x ^ i * y ^ j := by
  rw [tensorHornerValue, listHornerEval_eq_sum, List.length_map]
  apply Finset.sum_congr rfl
  intro i _
  have h := List.getD_map (l := coefficients) (d := ([] : List ℚ)) (n := i)
    (fun row ↦ listHornerEval y (row.map (Rat.cast : ℚ → ℝ)))
  simp only [List.map_nil, listHornerEval_nil] at h
  rw [h, listHornerEval_rat_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_assoc, mul_comm (y ^ j) (x ^ i)]

/-- Rectangular coefficient data assembled from one shared coefficient function. -/
def tensorCoefficients (nx ny : ℕ) (c : ℕ → ℕ → ℚ) : List (List ℚ) :=
  (List.range nx).map fun i ↦ (List.range ny).map fun j ↦ c i j

/-- A rectangular coefficient table evaluates to the finite power sum
`∑ i, ∑ j, c i j * x ^ i * y ^ j`. -/
theorem tensorHornerValue_tensorCoefficients (nx ny : ℕ) (c : ℕ → ℕ → ℚ) (x y : ℝ) :
    tensorHornerValue (tensorCoefficients nx ny c) x y =
      ∑ i ∈ Finset.range nx, ∑ j ∈ Finset.range ny, (c i j : ℝ) * x ^ i * y ^ j := by
  rw [tensorHornerValue_eq_sum]
  simp only [tensorCoefficients, List.length_map, List.length_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < nx := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi')]
  simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < ny := Finset.mem_range.mp hj
  rw [List.getD_eq_getElem _ _ (by simpa using hj')]
  simp

/-- Evaluation at the origin selects the constant coefficient of a nonempty tensor. -/
theorem tensorHornerValue_tensorCoefficients_zero (nx ny : ℕ) (c : ℕ → ℕ → ℚ)
    (hx : 0 < nx) (hy : 0 < ny) :
    tensorHornerValue (tensorCoefficients nx ny c) 0 0 = (c 0 0 : ℝ) := by
  rw [tensorHornerValue_tensorCoefficients]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [zero_pow hj]
    · simp [hy]
  · intro i _ hi
    simp [zero_pow hi]
  · simp [hx]

end CAS.Splines
