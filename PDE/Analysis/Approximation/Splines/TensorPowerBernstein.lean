/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.PowerBernstein

/-!
# Tensor power polynomials in a Bernstein basis

Converting rows and then columns preserves the tensor polynomial.
Bounds on the resulting coefficients hold throughout the closed unit square.

## Main definitions

* `tensorPowerBernsteinCoefficients`: the power-to-Bernstein conversion applied in both
  coordinates.

## Main results

* `sum_tensorPowerBernsteinCoefficients`: the converted coefficients represent the original tensor
  power polynomial.
* `abs_tensorPowerPolynomial_le`: a bound of every converted coefficient bounds the tensor power
  polynomial on `[0, 1]²`.
-/

@[expose] public noncomputable section

namespace CAS.Splines

open scoped BigOperators unitInterval

/-- Apply the finite power-to-Bernstein conversion in both coordinates. -/
def tensorPowerBernsteinCoefficients {n m : ℕ}
    (coefficients : Fin (n + 1) → Fin (m + 1) → ℝ)
    (k : Fin (n + 1)) (l : Fin (m + 1)) : ℝ :=
  powerBernsteinCoefficients (fun i ↦ powerBernsteinCoefficients (coefficients i) l) k

/-- Row and column conversion preserves every value of the tensor polynomial. -/
theorem sum_tensorPowerBernsteinCoefficients {n m : ℕ}
    (coefficients : Fin (n + 1) → Fin (m + 1) → ℝ) (x y : I) :
    (∑ k, ∑ l, tensorPowerBernsteinCoefficients coefficients k l *
      bernstein n k x * bernstein m l y) =
      ∑ i, ∑ j, coefficients i j * (x : ℝ) ^ i.val * (y : ℝ) ^ j.val := by
  calc
    _ = ∑ l, (∑ k, tensorPowerBernsteinCoefficients coefficients k l *
        bernstein n k x) * bernstein m l y := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ l, (∑ i, powerBernsteinCoefficients (coefficients i) l *
        (x : ℝ) ^ i.val) * bernstein m l y := by
      simp_rw [tensorPowerBernsteinCoefficients, sum_powerBernsteinCoefficients]
    _ = ∑ i, (∑ l, powerBernsteinCoefficients (coefficients i) l *
        bernstein m l y) * (x : ℝ) ^ i.val := by
      simp only [Finset.sum_mul, mul_right_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [sum_powerBernsteinCoefficients]
      simp only [Finset.sum_mul, mul_right_comm]

/-- Uniform Bernstein coefficient bounds imply a bound on the whole closed unit square. -/
theorem abs_tensorPowerPolynomial_le {n m : ℕ}
    (coefficients : Fin (n + 1) → Fin (m + 1) → ℝ) (bound : ℝ) (x y : I)
    (hcoeff : ∀ k l, |tensorPowerBernsteinCoefficients coefficients k l| ≤ bound) :
    |∑ i, ∑ j, coefficients i j * (x : ℝ) ^ i.val * (y : ℝ) ^ j.val| ≤ bound := by
  rw [← sum_tensorPowerBernsteinCoefficients]
  have hsum :
      (∑ k, ∑ l, tensorPowerBernsteinCoefficients coefficients k l *
        bernstein n k x * bernstein m l y) =
      ∑ k, (∑ l, tensorPowerBernsteinCoefficients coefficients k l *
        bernstein m l y) * bernstein n k x := by
    simp only [Finset.sum_mul, mul_right_comm]
  rw [hsum]
  apply abs_sum_mul_bernstein_le
  intro k
  exact abs_sum_mul_bernstein_le _ bound y (hcoeff k)

end CAS.Splines
