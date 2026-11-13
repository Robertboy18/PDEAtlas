/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteFactorControls
import CAS.ExactTactic

/-!
# Integer certificates for Hermite factor controls

On a panel of width `1/n` at offset `t/n` from a factor's center, take the
factor coefficient `κ = 1/q`. Nodal values and candidate physical slopes have
a common denominator `D`. Multiplying each cubic Bernstein control by
`3*n*q*D` leaves an integer expression.

The same expression includes the radius of a common slope error `E/D`.
Positive `E` gives an upper control and negative `E` gives a lower control.
These formulas do not depend on a particular mesh, profile, or PDE.
-/

@[expose] public section

noncomputable section

namespace CAS.Splines

/-- Cleared Bernstein coefficients contributed by the two nodal numerators. -/
def hermiteFactorConstantNumerator (n q t a b : ℤ) : Fin 4 → ℤ :=
  ![3 * n * q * a, 3 * n * q * a - 6 * n * t * (b - a),
    3 * n * q * b - 6 * n * (t + 1) * (b - a), 3 * n * q * b]

/-- Cleared Bernstein coefficients multiplying the left physical slope numerator. -/
def hermiteFactorLeftNumerator (q t : ℤ) : Fin 4 → ℤ :=
  ![-3 * t, q - 1 + t, 2 * (t + 1), 0]

/-- Cleared Bernstein coefficients multiplying the right physical slope numerator. -/
def hermiteFactorRightNumerator (q t : ℤ) : Fin 4 → ℤ :=
  ![0, 2 * t, t - q + 2, -3 * (t + 1)]

/-- Candidate control with its signed slope-error radius and all denominators cleared. -/
def hermiteFactorNumerator (n q t a b da db E : ℤ) (k : Fin 4) : ℤ :=
  hermiteFactorConstantNumerator n q t a b k +
    hermiteFactorLeftNumerator q t k * da + hermiteFactorRightNumerator q t k * db +
    (|hermiteFactorLeftNumerator q t k| + |hermiteFactorRightNumerator q t k|) * E

/-- The left-slope coefficient decodes with denominator `3*n*q`. -/
theorem hermiteFactorLeftSlope_eq_numerator (n q t : ℤ)
    (hn : (n : ℝ) ≠ 0) (hq : (q : ℝ) ≠ 0) (k : Fin 4) :
    hermiteFactorLeftSlope (1 / q) (t / n) (1 / n) k =
      (hermiteFactorLeftNumerator q t k : ℝ) / (3 * n * q) := by
  fin_cases k <;>
    simp only [hermiteFactorLeftSlope, hermiteFactorLeftNumerator] <;>
    push_cast <;> cas using And.intro hn hq

/-- The right-slope coefficient decodes with denominator `3*n*q`. -/
theorem hermiteFactorRightSlope_eq_numerator (n q t : ℤ)
    (hn : (n : ℝ) ≠ 0) (hq : (q : ℝ) ≠ 0) (k : Fin 4) :
    hermiteFactorRightSlope (1 / q) (t / n) (1 / n) k =
      (hermiteFactorRightNumerator q t k : ℝ) / (3 * n * q) := by
  fin_cases k <;>
    simp only [hermiteFactorRightSlope, hermiteFactorRightNumerator] <;>
    push_cast <;> cas using And.intro hn hq

/-- Nodal values with common denominator `D` decode to the constant controls. -/
theorem hermiteFactorConstant_eq_numerator (n q D t a b : ℤ)
    (hn : (n : ℝ) ≠ 0) (hq : (q : ℝ) ≠ 0) (hD : (D : ℝ) ≠ 0) (k : Fin 4) :
    hermiteFactorConstant (1 / q) (t / n) (1 / n) ((a : ℝ) / D) ((b : ℝ) / D) k =
      (hermiteFactorConstantNumerator n q t a b k : ℝ) / (3 * n * q * D) := by
  fin_cases k <;>
    simp only [hermiteFactorConstant, hermiteFactorConstantNumerator] <;>
    push_cast <;> cas using And.intro hn (And.intro hq hD)

/-- The denominators decode the full control and its signed error radius.
The error numerator may be negative, so the identity also covers lower controls. The
denominator `D` may have any sign; at `D = 0` both sides vanish. -/
theorem hermiteFactorControl_add_radius_eq_numerator (n q D t a b da db E : ℤ)
    (hn : 0 < n) (hq : 0 < q) (k : Fin 4) :
    hermiteFactorControl (1 / q) (t / n) (1 / n)
        ((a : ℝ) / D) ((b : ℝ) / D) ((da : ℝ) / D) ((db : ℝ) / D) k +
      hermiteFactorRadius (1 / q) (t / n) (1 / n) k * ((E : ℝ) / D) =
      (hermiteFactorNumerator n q t a b da db E k : ℝ) / (3 * n * q * D) := by
  rcases eq_or_ne D 0 with rfl | hD0
  · fin_cases k <;> simp [hermiteFactorControl, hermiteFactorConstant]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD0
  have hscale : (0 : ℝ) < 3 * n * q := mul_pos (mul_pos (by norm_num) hnr) hqr
  simp only [hermiteFactorControl, hermiteFactorRadius,
    hermiteFactorLeftSlope_eq_numerator n q t hnr.ne' hqr.ne',
    hermiteFactorRightSlope_eq_numerator n q t hnr.ne' hqr.ne',
    hermiteFactorConstant_eq_numerator n q D t a b hnr.ne' hqr.ne' hDr,
    abs_div, abs_of_pos hscale]
  rw [hermiteFactorNumerator]
  push_cast
  cas using And.intro hnr.ne' (And.intro hqr.ne' hDr)

end CAS.Splines
