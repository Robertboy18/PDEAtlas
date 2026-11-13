/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteFactorLowerBounds
public import PDE.Analysis.Approximation.Splines.HermiteJetBounds
import CAS.ExactTactic

/-!
# Cubic controls for a second-order differential expression

For a cubic `p`, the expression `a p + b (x-c) p' + d (x-c)² p''` remains cubic.
Its controls are linear in the polynomial's four coefficients. Keeping those controls
over an arbitrary commutative ring permits exact integer replay after clearing denominators.
-/

@[expose] public section

namespace CAS.Splines

open _root_.Polynomial Set

/-- Three times the Bernstein controls of a cubic second-order differential expression.
Here `s` is the left endpoint relative to the center, in normalized coordinates. -/
def cubicDifferentialControl {R : Type*} [CommRing R]
    (a b d s A B C D : R) : Fin 4 → R :=
  let e₀ := a * A + b * s * B + 2 * d * s ^ 2 * C
  let e₁ := (a + b) * B + (2 * b + 4 * d) * s * C + 6 * d * s ^ 2 * D
  let e₂ := (a + 2 * b + 2 * d) * C + (3 * b + 12 * d) * s * D
  let e₃ := (a + 3 * b + 6 * d) * D
  ![3 * e₀, 3 * e₀ + e₁, 3 * e₀ + 2 * e₁ + e₂, 3 * (e₀ + e₁ + e₂ + e₃)]

/-- The differential controls reconstruct the expression throughout the real line. -/
theorem cubicDifferentialControl_identity (a b d s A B C D z : ℝ) :
    3 * (a * (A + B * z + C * z ^ 2 + D * z ^ 3) +
      b * (s + z) * (B + 2 * C * z + 3 * D * z ^ 2) +
      d * (s + z) ^ 2 * (2 * C + 6 * D * z)) =
    cubicDifferentialControl a b d s A B C D 0 * (bernsteinPolynomial ℝ 3 0).eval z +
    cubicDifferentialControl a b d s A B C D 1 * (bernsteinPolynomial ℝ 3 1).eval z +
    cubicDifferentialControl a b d s A B C D 2 * (bernsteinPolynomial ℝ 3 2).eval z +
    cubicDifferentialControl a b d s A B C D 3 * (bernsteinPolynomial ℝ 3 3).eval z := by
  simp only [cubicDifferentialControl, bernsteinPolynomial, eval_mul, eval_natCast,
    eval_pow, eval_X, eval_sub, eval_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num
  cas

/-- Nonnegative controls certify the differential expression on the entire closed unit panel. -/
theorem cubic_differential_nonneg_of_controls (a b d s A B C D : ℝ) {z : ℝ}
    (hz : z ∈ Icc 0 1) (hc : ∀ k, 0 ≤ cubicDifferentialControl a b d s A B C D k) :
    0 ≤ a * (A + B * z + C * z ^ 2 + D * z ^ 3) +
      b * (s + z) * (B + 2 * C * z + 3 * D * z ^ 2) +
      d * (s + z) ^ 2 * (2 * C + 6 * D * z) := by
  have h := le_bernstein_cubic_of_le_controls hz hc
  rw [← cubicDifferentialControl_identity] at h
  linarith

/-- Cubic coefficients obtained from Hermite data after the width is cleared.
The arguments `da` and `db` are slopes multiplied by the panel width. -/
def hermiteDifferentialControl {R : Type*} [CommRing R]
    (a b d s A B da db : R) : Fin 4 → R :=
  cubicDifferentialControl a b d s A da (3 * (B - A) - 2 * da - db)
    (2 * (A - B) + da + db)

/-- Separating the two slopes exposes the exact error coefficients. -/
theorem hermiteDifferentialControl_affine (a b d s A B da db : ℝ) (k : Fin 4) :
    hermiteDifferentialControl a b d s A B da db k =
      hermiteDifferentialControl a b d s A B 0 0 k +
      hermiteDifferentialControl a b d s 0 0 1 0 k * da +
      hermiteDifferentialControl a b d s 0 0 0 1 k * db := by
  fin_cases k <;> simp only [hermiteDifferentialControl, cubicDifferentialControl] <;> cas

/-- Differential control signs apply to physical Hermite polynomials, with the
center and slopes expressed in units of the panel width. -/
theorem hermite_differential_nonneg_of_controls
    (a b d center left h A B da db : ℝ) (hh : h ≠ 0) {z : ℝ}
    (hz : z ∈ Icc 0 1)
    (hc : ∀ k, 0 ≤ hermiteDifferentialControl a b d ((left - center) / h)
      A B (h * da) (h * db) k) :
    let p := hermitePolynomial left h A B da db
    let x := left + h * z
    0 ≤ a * p.eval x + b * (x - center) * polynomialJet 1 p x +
      d * (x - center) ^ 2 * polynomialJet 2 p x := by
  dsimp only
  have hn := cubic_differential_nonneg_of_controls a b d ((left - center) / h)
    A (h * da) (3 * (B - A) - 2 * (h * da) - h * db)
    (2 * (A - B) + h * da + h * db) hz hc
  rw [hermitePolynomial_eval, hermitePolynomial_first_bernstein _ _ _ _ _ _ _ hh,
    hermitePolynomial_second_affine _ _ _ _ _ _ _ hh]
  convert hn using 1
  unfold hermiteValue
  cas using hh

/-- A uniform slope error gives an explicit error radius for each differential control. -/
theorem abs_hermiteDifferentialControl_sub_le
    (a b d s A B da db ea eb ε : ℝ) (k : Fin 4)
    (ha : |da - ea| ≤ ε) (hb : |db - eb| ≤ ε) :
    |hermiteDifferentialControl a b d s A B da db k -
      hermiteDifferentialControl a b d s A B ea eb k| ≤
      (|hermiteDifferentialControl a b d s 0 0 1 0 k| +
        |hermiteDifferentialControl a b d s 0 0 0 1 k|) * ε := by
  rw [hermiteDifferentialControl_affine a b d s A B da db,
    hermiteDifferentialControl_affine a b d s A B ea eb]
  have he : hermiteDifferentialControl a b d s A B 0 0 k +
      hermiteDifferentialControl a b d s 0 0 1 0 k * da +
      hermiteDifferentialControl a b d s 0 0 0 1 k * db -
      (hermiteDifferentialControl a b d s A B 0 0 k +
        hermiteDifferentialControl a b d s 0 0 1 0 k * ea +
        hermiteDifferentialControl a b d s 0 0 0 1 k * eb) =
      hermiteDifferentialControl a b d s 0 0 1 0 k * (da - ea) +
      hermiteDifferentialControl a b d s 0 0 0 1 k * (db - eb) := by cas
  rw [he]
  calc
    _ ≤ |hermiteDifferentialControl a b d s 0 0 1 0 k * (da - ea)| +
        |hermiteDifferentialControl a b d s 0 0 0 1 k * (db - eb)| := abs_add_le _ _
    _ ≤ |hermiteDifferentialControl a b d s 0 0 1 0 k| * ε +
        |hermiteDifferentialControl a b d s 0 0 0 1 k| * ε := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
    _ = _ := by cas

end CAS.Splines
