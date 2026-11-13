/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.Approximation.Splines.Hermite
import CAS.ExactTactic

/-!
# Bounds for the first two Hermite jets

The first physical derivative is a quadratic Bernstein polynomial. The second
derivative is affine between its endpoint curvatures. Their nonnegative basis
functions give bounds throughout a closed panel, rather than only at sampled points.
-/

@[expose] public section

noncomputable section

namespace CAS.Splines

open _root_.Polynomial Set

/-- The first physical jet in the quadratic Bernstein basis. -/
theorem hermitePolynomial_first_bernstein (left h a b da db z : ℝ) (hh : h ≠ 0) :
    polynomialJet 1 (hermitePolynomial left h a b da db) (left + h * z) =
      da * (1 - z) ^ 2 + 2 * (3 * (b - a) / h - da - db) * z * (1 - z) +
        db * z ^ 2 := by
  simp only [polynomialJet_succ, polynomialJet_zero, hermitePolynomial, map_mul,
    map_sub, map_add, derivative_C, derivative_mul, zero_mul, mul_zero,
    add_zero, derivative_X, sub_zero, one_mul, zero_add, derivative_pow,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, eval_add, eval_mul, eval_C,
    eval_sub, eval_X, eval_pow]
  cas using hh

/-- The second physical jet is affine between the two endpoint curvatures. -/
theorem hermitePolynomial_second_affine (left h a b da db z : ℝ) (hh : h ≠ 0) :
    polynomialJet 2 (hermitePolynomial left h a b da db) (left + h * z) =
      (6 * (b - a) / h ^ 2 - (4 * da + 2 * db) / h) * (1 - z) +
        (-6 * (b - a) / h ^ 2 + (2 * da + 4 * db) / h) * z := by
  simp only [polynomialJet_succ, polynomialJet_zero, hermitePolynomial, map_mul,
    map_sub, map_add, derivative_C, derivative_mul, zero_mul, mul_zero,
    add_zero, derivative_X, sub_zero, one_mul, zero_add, derivative_pow,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, eval_add, eval_mul, eval_C,
    eval_sub, eval_X]
  cas using hh

/-- A quadratic Bernstein polynomial stays within a common absolute control bound. -/
theorem abs_quadratic_bernstein_le (a b c K z : ℝ) (hz : z ∈ Icc 0 1)
    (ha : |a| ≤ K) (hb : |b| ≤ K) (hc : |c| ≤ K) :
    |a * (1 - z) ^ 2 + 2 * b * z * (1 - z) + c * z ^ 2| ≤ K := by
  have hmid : 0 ≤ 2 * z * (1 - z) :=
    mul_nonneg (mul_nonneg (by norm_num) hz.1) (sub_nonneg.mpr hz.2)
  have heq : 2 * b * z * (1 - z) = b * (2 * z * (1 - z)) := by cas
  rw [heq]
  calc
    _ ≤ |a * (1 - z) ^ 2| + |b * (2 * z * (1 - z))| + |c * z ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |a| * (1 - z) ^ 2 + |b| * (2 * z * (1 - z)) + |c| * z ^ 2 := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg (1 - z)),
        abs_of_nonneg hmid, abs_of_nonneg (sq_nonneg z)]
    _ ≤ K * (1 - z) ^ 2 + K * (2 * z * (1 - z)) + K * z ^ 2 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right ha (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hb hmid)) (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
    _ = K := by cas

/-- An affine interpolant stays within a common absolute endpoint bound. -/
theorem abs_affine_interpolation_le (a b K z : ℝ) (hz : z ∈ Icc 0 1)
    (ha : |a| ≤ K) (hb : |b| ≤ K) :
    |a * (1 - z) + b * z| ≤ K := by
  have hleft : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
  calc
    _ ≤ |a * (1 - z)| + |b * z| := abs_add_le _ _
    _ = |a| * (1 - z) + |b| * z := by
      rw [abs_mul, abs_mul, abs_of_nonneg hleft, abs_of_nonneg hz.1]
    _ ≤ K * (1 - z) + K * z :=
      add_le_add (mul_le_mul_of_nonneg_right ha hleft)
        (mul_le_mul_of_nonneg_right hb hz.1)
    _ = K := by cas

/-- First-jet bounds follow from the three Bernstein controls. -/
theorem abs_hermitePolynomial_first_le (left h a b da db K z : ℝ)
    (hh : h ≠ 0) (hz : z ∈ Icc 0 1) (ha : |da| ≤ K)
    (hb : |3 * (b - a) / h - da - db| ≤ K) (hc : |db| ≤ K) :
    |polynomialJet 1 (hermitePolynomial left h a b da db) (left + h * z)| ≤ K := by
  rw [hermitePolynomial_first_bernstein _ _ _ _ _ _ _ hh]
  exact abs_quadratic_bernstein_le _ _ _ _ _ hz ha hb hc

/-- Second-jet bounds follow from the two endpoint curvatures. -/
theorem abs_hermitePolynomial_second_le (left h a b da db K z : ℝ)
    (hh : h ≠ 0) (hz : z ∈ Icc 0 1)
    (ha : |6 * (b - a) / h ^ 2 - (4 * da + 2 * db) / h| ≤ K)
    (hb : |-6 * (b - a) / h ^ 2 + (2 * da + 4 * db) / h| ≤ K) :
    |polynomialJet 2 (hermitePolynomial left h a b da db) (left + h * z)| ≤ K := by
  rw [hermitePolynomial_second_affine _ _ _ _ _ _ _ hh]
  exact abs_affine_interpolation_le _ _ _ _ hz ha hb

/-- A uniform slope perturbation changes the first jet by at most twice that bound. -/
theorem hermitePolynomial_first_sub_le (left h a b da db ea eb ε z : ℝ)
    (hh : h ≠ 0) (hz : z ∈ Icc 0 1) (hε : 0 ≤ ε)
    (ha : |da - ea| ≤ ε) (hb : |db - eb| ≤ ε) :
    |polynomialJet 1 (hermitePolynomial left h a b da db) (left + h * z) -
      polynomialJet 1 (hermitePolynomial left h a b ea eb) (left + h * z)| ≤
        2 * ε := by
  have heq :
      polynomialJet 1 (hermitePolynomial left h a b da db) (left + h * z) -
        polynomialJet 1 (hermitePolynomial left h a b ea eb) (left + h * z) =
      (da - ea) * (1 - z) ^ 2 +
        2 * (-(da - ea) - (db - eb)) * z * (1 - z) + (db - eb) * z ^ 2 := by
    rw [hermitePolynomial_first_bernstein _ _ _ _ _ _ _ hh,
      hermitePolynomial_first_bernstein _ _ _ _ _ _ _ hh]
    cas
  rw [heq]
  apply abs_quadratic_bernstein_le _ _ _ _ _ hz
  · linarith
  · calc
      |-(da - ea) - (db - eb)| ≤ |-(da - ea)| + |db - eb| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (-(da - ea)) 0 (db - eb)
      _ ≤ ε + ε := add_le_add (by simpa only [abs_neg] using ha) hb
      _ = 2 * ε := by cas
  · linarith

/-- A uniform slope perturbation changes the second jet by at most six times the
bound divided by the panel width. -/
theorem hermitePolynomial_second_sub_le (left h a b da db ea eb ε z : ℝ)
    (hh : 0 < h) (hz : z ∈ Icc 0 1)
    (ha : |da - ea| ≤ ε) (hb : |db - eb| ≤ ε) :
    |polynomialJet 2 (hermitePolynomial left h a b da db) (left + h * z) -
      polynomialJet 2 (hermitePolynomial left h a b ea eb) (left + h * z)| ≤
        6 * ε / h := by
  have heq :
      polynomialJet 2 (hermitePolynomial left h a b da db) (left + h * z) -
        polynomialJet 2 (hermitePolynomial left h a b ea eb) (left + h * z) =
      (-(4 * (da - ea) + 2 * (db - eb)) / h) * (1 - z) +
        ((2 * (da - ea) + 4 * (db - eb)) / h) * z := by
    rw [hermitePolynomial_second_affine _ _ _ _ _ _ _ hh.ne',
      hermitePolynomial_second_affine _ _ _ _ _ _ _ hh.ne']
    cas using hh.ne'
  rw [heq]
  apply abs_affine_interpolation_le _ _ _ _ hz
  · rw [abs_div, abs_neg, abs_of_pos hh]
    apply div_le_div_of_nonneg_right _ hh.le
    calc
      _ ≤ |4 * (da - ea)| + |2 * (db - eb)| := abs_add_le _ _
      _ = 4 * |da - ea| + 2 * |db - eb| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 4 * ε + 2 * ε :=
        add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
          (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = 6 * ε := by cas
  · rw [abs_div, abs_of_pos hh]
    apply div_le_div_of_nonneg_right _ hh.le
    calc
      _ ≤ |2 * (da - ea)| + |4 * (db - eb)| := abs_add_le _ _
      _ = 2 * |da - ea| + 4 * |db - eb| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * ε + 4 * ε :=
        add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
          (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = 6 * ε := by cas

end CAS.Splines
