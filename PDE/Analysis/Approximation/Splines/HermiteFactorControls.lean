/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteSign
import CAS.ExactTactic

/-!
# Bernstein controls for a Hermite polynomial minus a weighted derivative

For a physical panel of width `h`, the factor `p - κ * (x - center) * p'`
is cubic. Its Bernstein coefficients are affine in the two physical slopes.
The coefficient formulas and their slope-error radii give finite sign
certificates without sampling between nodes.
-/

@[expose] public section

noncomputable section

open Set Polynomial

namespace CAS.Splines

/-- The part of each factor coefficient determined by the nodal values.
Here `s` is the left endpoint minus the factor's center. -/
def hermiteFactorConstant (κ s h a b : ℝ) : Fin 4 → ℝ :=
  ![a, a - 2 * κ * s * (b - a) / h,
    b - 2 * κ * (s + h) * (b - a) / h, b]

/-- The coefficient of the left physical slope in each Bernstein control. -/
def hermiteFactorLeftSlope (κ s h : ℝ) : Fin 4 → ℝ :=
  ![-κ * s, ((1 - κ) * h + κ * s) / 3, 2 * κ * (s + h) / 3, 0]

/-- The coefficient of the right physical slope in each Bernstein control. -/
def hermiteFactorRightSlope (κ s h : ℝ) : Fin 4 → ℝ :=
  ![0, 2 * κ * s / 3, (κ * (s + h) - (1 - κ) * h) / 3, -κ * (s + h)]

/-- The four Bernstein controls of `p - κ * (x - center) * p'`. -/
def hermiteFactorControl (κ s h a b da db : ℝ) (k : Fin 4) : ℝ :=
  hermiteFactorConstant κ s h a b k +
    hermiteFactorLeftSlope κ s h k * da + hermiteFactorRightSlope κ s h k * db

/-- A common error in both physical slopes changes a control by at most this
nonnegative factor times the slope error. -/
def hermiteFactorRadius (κ s h : ℝ) (k : Fin 4) : ℝ :=
  |hermiteFactorLeftSlope κ s h k| + |hermiteFactorRightSlope κ s h k|

/-- The factor controls are the coefficients in Mathlib's Bernstein basis. -/
theorem hermitePolynomial_factor_eq_bernstein
    (κ center left h a b da db x : ℝ) (hh : h ≠ 0) :
    let p := hermitePolynomial left h a b da db
    let control := hermiteFactorControl κ (left - center) h a b da db
    let z := (x - left) / h
    p.eval x - κ * (x - center) * polynomialJet 1 p x =
      control 0 * (bernsteinPolynomial ℝ 3 0).eval z +
      control 1 * (bernsteinPolynomial ℝ 3 1).eval z +
      control 2 * (bernsteinPolynomial ℝ 3 2).eval z +
      control 3 * (bernsteinPolynomial ℝ 3 3).eval z := by
  dsimp only
  simp only [hermiteFactorControl, hermiteFactorConstant, hermiteFactorLeftSlope,
    hermiteFactorRightSlope, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, bernsteinPolynomial,
    polynomialJet, Function.iterate_one, hermitePolynomial, map_add, map_mul,
    derivative_C, derivative_mul, derivative_pow, derivative_sub, derivative_X,
    zero_add, zero_mul, mul_zero, add_zero, one_mul, sub_zero,
    eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_pow, eval_natCast, eval_one]
  norm_num
  cas using hh

/-- A cubic with nonpositive controls and a negative endpoint control is negative
inside the panel. Included boundary points require their own strict endpoint control. -/
theorem bernstein_cubic_neg_of_controls (control : Fin 4 → ℝ) {z : ℝ}
    (hz : z ∈ Icc 0 1) (hnonpos : ∀ k, control k ≤ 0)
    (hstrict : control 0 < 0 ∨ control 3 < 0)
    (hzero : z = 0 → control 0 < 0) (hone : z = 1 → control 3 < 0) :
    control 0 * (bernsteinPolynomial ℝ 3 0).eval z +
      control 1 * (bernsteinPolynomial ℝ 3 1).eval z +
      control 2 * (bernsteinPolynomial ℝ 3 2).eval z +
      control 3 * (bernsteinPolynomial ℝ 3 3).eval z < 0 := by
  have heq : control 0 * (bernsteinPolynomial ℝ 3 0).eval z +
      control 1 * (bernsteinPolynomial ℝ 3 1).eval z +
      control 2 * (bernsteinPolynomial ℝ 3 2).eval z +
      control 3 * (bernsteinPolynomial ℝ 3 3).eval z =
      hermiteValue 1 (control 0) (control 3)
        (3 * (control 1 - control 0)) (3 * (control 3 - control 2)) z := by
    rw [hermiteValue_eq_bernstein]
    cas
  rw [heq]
  by_cases hz0 : z = 0
  · simpa only [hz0, hermiteValue_zero] using hzero hz0
  by_cases hz1 : z = 1
  · simpa only [hz1, hermiteValue_one] using hone hz1
  apply hermiteValue_neg_of_controls (hnonpos 0) (hnonpos 3) _ _ hstrict
    ⟨lt_of_le_of_ne hz.1 (Ne.symm hz0), lt_of_le_of_ne hz.2 hz1⟩
  · convert hnonpos 1 using 1
    cas
  · convert hnonpos 2 using 1
    cas

/-- A finite Bernstein certificate proves the weighted-derivative factor
negative on a physical panel, allowing zero coefficients at excluded endpoints. -/
theorem hermitePolynomial_factor_neg_of_controls
    (κ center left h a b da db : ℝ) {x : ℝ} (hh : 0 < h)
    (hx : x ∈ Icc left (left + h))
    (hnonpos : ∀ k, hermiteFactorControl κ (left - center) h a b da db k ≤ 0)
    (hstrict : hermiteFactorControl κ (left - center) h a b da db 0 < 0 ∨
      hermiteFactorControl κ (left - center) h a b da db 3 < 0)
    (hleft : x = left → hermiteFactorControl κ (left - center) h a b da db 0 < 0)
    (hright : x = left + h → hermiteFactorControl κ (left - center) h a b da db 3 < 0) :
    (hermitePolynomial left h a b da db).eval x -
      κ * (x - center) * polynomialJet 1 (hermitePolynomial left h a b da db) x < 0 := by
  rw [hermitePolynomial_factor_eq_bernstein κ center left h a b da db x hh.ne']
  refine bernstein_cubic_neg_of_controls _ ?_ hnonpos hstrict ?_ ?_
  · exact ⟨div_nonneg (sub_nonneg.mpr hx.1) hh.le,
      (div_le_one hh).mpr (by linarith [hx.2])⟩
  · intro hz
    apply hleft
    have hnum := (div_eq_zero_iff.mp hz).resolve_right hh.ne'
    exact sub_eq_zero.mp hnum
  · intro hz
    apply hright
    have hnum := (div_eq_one_iff_eq hh.ne').mp hz
    linarith only [hnum]

/-- A slope enclosure gives an exact absolute error bound for every control. -/
theorem abs_hermiteFactorControl_sub_le
    (κ s h a b da db pa pb ε : ℝ) (k : Fin 4)
    (ha : |da - pa| ≤ ε) (hb : |db - pb| ≤ ε) :
    |hermiteFactorControl κ s h a b da db k -
      hermiteFactorControl κ s h a b pa pb k| ≤ hermiteFactorRadius κ s h k * ε := by
  have heq : hermiteFactorControl κ s h a b da db k -
      hermiteFactorControl κ s h a b pa pb k =
      hermiteFactorLeftSlope κ s h k * (da - pa) +
        hermiteFactorRightSlope κ s h k * (db - pb) := by
    unfold hermiteFactorControl
    cas
  rw [heq]
  calc
    _ ≤ |hermiteFactorLeftSlope κ s h k * (da - pa)| +
        |hermiteFactorRightSlope κ s h k * (db - pb)| := abs_add_le _ _
    _ = |hermiteFactorLeftSlope κ s h k| * |da - pa| +
        |hermiteFactorRightSlope κ s h k| * |db - pb| := by rw [abs_mul, abs_mul]
    _ ≤ |hermiteFactorLeftSlope κ s h k| * ε +
        |hermiteFactorRightSlope κ s h k| * ε :=
      add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
    _ = _ := by unfold hermiteFactorRadius; cas

/-- The candidate control plus its exact radius bounds the true control from above. -/
theorem hermiteFactorControl_le_of_slope_error
    (κ s h a b da db pa pb ε : ℝ) (k : Fin 4)
    (ha : |da - pa| ≤ ε) (hb : |db - pb| ≤ ε) :
    hermiteFactorControl κ s h a b da db k ≤
      hermiteFactorControl κ s h a b pa pb k + hermiteFactorRadius κ s h k * ε := by
  have herror := abs_hermiteFactorControl_sub_le κ s h a b da db pa pb ε k ha hb
  have hle := (le_abs_self _).trans herror
  linarith only [hle]

end CAS.Splines
