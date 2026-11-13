/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import CAS.ExactTactic
import Mathlib.Analysis.Convex.Deriv

/-!
# Odd-power scalar nonlinearities

Scalar facts shared by odd-power semilinear elliptic and nonlinear wave
equations. The polynomial

`linear * z + nonlinear * z ^ (2 * k + 1)`

is the derivative of the canonical potential

`linear / 2 * z² + nonlinear / (2 * (k + 1)) * z ^ (2 * (k + 1))`.

Nonnegative coefficients make both terms in the potential nonnegative and
make the polynomial monotone. If either coefficient is positive, the
polynomial is strictly monotone and the potential vanishes only at zero.

Here `z` is a real number, not a function. The PDE files apply these facts
pointwise to `u(x)` (for the defocusing semilinear elliptic equation
`-Δu + m u + λ u^{2k+1} = f`) or to `u(t,x)` (for the semilinear wave equation
`u_tt - Δu + m u + λ u^{2k+1} = 0`), where the potential is the nonlinear part
of the energy density. With `m = 0` and `λ = 1`, the wave equation in three dimensions is
Evans's subcritical equation (18) of §12.3.3 with `p = 3` when `k = 1`, and his critical
equation (1) of §12.4 when `k = 2`.

## Main results

* `oddPowerPolynomial`, `oddPowerPotential`: the polynomial
  `m z + λ z^{2k+1}` and its primitive `(m/2) z² + (λ/(2k+2)) z^{2k+2}`.
* `hasDerivAt_oddPowerPotential`, `deriv_oddPowerPotential`,
  `contDiff_oddPowerPotential`: the potential is smooth with derivative the
  polynomial.
* `lipschitzOnWith_oddPowerPolynomial`: an explicit Lipschitz constant on
  `[-R, R]`, with no sign condition on the coefficients.
* `monotone_oddPowerPolynomial`, `strictMono_oddPowerPolynomial`,
  `convexOn_oddPowerPotential`, `strictConvexOn_oddPowerPotential`:
  monotonicity and convexity under nonnegative (resp. not both zero)
  coefficients.
* `oddPowerPotential_nonneg`, `oddPowerPotential_eq_zero_iff`,
  `oddPowerPolynomial_mul_self_nonneg`: sign information used in energy
  estimates.
* `mul_deriv_oddPowerPotential_le`: the scaling inequality
  `z V'(z) ≤ 2(k+1) V(z)` for `m ≥ 0`. This is the hypothesis (2), `z f(z) ≤ λ F(z)`, of
  Evans's nonexistence theorem for negative energy, with `f = V'`, `F = V` and his constant
  `λ` equal to `2(k+1)`, which exceeds 2 when `k ≥ 1`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.3, the equation (18), p. 676, §12.4, the
  equation (1), p. 679, and §12.5.1, Theorem 1 (nonexistence for negative energy) and its
  proof, pp. 687-688. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Scalar

/-- A linear term plus a positive odd power. -/
def oddPowerPolynomial
    (linear nonlinear : ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  linear * z + nonlinear * z ^ (2 * k + 1)

/-- The canonical primitive of `oddPowerPolynomial`. -/
def oddPowerPotential
    (linear nonlinear : ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  linear / 2 * z ^ 2 +
    nonlinear / (2 * (k + 1) : ℝ) * z ^ (2 * (k + 1))

/-- The odd-power polynomial vanishes at the origin: both terms have no constant part. -/
@[simp]
theorem oddPowerPolynomial_zero
    (linear nonlinear : ℝ) (k : ℕ) :
    oddPowerPolynomial linear nonlinear k 0 = 0 := by
  simp [oddPowerPolynomial]

/-- The canonical potential is normalized to vanish at the origin. -/
@[simp]
theorem oddPowerPotential_zero
    (linear nonlinear : ℝ) (k : ℕ) :
    oddPowerPotential linear nonlinear k 0 = 0 := by
  simp [oddPowerPotential]

/-- The canonical odd-power potential is smooth. -/
theorem contDiff_oddPowerPotential
    (linear nonlinear : ℝ) (k : ℕ) :
    ContDiff ℝ ⊤ (oddPowerPotential linear nonlinear k) := by
  exact (contDiff_const.mul (contDiff_id.pow 2)).add
    (contDiff_const.mul (contDiff_id.pow (2 * (k + 1))))

/-- The derivative of the canonical potential is the odd-power polynomial. -/
theorem hasDerivAt_oddPowerPotential
    (linear nonlinear : ℝ) (k : ℕ) (z : ℝ) :
    HasDerivAt (oddPowerPotential linear nonlinear k)
      (oddPowerPolynomial linear nonlinear k z) z := by
  unfold oddPowerPotential oddPowerPolynomial
  rw [show 2 * (k + 1) = 2 * k + 2 by ring]
  cas

/-- The scalar derivative formula for the canonical odd-power potential. -/
theorem deriv_oddPowerPotential
    (linear nonlinear : ℝ) (k : ℕ) (z : ℝ) :
    deriv (oddPowerPotential linear nonlinear k) z =
      oddPowerPolynomial linear nonlinear k z :=
  (hasDerivAt_oddPowerPotential linear nonlinear k z).deriv

/-- A nonnegative quadratic coefficient gives the scaling-growth inequality
used by the negative-energy concavity method:

`z V'(z) ≤ 2 (k + 1) V(z)`.

The higher-order coefficient is arbitrary. Its contribution is homogeneous
of degree `2 * (k + 1)` and therefore cancels exactly; the remaining
difference is `k * linear * z²`. -/
theorem mul_deriv_oddPowerPotential_le
    {linear : ℝ} (nonlinear : ℝ) (k : ℕ)
    (hlinear : 0 ≤ linear) (z : ℝ) :
    z * deriv (oddPowerPotential linear nonlinear k) z ≤
      (2 * (k + 1) : ℝ) *
        oddPowerPotential linear nonlinear k z := by
  rw [deriv_oddPowerPotential]
  simp only [oddPowerPolynomial, oddPowerPotential]
  have hk : (k : ℝ) + 1 ≠ 0 := by
    positivity
  rw [show 2 * (k + 1) = 2 * k + 2 by omega,
    pow_add z (2 * k) 2, pow_succ z (2 * k)]
  field_simp
  nlinarith [mul_nonneg (Nat.cast_nonneg k)
    (mul_nonneg hlinear (sq_nonneg z))]

/-- On `[-R, R]`, an odd-power polynomial is Lipschitz with the bound obtained
from its largest possible derivative magnitude on that interval.

No sign condition is imposed on either coefficient. -/
theorem lipschitzOnWith_oddPowerPolynomial
    (linear nonlinear : ℝ) (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith
      (Real.toNNReal
        (|linear| + |nonlinear| * (2 * k + 1 : ℕ) * R ^ (2 * k)))
      (oddPowerPolynomial linear nonlinear k)
      (Set.Icc (-R) R) := by
  have hconstant :
      0 ≤ |linear| + |nonlinear| * (2 * k + 1 : ℕ) * R ^ (2 * k) :=
    add_nonneg (abs_nonneg linear)
      (mul_nonneg
        (mul_nonneg (abs_nonneg nonlinear) (Nat.cast_nonneg _))
        (pow_nonneg hR _))
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.coe_toNNReal _ hconstant, Real.dist_eq, Real.dist_eq]
  have hxabs : |x| ≤ R := abs_le.mpr hx
  have hyabs : |y| ≤ R := abs_le.mpr hy
  have hmax : max |x| |y| ≤ R := max_le hxabs hyabs
  have hpower :
      |x ^ (2 * k + 1) - y ^ (2 * k + 1)| ≤
        |x - y| * (2 * k + 1 : ℕ) * R ^ (2 * k) := by
    calc
      |x ^ (2 * k + 1) - y ^ (2 * k + 1)| ≤
          |x - y| * (2 * k + 1 : ℕ) *
            max |x| |y| ^ (2 * k + 1 - 1) :=
        abs_pow_sub_pow_le x y (2 * k + 1)
      _ = |x - y| * (2 * k + 1 : ℕ) *
            max |x| |y| ^ (2 * k) := by
        congr 2
      _ ≤ |x - y| * (2 * k + 1 : ℕ) * R ^ (2 * k) := by
        gcongr
  change
    |oddPowerPolynomial linear nonlinear k x -
        oddPowerPolynomial linear nonlinear k y| ≤
      (|linear| + |nonlinear| * (2 * k + 1 : ℕ) * R ^ (2 * k)) * |x - y|
  calc
    |oddPowerPolynomial linear nonlinear k x -
        oddPowerPolynomial linear nonlinear k y| =
        |linear * (x - y) +
          nonlinear * (x ^ (2 * k + 1) - y ^ (2 * k + 1))| := by
      congr 1
      simp only [oddPowerPolynomial]
      ring
    _ ≤ |linear * (x - y)| +
          |nonlinear * (x ^ (2 * k + 1) - y ^ (2 * k + 1))| :=
      abs_add_le _ _
    _ = |linear| * |x - y| +
          |nonlinear| * |x ^ (2 * k + 1) - y ^ (2 * k + 1)| := by
      rw [abs_mul, abs_mul]
    _ ≤ |linear| * |x - y| +
          |nonlinear| * (|x - y| * (2 * k + 1 : ℕ) * R ^ (2 * k)) := by
      gcongr
    _ = (|linear| + |nonlinear| * (2 * k + 1 : ℕ) * R ^ (2 * k)) *
          |x - y| := by
      ring

/-- Nonnegative coefficients make a linear-plus-odd-power polynomial
monotone. -/
theorem monotone_oddPowerPolynomial
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear) :
    Monotone (oddPowerPolynomial linear nonlinear k) := by
  change Monotone fun z : ℝ ↦
    linear * z + nonlinear * z ^ (2 * k + 1)
  exact (monotone_id.const_mul hlinear).add
    ((odd_two_mul_add_one k).strictMono_pow.monotone.const_mul hnonlinear)

/-- Adding the negative part of the linear coefficient makes an odd-power
polynomial monotone whenever its higher-order coefficient is nonnegative. -/
theorem monotone_oddPowerPolynomial_add_negPart
    {linear nonlinear : ℝ} (k : ℕ)
    (hnonlinear : 0 ≤ nonlinear) :
    Monotone fun z ↦
      oddPowerPolynomial linear nonlinear k z +
        linear⁻ * z := by
  have hlinear : 0 ≤ linear + linear⁻ := by
    calc
      0 ≤ linear⁺ := posPart_nonneg linear
      _ = linear + linear⁻ := by
        linarith [posPart_sub_negPart linear]
  convert monotone_oddPowerPolynomial
    (linear := linear + linear⁻)
    (nonlinear := nonlinear) k hlinear hnonlinear using 1
  funext z
  simp only [oddPowerPolynomial]
  ring

/-- The derivative of a canonical odd-power potential with nonnegative
coefficients is monotone. -/
theorem monotone_deriv_oddPowerPotential
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear) :
    Monotone (deriv (oddPowerPotential linear nonlinear k)) := by
  intro x y hxy
  simpa only [deriv_oddPowerPotential] using
    monotone_oddPowerPolynomial k hlinear hnonlinear hxy

/-- Nonnegative coefficients make the canonical odd-power potential convex
on the real line. -/
theorem convexOn_oddPowerPotential
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear) :
    ConvexOn ℝ Set.univ (oddPowerPotential linear nonlinear k) := by
  exact (monotone_deriv_oddPowerPotential k hlinear hnonlinear).convexOn_univ_of_deriv
    ((contDiff_oddPowerPotential linear nonlinear k).differentiable (by simp))

/-- A nonnegative linear-plus-odd-power polynomial has nonnegative pairing
with its argument. -/
theorem oddPowerPolynomial_mul_self_nonneg
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear) (z : ℝ) :
    0 ≤ oddPowerPolynomial linear nonlinear k z * z := by
  have hmono :=
    monotone_oddPowerPolynomial k hlinear hnonlinear
  rcases le_total z 0 with hz | hz
  · exact mul_nonneg_of_nonpos_of_nonpos
      (by simpa using hmono hz) hz
  · exact mul_nonneg
      (by simpa using hmono hz) hz

/-- A positive linear coefficient makes the polynomial strictly monotone,
even when the odd-power coefficient is only nonnegative. -/
theorem strictMono_oddPowerPolynomial_of_linear_pos
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 < linear) (hnonlinear : 0 ≤ nonlinear) :
    StrictMono (oddPowerPolynomial linear nonlinear k) := by
  change StrictMono fun z : ℝ ↦
    linear * z + nonlinear * z ^ (2 * k + 1)
  exact (strictMono_id.const_mul hlinear).add_monotone
    ((odd_two_mul_add_one k).strictMono_pow.monotone.const_mul hnonlinear)

/-- A positive odd-power coefficient makes the polynomial strictly monotone,
even when the linear coefficient is only nonnegative. -/
theorem strictMono_oddPowerPolynomial_of_nonlinear_pos
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 < nonlinear) :
    StrictMono (oddPowerPolynomial linear nonlinear k) := by
  change StrictMono fun z : ℝ ↦
    linear * z + nonlinear * z ^ (2 * k + 1)
  exact (monotone_id.const_mul hlinear).add_strictMono
    ((odd_two_mul_add_one k).strictMono_pow.const_mul hnonlinear)

/-- Nonnegative coefficients, not both zero, make the polynomial strictly
monotone. -/
theorem strictMono_oddPowerPolynomial
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear)
    (hpositive : 0 < linear ∨ 0 < nonlinear) :
    StrictMono (oddPowerPolynomial linear nonlinear k) := by
  rcases hpositive with hlinearPos | hnonlinearPos
  · exact strictMono_oddPowerPolynomial_of_linear_pos
      k hlinearPos hnonlinear
  · exact strictMono_oddPowerPolynomial_of_nonlinear_pos
      k hlinear hnonlinearPos

/-- The derivative of a canonical odd-power potential is strictly monotone
when its coefficients are nonnegative and not both zero. -/
theorem strictMono_deriv_oddPowerPotential
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear)
    (hpositive : 0 < linear ∨ 0 < nonlinear) :
    StrictMono (deriv (oddPowerPotential linear nonlinear k)) := by
  intro x y hxy
  simpa only [deriv_oddPowerPotential] using
    strictMono_oddPowerPolynomial k hlinear hnonlinear hpositive hxy

/-- If the nonnegative coefficients are not both zero, the canonical
odd-power potential is strictly convex on the real line. -/
theorem strictConvexOn_oddPowerPotential
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear)
    (hpositive : 0 < linear ∨ 0 < nonlinear) :
    StrictConvexOn ℝ Set.univ (oddPowerPotential linear nonlinear k) := by
  exact
    (strictMono_deriv_oddPowerPotential k hlinear hnonlinear hpositive)
      |>.strictConvexOn_univ_of_deriv
        (contDiff_oddPowerPotential linear nonlinear k).continuous

/-- Nonnegative coefficients give a nonnegative canonical odd-power
potential. -/
theorem oddPowerPotential_nonneg
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear) (z : ℝ) :
    0 ≤ oddPowerPotential linear nonlinear k z := by
  have heven : 0 ≤ z ^ (2 * (k + 1)) :=
    (even_two_mul (k + 1)).pow_nonneg z
  exact add_nonneg
    (mul_nonneg (div_nonneg hlinear (by norm_num)) (sq_nonneg z))
    (mul_nonneg (div_nonneg hnonlinear (by positivity)) heven)

/-- The quadratic term is a lower bound when the odd-power coefficient is
nonnegative. -/
theorem oddPowerPotential_quadratic_le
    {linear nonlinear : ℝ} (k : ℕ)
    (hnonlinear : 0 ≤ nonlinear) (z : ℝ) :
    linear / 2 * z ^ 2 ≤ oddPowerPotential linear nonlinear k z := by
  unfold oddPowerPotential
  exact le_add_of_nonneg_right
    (mul_nonneg (div_nonneg hnonlinear (by positivity))
      ((even_two_mul (k + 1)).pow_nonneg z))

/-- The higher-power term is a lower bound when the linear coefficient is
nonnegative. -/
theorem oddPowerPotential_power_le
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (z : ℝ) :
    nonlinear / (2 * (k + 1) : ℝ) * z ^ (2 * (k + 1)) ≤
      oddPowerPotential linear nonlinear k z := by
  unfold oddPowerPotential
  exact le_add_of_nonneg_left
    (mul_nonneg (div_nonneg hlinear (by norm_num)) (sq_nonneg z))

/-- With nonnegative coefficients, one of them positive, the canonical
odd-power potential vanishes exactly at zero. -/
theorem oddPowerPotential_eq_zero_iff
    {linear nonlinear : ℝ} (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear)
    (hpositive : 0 < linear ∨ 0 < nonlinear) (z : ℝ) :
    oddPowerPotential linear nonlinear k z = 0 ↔ z = 0 := by
  constructor
  · intro hzero
    rcases hpositive with hlinearPos | hnonlinearPos
    · have hquadratic :=
        oddPowerPotential_quadratic_le
          (linear := linear) k hnonlinear z
      have hcoefficient : 0 < linear / 2 :=
        div_pos hlinearPos (by norm_num)
      have hproduct :
          linear / 2 * z ^ 2 = 0 := by
        apply le_antisymm
        · simpa only [hzero] using hquadratic
        · exact mul_nonneg hcoefficient.le (sq_nonneg z)
      have hzsq : z ^ 2 = 0 :=
        (mul_eq_zero.mp hproduct).resolve_left hcoefficient.ne'
      exact sq_eq_zero_iff.mp hzsq
    · have hpower :=
        oddPowerPotential_power_le
          (nonlinear := nonlinear) k hlinear z
      have hcoefficient :
          0 < nonlinear / (2 * (k + 1) : ℝ) :=
        div_pos hnonlinearPos (by positivity)
      have hproduct :
          nonlinear / (2 * (k + 1) : ℝ) *
              z ^ (2 * (k + 1)) = 0 := by
        apply le_antisymm
        · simpa only [hzero] using hpower
        · exact mul_nonneg hcoefficient.le
            ((even_two_mul (k + 1)).pow_nonneg z)
      have hzpow : z ^ (2 * (k + 1)) = 0 :=
        (mul_eq_zero.mp hproduct).resolve_left hcoefficient.ne'
      exact (pow_eq_zero_iff (by omega : 2 * (k + 1) ≠ 0)).mp hzpow
  · rintro rfl
    exact oddPowerPotential_zero linear nonlinear k

end PDE.Analysis.Scalar
