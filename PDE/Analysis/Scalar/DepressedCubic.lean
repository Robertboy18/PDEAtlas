/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The real root of a depressed cubic

For the depressed cubic `Z³ + p Z + q` with `q² + 4 p³ / 27 ≥ 0`, Cardano's formula

`Z = r - p / (3 r)`,  `r = ((-q + √(q² + 4 p³ / 27)) / 2)^{1/3}`

gives a real root whenever `r > 0`. When the discriminant `-(4 p³ + 27 q²)` is negative the real
root is unique: two distinct real roots `Z₁, Z₂` would force
`4 p³ + 27 q² = -(Z₁ - Z₂)² (2 Z₁ + Z₂)² (Z₁ + 2 Z₂)² ≤ 0`.

Chen and Hou, Part I, Section 3.3.1, reduce the transport map of their Hölder estimate of `u_x`
to the cubic equation (3.14). Appendix B.3.2 shifts it to a depressed cubic, shows with the
discriminant (B.64) that the real root is unique, and gives the root by this formula, (B.65).

## Main declarations

* `cardanoRoot p q`: Cardano's expression.
* `cardanoRoot_cubic_eq_zero`: it is a root when `-q + √(q² + 4 p³ / 27) > 0`.
* `eq_of_cubic_eq_zero_of_discr_pos`: uniqueness of the real root when `4 p³ + 27 q² > 0`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3.3.1, (3.14), and
  Appendix B.3.2, (B.63)-(B.65). <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Scalar

/-- The cube root `r = ((-q + √(q² + 4 p³ / 27)) / 2)^{1/3}` in Cardano's formula. -/
def cardanoRadical (p q : ℝ) : ℝ :=
  ((-q + Real.sqrt (q ^ 2 + 4 * p ^ 3 / 27)) / 2) ^ (1 / 3 : ℝ)

/-- Cardano's expression `r - p / (3 r)` for a real root of `Z³ + p Z + q`. -/
def cardanoRoot (p q : ℝ) : ℝ :=
  cardanoRadical p q - p / (3 * cardanoRadical p q)

/-- The radical cubed is `(-q + √(q² + 4 p³ / 27)) / 2` when this is nonnegative. -/
theorem cardanoRadical_pow_three {p q : ℝ} (h : 0 ≤ -q + Real.sqrt (q ^ 2 + 4 * p ^ 3 / 27)) :
    cardanoRadical p q ^ 3 = (-q + Real.sqrt (q ^ 2 + 4 * p ^ 3 / 27)) / 2 := by
  rw [cardanoRadical, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  norm_num

/-- The radical is positive when `-q + √(q² + 4 p³ / 27) > 0`. -/
theorem cardanoRadical_pos {p q : ℝ} (h : 0 < -q + Real.sqrt (q ^ 2 + 4 * p ^ 3 / 27)) :
    0 < cardanoRadical p q :=
  Real.rpow_pos_of_pos (by linarith) _

/-- **Cardano's formula.** If `q² + 4 p³ / 27 ≥ 0` and `-q + √(q² + 4 p³ / 27) > 0`, then
`cardanoRoot p q` is a root of `Z³ + p Z + q`. -/
theorem cardanoRoot_cubic_eq_zero {p q : ℝ} (hD : 0 ≤ q ^ 2 + 4 * p ^ 3 / 27)
    (h : 0 < -q + Real.sqrt (q ^ 2 + 4 * p ^ 3 / 27)) :
    cardanoRoot p q ^ 3 + p * cardanoRoot p q + q = 0 := by
  have hr := cardanoRadical_pos h
  have h3 := cardanoRadical_pow_three h.le
  have hs := Real.sq_sqrt hD
  set r := cardanoRadical p q
  set s := Real.sqrt (q ^ 2 + 4 * p ^ 3 / 27)
  have hr0 : r ≠ 0 := hr.ne'
  have key : (r ^ 3) ^ 2 + q * r ^ 3 - p ^ 3 / 27 = 0 := by
    rw [h3]
    linear_combination (1 / 4 : ℝ) * hs
  have hexp : (r - p / (3 * r)) ^ 3 + p * (r - p / (3 * r)) + q =
      ((r ^ 3) ^ 2 + q * r ^ 3 - p ^ 3 / 27) / r ^ 3 := by
    field_simp
    ring
  change (r - p / (3 * r)) ^ 3 + p * (r - p / (3 * r)) + q = 0
  rw [hexp, key, zero_div]

/-- Two distinct real roots of `Z³ + p Z + q` force `4 p³ + 27 q² ≤ 0`: the real root is unique
when `4 p³ + 27 q² > 0`. -/
theorem eq_of_cubic_eq_zero_of_discr_pos {p q Z₁ Z₂ : ℝ} (hdisc : 0 < 4 * p ^ 3 + 27 * q ^ 2)
    (h₁ : Z₁ ^ 3 + p * Z₁ + q = 0) (h₂ : Z₂ ^ 3 + p * Z₂ + q = 0) : Z₁ = Z₂ := by
  by_contra hne
  have hsub : Z₁ - Z₂ ≠ 0 := sub_ne_zero.2 hne
  have hp : p = -(Z₁ ^ 2 + Z₁ * Z₂ + Z₂ ^ 2) := by
    have : (Z₁ - Z₂) * (Z₁ ^ 2 + Z₁ * Z₂ + Z₂ ^ 2 + p) = 0 := by linear_combination h₁ - h₂
    linarith [(mul_eq_zero.1 this).resolve_left hsub]
  have hq : q = Z₁ * Z₂ * (Z₁ + Z₂) := by
    rw [hp] at h₁
    linarith
  have hid : 4 * p ^ 3 + 27 * q ^ 2 =
      -((Z₁ - Z₂) ^ 2 * (2 * Z₁ + Z₂) ^ 2 * (Z₁ + 2 * Z₂) ^ 2) := by
    rw [hp, hq]
    ring
  have : 0 ≤ (Z₁ - Z₂) ^ 2 * (2 * Z₁ + Z₂) ^ 2 * (Z₁ + 2 * Z₂) ^ 2 := by positivity
  linarith

/-- Cardano's expression is continuous in the coefficients on the set where the radicand
`-q + √(q² + 4 p³ / 27)` is positive. -/
theorem continuousAt_cardanoRoot {p q : ℝ} (h : 0 < -q + Real.sqrt (q ^ 2 + 4 * p ^ 3 / 27)) :
    ContinuousAt (fun v : ℝ × ℝ ↦ cardanoRoot v.1 v.2) (p, q) := by
  have hrad : ContinuousAt (fun v : ℝ × ℝ ↦ cardanoRadical v.1 v.2) (p, q) := by
    unfold cardanoRadical
    refine ContinuousAt.rpow_const ?_ (Or.inl (by linarith))
    fun_prop
  have hr := cardanoRadical_pos h
  unfold cardanoRoot
  exact hrad.sub ((continuous_fst.continuousAt).div (continuousAt_const.mul hrad) (by positivity))

/-- Cardano's expression is measurable in the coefficients. -/
theorem measurable_cardanoRoot : Measurable fun v : ℝ × ℝ ↦ cardanoRoot v.1 v.2 := by
  unfold cardanoRoot cardanoRadical
  fun_prop

end PDE.Analysis.Scalar
