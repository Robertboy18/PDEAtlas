/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum.RealSqrt
public import PDE.Analysis.Scalar.AbsMul
public import PDE.Analysis.Scalar.Discrete
public import PDE.Analysis.Scalar.Inequalities.Basic
public import PDE.Analysis.Scalar.Powers

set_option linter.style.header false

/-!
# Inequalities between real numbers

The lemmas bound squares, products, absolute values and fractions of real numbers: Young-type bounds
of a product by squares, bounds of a sum by the sum of the bounds, comparisons of two expressions
under sign conditions. Almost every proof is a short calculation closed by `nlinarith`, `linarith`,
`positivity` or `field_simp`, sometimes after a case split.

## Main results

* `PDE.Analysis.sum_four_mul_mul_le_sum_sq`: Let `c1`, `c2`, `c3`, `c4` be real numbers that are at
  most `K`, with `c1`, `c3`, `c4` nonnegative, and let `S1`, `S2`, `S3`, `S4` be nonnegative real
  numbers. Then `c1 * S2 * S1 + c2 * S1 ^ 2 + c3 * S4 * S1 + c4 * S3 * S1 ≤ 4 * K * (S1 ^ 2 +
  S2 ^ 2 + S3 ^ 2 + S4 ^ 2)`.
* `PDE.Analysis.sqrt_mul_sqrt_le_half_mul_add`: Young-type bound: for reals `a ≥ 0`, `b ≥ 0` and
  `ℓ > 0`, `√a * √b ≤ (1 / 2) * (ℓ * b + a / ℓ)`. This is `two_mul_mul_le_mul_sq_add` for `√b` and
  `√a`, divided by `2`.
* `PDE.Analysis.abs_mul_add_mul_le_add_mul`: For real numbers with `|c| ≤ 1`, `|p1| ≤ M1`,
  `|p2| ≤ M2` and `|x| ≤ B`, `|c * (p1 + p2) * x| ≤ (M1 + M2) * B`.
* `PDE.Analysis.abs_mul_mul_add_mul_mul_le`: For real numbers with `|c| ≤ 1`, `|a1| * |g| ≤ M1`,
  `|a2| * |g| ≤ M2`, `|b1| ≤ B1` and `|b2| ≤ B2`,
  `|c * (a1 * b1 + a2 * b2) * g| ≤ M1 * B1 + M2 * B2`.
* `PDE.Analysis.abs_mul_mul_le_of_le_one`: For real numbers with `0 ≤ a`, `a ≤ A`, `0 ≤ x`, `x ≤ X`,
  `0 ≤ e` and `e ≤ 1`, `|a * x * e| ≤ A * X`.
* `PDE.Analysis.abs_mul_mul_mul_le_of_le`: For real numbers with `|a| ≤ α`, `|b| ≤ β`, `|c| ≤ γ` and
  `|d| ≤ δ`, `|a * b * c * d| ≤ α * β * γ * δ`.
* `PDE.Analysis.abs_mul_sq_sub_mul_sq_le`: For real numbers with `|c| ≤ M`, `0 ≤ a`, `0 ≤ a'`,
  `|a' - a| ≤ d` and `0 < t`,
  `|c * a' ^ 2 - c * a ^ 2| ≤ (2 * M) * (1 + 1 / t) * d ^ 2 + (2 * M) * t * a ^ 2`.
* `PDE.Analysis.abs_mul_sub_mul_le_add_sq`: For real numbers with `0 ≤ a`, `0 ≤ b'`, `|a' - a| ≤ d`,
  `|b' - b| ≤ e` and `0 < t`,
  `|a' * b' - a * b| ≤ (1 + 1 / t) * (d ^ 2 + e ^ 2) + t * (a ^ 2 + b ^ 2)`.

There are 142 further lemmas of the same kind.

## Implementation notes

Young's inequality for a product, `2 * (a * b) ≤ β * a ^ 2 + b ^ 2 / β`, is Mathlib's
`two_mul_le_add_mul_sq`; `two_mul_mul_le_mul_sq_add` of `PDE.Analysis.Scalar.Inequalities.Basic`
states it in the notation of these modules. Its consequences include `two_mul_le_mul_sq_add_div`,
`mul_le_split_squares` and `sqrt_mul_sqrt_le_half_mul_add`. `sq_le_add_pow_six_div_sq` is
`sq_le_pow_six_div_sq_add` of that module with the summands exchanged.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Set Real

namespace PDE.Analysis

/-- A chain of bounds for real numbers `v B c Y Lp ρ C`: if `|v| ≤ B`, `B = c * Y`, `Y ≤ Lp * ρ`,
`0 ≤ c`, `c * Lp ≤ C` and `0 ≤ ρ`, then `|v| ≤ C * ρ`. -/
theorem abs_le_mul_of_le_mul_mul {v B c Y Lp ρ C : ℝ} (hv : |v| ≤ B) (hB : B = c * Y)
    (hY : Y ≤ Lp * ρ) (hc : 0 ≤ c)
    (hC : c * Lp ≤ C) (hρ : 0 ≤ ρ) : |v| ≤ C * ρ := by
  calc |v| ≤ c * Y := hB ▸ hv
    _ ≤ c * (Lp * ρ) := mul_le_mul_of_nonneg_left hY hc
    _ = (c * Lp) * ρ := by ring
    _ ≤ C * ρ := mul_le_mul_of_nonneg_right hC hρ

/-- For real numbers, if `x = a * w`, `|a| ≤ M` and `0 ≤ w`, then `|x| ≤ M * w`. -/
theorem abs_le_of_eq_mul {x a w M : ℝ} (h : x = a * w) (ha : |a| ≤ M) (hw : 0 ≤ w) : |x| ≤ M * w :=
    by
  rw [h, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right ha hw

/-- For real numbers, if `0 ≤ a` and `a ≤ M` then `|a| ≤ M`. -/
theorem abs_le_of_nonneg_of_le {a M : ℝ} (h0 : 0 ≤ a) (h : a ≤ M) : |a| ≤ M := by
  rw [abs_of_nonneg h0]
  exact h

/-- A real `x` in `[0, 1]` satisfies `|x| ≤ 1`. -/
theorem abs_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : |x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hx.1], hx.2⟩

/-- For real numbers with `1 ≤ B` and `|x| ≤ B`, one has `|x| ≤ B ^ 3`. -/
theorem abs_le_pow_three_of_abs_le {x B : ℝ} (hB : 1 ≤ B) (hx : |x| ≤ B) : |x| ≤ B ^ 3 := by
  have h2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have h3 : B ≤ B ^ 3 := by
    calc B = B * 1 := (mul_one B).symm
      _ ≤ B * B ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = B ^ 3 := by ring
  linarith

/-- For a real `y`, `|max y 0| ≤ |y|`. -/
theorem abs_max_zero_le (y : ℝ) : |max y 0| ≤ |y| := by
  rcases le_total y 0 with h | h
  · rw [max_eq_right h]
    simp
  · rw [max_eq_left h]

/-- For real numbers, `|c * a + d * b| ≤ |c| * |a| + |d| * |b|`. -/
theorem abs_mul_add_mul_le (a b c d : ℝ) : |c * a + d * b| ≤ |c| * |a| + |d| * |b| :=
  (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])

/-- For real numbers with `|c| ≤ 1`, `|p1| ≤ M1`, `|p2| ≤ M2` and `|x| ≤ B`,
`|c * (p1 + p2) * x| ≤ (M1 + M2) * B`. -/
theorem abs_mul_add_mul_le_add_mul {c p1 p2 x M1 M2 B : ℝ} (hc : |c| ≤ 1) (h1 : |p1| ≤ M1)
    (h2 : |p2| ≤ M2)
    (hx : |x| ≤ B) : |c * (p1 + p2) * x| ≤ (M1 + M2) * B := by
  have hS : |p1 + p2| ≤ M1 + M2 := (abs_add_le _ _).trans (add_le_add h1 h2)
  have := abs_mul_le_of_le (abs_mul_le_of_le hc hS) hx
  rwa [one_mul] at this

/-- For real numbers with `0 ≤ p`, `p ≤ M`, `0 ≤ e` and `e ≤ 1`, `|p * e| ≤ M`. -/
theorem abs_mul_le_of_le_one {p e M : ℝ} (hp : 0 ≤ p) (hpM : p ≤ M) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    |p * e| ≤ M := by
  rw [abs_of_nonneg (mul_nonneg hp he0)]
  nlinarith

/-- For real numbers with `0 ≤ a`, `0 ≤ b`, `0 ≤ r` and `k ^ 2 * a ≤ 8 * a + 2 * r ^ 2 * b`,
`|k| * a ≤ 3 * a + r * (a + b)`. The proof compares the squares of the two nonnegative sides, using
`(|k| * a) ^ 2 = a * (k ^ 2 * a)`. -/
theorem abs_mul_le_of_sq_mul_le (k a b r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (h : k ^ 2 * a ≤ 8 * a + 2 * r ^ 2 * b) : |k| * a ≤ 3 * a + r * (a + b) := by
  have h0 : 0 ≤ |k| * a := mul_nonneg (abs_nonneg k) ha
  have h1 : 0 ≤ 3 * a + r * (a + b) := by positivity
  have hk : |k| ^ 2 = k ^ 2 := sq_abs k
  have hsq : (|k| * a) ^ 2 ≤ (3 * a + r * (a + b)) ^ 2 := by
    have e : (|k| * a) ^ 2 = a * (k ^ 2 * a) := by rw [mul_pow, hk]; ring
    rw [e]
    have h3 : a * (k ^ 2 * a) ≤ a * (8 * a + 2 * r ^ 2 * b) := mul_le_mul_of_nonneg_left h ha
    nlinarith [sq_nonneg (a - b), mul_nonneg hr ha, mul_nonneg hr hb, mul_nonneg ha hb,
      mul_nonneg (mul_nonneg hr hr) (mul_nonneg ha hb), sq_nonneg (r * (a - b))]
  exact (pow_le_pow_iff_left₀ h0 h1 (by norm_num)).1 hsq

/-- For real numbers with `1 ≤ B`, `|x| ≤ B` and `|y| ≤ B`, the product satisfies `|x * y| ≤ B ^ 3`.
-/
theorem abs_mul_le_pow_three {x y B : ℝ} (hB : 1 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |x * y| ≤ B ^ 3 := by
  have h1 : |x| * |y| ≤ B * B := mul_le_mul hx hy (abs_nonneg y) (by linarith)
  rw [abs_mul]
  nlinarith

/-- For real numbers with `|c| ≤ 1`, `|a1| * |g| ≤ M1`, `|a2| * |g| ≤ M2`, `|b1| ≤ B1` and
`|b2| ≤ B2`, `|c * (a1 * b1 + a2 * b2) * g| ≤ M1 * B1 + M2 * B2`. The proof bounds the left side by
`(|a1| * |g|) * |b1| + (|a2| * |g|) * |b2|`. -/
theorem abs_mul_mul_add_mul_mul_le {c a1 b1 a2 b2 g M1 M2 B1 B2 : ℝ} (hc : |c| ≤ 1)
    (h1 : |a1| * |g| ≤ M1)
    (h2 : |a2| * |g| ≤ M2) (hb1 : |b1| ≤ B1) (hb2 : |b2| ≤ B2) :
    |c * (a1 * b1 + a2 * b2) * g| ≤ M1 * B1 + M2 * B2 := by
  have hS : |a1 * b1 + a2 * b2| ≤ |a1| * |b1| + |a2| * |b2| :=
    (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
  have n1 : (0 : ℝ) ≤ |a1| * |g| := by positivity
  have n2 : (0 : ℝ) ≤ |a2| * |g| := by positivity
  calc |c * (a1 * b1 + a2 * b2) * g| = |c| * |a1 * b1 + a2 * b2| * |g| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (|a1| * |b1| + |a2| * |b2|) * |g| := by gcongr
    _ = (|a1| * |g|) * |b1| + (|a2| * |g|) * |b2| := by ring
    _ ≤ M1 * B1 + M2 * B2 :=
        add_le_add (mul_le_mul h1 hb1 (abs_nonneg _) (n1.trans h1))
          (mul_le_mul h2 hb2 (abs_nonneg _) (n2.trans h2))

/-- For real numbers, if `|x| ≤ B`, `|y| ≤ B` and `|z| ≤ B`, then `|x * y * z / 2| ≤ B ^ 3`. -/
theorem abs_mul_mul_div_two_le_pow {x y z B : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) (hz : |z| ≤ B) :
    |x * y * z / 2| ≤ B ^ 3 := by
  have hB : 0 ≤ B := (abs_nonneg x).trans hx
  have h1 : |x| * |y| ≤ B * B := mul_le_mul hx hy (abs_nonneg y) hB
  have h2 : |x| * |y| * |z| ≤ B * B * B := mul_le_mul h1 hz (abs_nonneg z) (mul_nonneg hB hB)
  rw [abs_div, abs_mul, abs_mul, abs_two]
  have h3 : 0 ≤ |x| * |y| * |z| := by positivity
  nlinarith

/-- For real numbers `c`, `p`, `q`, `|c * (p * q)| ≤ |c| * (p ^ 2 + q ^ 2)`. -/
theorem abs_mul_mul_le_mul_add_sq {c p q : ℝ} : |c * (p * q)| ≤ |c| * (p ^ 2 + q ^ 2) := by
  rw [abs_mul, abs_mul]
  have h1 : |p| * |q| ≤ p ^ 2 + q ^ 2 := by
    nlinarith [sq_nonneg (|p| - |q|), sq_abs p, sq_abs q, abs_nonneg p, abs_nonneg q]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

/-- For real numbers with `0 ≤ a`, `a ≤ A`, `0 ≤ x`, `x ≤ X`, `0 ≤ e` and `e ≤ 1`,
`|a * x * e| ≤ A * X`. -/
theorem abs_mul_mul_le_of_le_one {a A x X e : ℝ} (ha : 0 ≤ a) (hA : a ≤ A) (hx : 0 ≤ x) (hX : x ≤ X)
    (he : 0 ≤ e)
    (he1 : e ≤ 1) : |a * x * e| ≤ A * X := by
  rw [abs_of_nonneg (by positivity)]
  have h1 : a * x ≤ A * X := mul_le_mul hA hX hx (ha.trans hA)
  have h2 : a * x * e ≤ a * x := by nlinarith [mul_nonneg ha hx]
  linarith

/-- For real numbers with `|a| ≤ α`, `|b| ≤ β`, `|c| ≤ γ` and `|d| ≤ δ`,
`|a * b * c * d| ≤ α * β * γ * δ`. -/
theorem abs_mul_mul_mul_le_of_le {a b c d α β γ δ : ℝ} (ha : |a| ≤ α) (hb : |b| ≤ β) (hc : |c| ≤ γ)
    (hd : |d| ≤ δ) :
    |a * b * c * d| ≤ α * β * γ * δ :=
  abs_mul_le_of_le (abs_mul_mul_le_of_le ha hb hc) hd

/-- For real numbers with `0 ≤ a`, `0 ≤ b'`, `|a' - a| ≤ d`, `|b' - b| ≤ e` and `0 < t`,
`|a' * b' - a * b| ≤ (1 + 1 / t) * (d ^ 2 + e ^ 2) + t * (a ^ 2 + b ^ 2)`. The proof writes
`a' * b' - a * b = (a' - a) * b' + a * (b' - b)`, uses `b' ≤ b + e`, and bounds the products
`d * b`, `a * e` and `d * e` by squares, with the weight `t` for the first two. -/
theorem abs_mul_sub_mul_le_add_sq {a b a' b' d e t : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b')
    (hd : |a' - a| ≤ d) (he : |b' - b| ≤ e) (ht : 0 < t) :
    |a' * b' - a * b| ≤ (1 + 1 / t) * (d ^ 2 + e ^ 2) + t * (a ^ 2 + b ^ 2) := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hbb : b' ≤ b + e := by linarith [le_abs_self (b' - b)]
  have s1 : |a' * b' - a * b| ≤ d * b' + a * e := by
    have eq : a' * b' - a * b = (a' - a) * b' + a * (b' - b) := by ring
    rw [eq]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hb']
      exact mul_le_mul_of_nonneg_right hd hb'
    · rw [abs_mul, abs_of_nonneg ha]
      exact mul_le_mul_of_nonneg_left he ha
  have s2 : d * b' ≤ d * b + d * e := by nlinarith
  have h1 : d * b ≤ d ^ 2 / t + t * b ^ 2 := by
    have : d * b * t ≤ d ^ 2 + t * b ^ 2 * t := by nlinarith [sq_nonneg (d - t * b)]
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    linarith
  have h2 : a * e ≤ e ^ 2 / t + t * a ^ 2 := by
    have : a * e * t ≤ e ^ 2 + t * a ^ 2 * t := by nlinarith [sq_nonneg (e - t * a)]
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    linarith
  have h3 : d * e ≤ d ^ 2 + e ^ 2 := by nlinarith [sq_nonneg (d - e)]
  have e5 : (1 + 1 / t) * (d ^ 2 + e ^ 2) = d ^ 2 + e ^ 2 + (d ^ 2 / t + e ^ 2 / t) := by ring
  have h4 : 0 ≤ d ^ 2 / t := by positivity
  have h5 : 0 ≤ e ^ 2 / t := by positivity
  rw [e5]
  nlinarith

/-- For real numbers, if `0 ≤ x` and `x ≤ M` then `|-x| ≤ M`. -/
theorem abs_neg_le_of_nonneg_of_le {x M : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ M) : |-x| ≤ M := by
  rw [abs_neg, abs_of_nonneg h0]
  exact h1

/-- For a real `a` in `[0, 1]` and a natural number `d`, `|(1 - a) ^ d| ≤ 1`. -/
theorem abs_one_sub_pow_le_one (d : ℕ) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) : |(1 - a) ^ d| ≤ 1 :=
    by
  rw [abs_of_nonneg (pow_nonneg (by linarith [ha.2]) _)]
  exact pow_le_one₀ (by linarith [ha.2]) (by linarith [ha.1])

/-- For reals `a`, `b` in `[0, 1]` and a natural number `d`,
`|(1 - a) ^ d - (1 - b) ^ d| ≤ d * |a - b|`. The proof uses
`|x ^ d - y ^ d| ≤ |x - y| * d * max |x| |y| ^ (d - 1)` with `x = 1 - a` and `y = 1 - b`, which both
have absolute value at most `1`. -/
theorem abs_one_sub_pow_sub_pow_le (d : ℕ) {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |(1 - a) ^ d - (1 - b) ^ d| ≤ d * |a - b| := by
  have h := abs_pow_sub_pow_le (a := 1 - a) (b := 1 - b) (n := d)
  have hm : max |1 - a| |1 - b| ^ (d - 1) ≤ 1 := by
    apply pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
    apply max_le
    · rw [abs_of_nonneg (by linarith [ha.2])]
      linarith [ha.1]
    · rw [abs_of_nonneg (by linarith [hb.2])]
      linarith [hb.1]
  rw [show (1 - a) - (1 - b) = -(a - b) by ring, abs_neg] at h
  calc _ ≤ |a - b| * d * max |1 - a| |1 - b| ^ (d - 1) := h
    _ ≤ |a - b| * d * 1 := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = d * |a - b| := by ring

/-- For a natural number `k`, a Boolean `ws` and real `x` with `|x| ≤ 1`:
`|(1 - x ^ 2) ^ k * (if ws then √(1 - x ^ 2) else 1)| ≤ 1`. The proof uses that `(1 - x ^ 2) ^ k`
and `√(1 - x ^ 2)` both lie between `0` and `1`. -/
theorem abs_pow_mul_ite_sqrt_le_one (k : ℕ) (ws : Bool) {x : ℝ} (hx : |x| ≤ 1) :
    |(1 - x ^ 2) ^ k * (if ws then Real.sqrt (1 - x ^ 2) else 1)| ≤ 1 := by
  have hu0 : 0 ≤ 1 - x ^ 2 := by nlinarith [abs_le.1 hx, sq_abs x, abs_nonneg x]
  have hu1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hp0 : 0 ≤ (1 - x ^ 2) ^ k := pow_nonneg hu0 _
  have hp1 : (1 - x ^ 2) ^ k ≤ 1 := pow_le_one₀ hu0 hu1
  cases ws
  · simp only [Bool.false_eq_true, ite_false, mul_one]
    rw [abs_of_nonneg hp0]
    exact hp1
  · simp only [ite_true]
    rw [abs_of_nonneg (mul_nonneg hp0 (Real.sqrt_nonneg _))]
    exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) hp1).trans (Real.sqrt_le_one.2 hu1)

/-- For real `u`, `v` with `|u| ≤ 1` and `|v| ≤ 1` and a natural number `n`,
`|u ^ n - v ^ n| ≤ n * |u - v|`. -/
theorem abs_pow_sub_pow_le_mul_abs {u v : ℝ} (n : ℕ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    |u ^ n - v ^ n| ≤ n * |u - v| := by
  have h := abs_pow_sub_pow_le u v n
  have hm : max |u| |v| ^ (n - 1) ≤ 1 := pow_le_one₀ (le_max_of_le_left (abs_nonneg u))
      (max_le hu hv)
  calc |u ^ n - v ^ n| ≤ |u - v| * n * max |u| |v| ^ (n - 1) := h
    _ ≤ |u - v| * n * 1 := by gcongr
    _ = n * |u - v| := by ring

/-- Let `X = iA - iZ` with `|iA| ≤ √a * √bA`, `|iZ| ≤ √h * √bZ`, `√bA ≤ ρ * cn` and `√bZ ≤ ε`, and
let `E = h + w₀ * a` with `0 < w₀` and `a`, `h`, `ε`, `ρ`, `cn` nonnegative. Then
`|X| ≤ (ε + cn * ρ / √w₀) * √E`. The proof uses the triangle inequality with `√a ≤ √E / √w₀` and
`√h ≤ √E`. -/
theorem abs_sub_le_mul_sqrt_add_mul {X iA iZ a h bA bZ E w₀ ε ρ cn : ℝ} (hX : X = iA - iZ)
    (hA1 : |iA| ≤ Real.sqrt a * Real.sqrt bA) (hZ1 : |iZ| ≤ Real.sqrt h * Real.sqrt bZ)
    (hsA : Real.sqrt bA ≤ ρ * cn) (hsZ : Real.sqrt bZ ≤ ε) (hE : E = h + w₀ * a) (hw : 0 < w₀)
    (ha0 : 0 ≤ a) (hh0 : 0 ≤ h) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hcn0 : 0 ≤ cn) :
    |X| ≤ (ε + cn * ρ / Real.sqrt w₀) * Real.sqrt E := by
  have hsw := Real.sqrt_pos.2 hw
  have hsa : Real.sqrt a ≤ Real.sqrt E / Real.sqrt w₀ := by
    rw [le_div_iff₀ hsw, ← Real.sqrt_mul ha0]
    exact Real.sqrt_le_sqrt (by rw [hE]; nlinarith)
  have hsh : Real.sqrt h ≤ Real.sqrt E := Real.sqrt_le_sqrt (by
    rw [hE]; nlinarith [mul_nonneg hw.le ha0])
  rw [hX]
  calc |iA - iZ| ≤ |iA| + |iZ| := abs_sub _ _
    _ ≤ Real.sqrt a * (ρ * cn) + Real.sqrt h * ε :=
        add_le_add (hA1.trans (mul_le_mul_of_nonneg_left hsA (Real.sqrt_nonneg _)))
          (hZ1.trans (mul_le_mul_of_nonneg_left hsZ (Real.sqrt_nonneg _)))
    _ ≤ Real.sqrt E / Real.sqrt w₀ * (ρ * cn) + Real.sqrt E * ε :=
        add_le_add (mul_le_mul_of_nonneg_right hsa (by positivity))
          (mul_le_mul_of_nonneg_right hsh (by positivity))
    _ = (ε + cn * ρ / Real.sqrt w₀) * Real.sqrt E := by ring

/-- If `x` lies in the open interval `Set.Ioo a b` and `a < s < b`, then `|x - s| ≤ b - a`. -/
theorem abs_sub_le_sub_of_mem_Ioo {a b x s : ℝ} (hx : x ∈ Ioo a b) (hs : a < s) (hs' : s < b) :
    |x - s| ≤ b - a := by
  obtain ⟨h1, h2⟩ := hx
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- For real numbers `P > 0` and `|a| ≤ R` and a pair of integers `ι : ℤ × ℤ`,
`|2 * Real.pi * ι.1 / P + ι.2 * a| ≤ (2 * Real.pi / P + R) * (ι.1 ^ 2 + ι.2 ^ 2)`, with the integers
cast to `ℝ`. The proof uses the triangle inequality and `|n| ≤ n ^ 2` for an integer `n`. -/
theorem abs_two_pi_div_add_mul_le {P a R : ℝ} (hP0 : 0 < P) (ha : |a| ≤ R) (ι : ℤ × ℤ) :
    |2 * Real.pi * ι.1 / P + ι.2 * a| ≤ (2 * Real.pi / P + R) * ((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) :=
        by
  have hpi : 0 < 2 * Real.pi / P := by positivity
  have hR0 : 0 ≤ R := (abs_nonneg _).trans ha
  have e1 : |2 * Real.pi * (ι.1 : ℝ) / P| = 2 * Real.pi / P * |(ι.1 : ℝ)| := by
    rw [show 2 * Real.pi * (ι.1 : ℝ) / P = 2 * Real.pi / P * ι.1 by ring, abs_mul, abs_of_pos hpi]
  have e2 : |(ι.2 : ℝ) * a| ≤ |(ι.2 : ℝ)| * R := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  have h1 := abs_intCast_le_intCast_sq ι.1
  have h2 := abs_intCast_le_intCast_sq ι.2
  have s1 := sq_nonneg (ι.1 : ℝ)
  have s2 := sq_nonneg (ι.2 : ℝ)
  calc _ ≤ |2 * Real.pi * (ι.1 : ℝ) / P| + |(ι.2 : ℝ) * a| := abs_add_le _ _
    _ ≤ 2 * Real.pi / P * (ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2 * R := by
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_left h1 hpi.le, mul_le_mul_of_nonneg_right h2 hR0]
    _ ≤ _ := by nlinarith [mul_nonneg hpi.le s2, mul_nonneg hR0 s1]

/-- If `|a| ≤ A`, then both entries of the vector `![a / 2, -(a / 2)]` have absolute value at most
`A / 2`: `|![a / 2, -(a / 2)] i| ≤ A / 2` for `i : Fin 2`. -/
theorem abs_vecCons_half_neg_half_le {a A : ℝ} (ha : |a| ≤ A) (i : Fin 2) :
    |(![a / 2, -(a / 2)] : Fin 2 → ℝ) i| ≤ A / 2 := by
  fin_cases i
  · simp [abs_div]
    linarith
  · simp [abs_div]
    linarith

/-- Let `a`, `b`, `c`, `r`, `K`, `wt` be nonnegative real numbers with `wt ≤ B` and `r * wt ≤ B`. If
`s * a ≤ K * (2 * b + 1 / 2 * r * c)` and `t * a ≤ 2 * a + 2 * r * c`, then
`(s + t) * wt * a ≤ B * (2 * K + 4) * (b + c + a / (1 + r))`. The proof multiplies both hypotheses
by `wt` and uses `wt * a ≤ 2 * B * (a / (1 + r))`, which follows from `wt * (1 + r) ≤ 2 * B`. -/
theorem add_mul_mul_le_of_mul_le {a b c wt B K s t r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hr : 0 ≤ r)
    (hK : 0 ≤ K) (hw0 : 0 ≤ wt) (hwB : wt ≤ B) (hwr : r * wt ≤ B)
    (h1 : s * a ≤ K * (2 * b + 1 / 2 * r * c)) (h2 : t * a ≤ 2 * a + 2 * r * c) :
    (s + t) * wt * a ≤ B * (2 * K + 4) * (b + c + a / (1 + r)) := by
  have hB0 : 0 ≤ B := hw0.trans hwB
  have hr1 : 0 < 1 + r := by linarith
  set d := a / (1 + r) with hd
  have hd0 : 0 ≤ d := div_nonneg ha hr1.le
  have had : a = (1 + r) * d := by rw [hd]; field_simp
  have e1 : s * a * wt ≤ K * (2 * b + 1 / 2 * r * c) * wt := mul_le_mul_of_nonneg_right h1 hw0
  have e2 : t * a * wt ≤ (2 * a + 2 * r * c) * wt := mul_le_mul_of_nonneg_right h2 hw0
  have e3 : wt * a ≤ 2 * B * d := by
    rw [had]
    have : wt * (1 + r) ≤ 2 * B := by linarith
    nlinarith
  have e4 : K * (2 * b + 1 / 2 * r * c) * wt ≤ 2 * K * B * b + 1 / 2 * K * B * c := by
    have q1 : K * b * wt ≤ K * b * B := mul_le_mul_of_nonneg_left hwB (mul_nonneg hK hb)
    have q2 : K * c * (r * wt) ≤ K * c * B := mul_le_mul_of_nonneg_left hwr (mul_nonneg hK hc)
    nlinarith
  have e5 : 2 * r * c * wt ≤ 2 * B * c := by nlinarith
  have f1 : 0 ≤ K * B * c := mul_nonneg (mul_nonneg hK hB0) hc
  have f2 : 0 ≤ K * B * d := mul_nonneg (mul_nonneg hK hB0) hd0
  have f3 : 0 ≤ B * b := mul_nonneg hB0 hb
  have f4 : 0 ≤ B * c := mul_nonneg hB0 hc
  have f5 : 0 ≤ B * d := mul_nonneg hB0 hd0
  nlinarith

/-- Let `0 < c`, `0 ≤ vh`, `0 ≤ ch` and `vh / c + ch / √c ≤ gl` be reals. Then
`0 ≤ vh + ch * √c / 2`, `vh + ch * √c / 2 ≤ (gl - ch / (2 * √c)) * c` and `0 ≤ gl - ch / (2 * √c)`.
The proof writes `c = s * s` with `s = √c > 0` and multiplies the hypothesis by `c`. -/
theorem add_mul_sqrt_half_le_sub_mul {c vh ch gl : ℝ} (hc : 0 < c) (hvh : 0 ≤ vh) (hch : 0 ≤ ch)
    (ht : vh / c + ch / Real.sqrt c ≤ gl) :
    0 ≤ vh + ch * Real.sqrt c / 2 ∧ vh + ch * Real.sqrt c / 2 ≤ (gl - ch / (2 * Real.sqrt c)) * c ∧
      0 ≤ gl - ch / (2 * Real.sqrt c) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ c = s * s := ⟨Real.sqrt c, Real.sqrt_pos.2 hc,
      (Real.mul_self_sqrt hc.le).symm⟩
  rw [Real.sqrt_mul_self hs.le] at ht ⊢
  have h1 : 0 ≤ vh + ch * s / 2 := by positivity
  have e1 : (vh / (s * s) + ch / s) * (s * s) = vh + ch * s := by
    field_simp
  have e2 : (gl - ch / (2 * s)) * (s * s) = gl * (s * s) - ch * s / 2 := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_right ht hc.le
  rw [e1] at h3
  have h2 : vh + ch * s / 2 ≤ (gl - ch / (2 * s)) * (s * s) := by
    rw [e2]
    linarith
  refine ⟨h1, h2, ?_⟩
  by_contra hneg
  have : (gl - ch / (2 * s)) * (s * s) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hc
  linarith

/-- For `0 < L` and `0 ≤ r`, `L / (r + L) ≤ max L 1 / (1 + r)`. -/
theorem div_add_le_max_div_one_add (L r : ℝ) (hL : 0 < L) (hr : 0 ≤ r) :
    L / (r + L) ≤ max L 1 / (1 + r) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rcases le_total L 1 with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

/-- Let `edge < 1` and `-L < r`. If `r ≤ L * edge / (1 - edge)`, then `r / (r + L) ≤ edge`. -/
theorem div_add_le_of_le_mul_div (L edge r : ℝ) (he : edge < 1) (hr : -L < r)
    (hR : r ≤ L * edge / (1 - edge)) : r / (r + L) ≤ edge := by
  have h1 : 0 < 1 - edge := by linarith
  have h2 : 0 < r + L := by linarith
  rw [div_le_iff₀ h2]
  rw [le_div_iff₀ h1] at hR
  nlinarith

/-- For reals `0 ≤ c`, `1 ≤ s` and `0 ≤ L` and natural numbers `m ≤ k`,
`c / (s + L) ^ k ≤ c / s ^ m`. -/
theorem div_add_pow_le {c s L : ℝ} (hc : 0 ≤ c) (hs : 1 ≤ s) (hL : 0 ≤ L) {k m : ℕ} (hkm : m ≤ k) :
    c / (s + L) ^ k ≤ c / s ^ m :=
  div_le_div_of_nonneg_left hc (by positivity)
    ((pow_le_pow_right₀ hs hkm).trans (pow_le_pow_left₀ (by linarith) (by linarith) k))

/-- For real numbers with `0 < τ ≤ ρ` and `0 ≤ A`, `A / (8 * ρ ^ 3) ≤ A / (8 * τ) / ρ ^ 2`. -/
theorem div_mul_cube_le_div_div_sq {τ ρ A : ℝ} (hτ : 0 < τ) (hρ : τ ≤ ρ) (hA : 0 ≤ A) :
    A / (8 * ρ ^ 3) ≤ A / (8 * τ) / ρ ^ 2 := by
  have hρ0 : 0 < ρ := hτ.trans_le hρ
  rw [div_div]
  apply div_le_div_of_nonneg_left hA (by positivity)
  have : τ * ρ ^ 2 ≤ ρ * ρ ^ 2 := mul_le_mul_of_nonneg_right hρ (sq_nonneg _)
  nlinarith

/-- Let `r > 0`, `ρ ≥ 0`, `s ≥ 0` and `K * φ ≥ 0`. If `s ^ 2 ≤ K ^ 2 * φ ^ 2 * Q`, `Q ≤ Qm` and
`4 * ρ ^ 2 * Qm ≤ r ^ 2`, then `2 * ρ / r * s ≤ K * φ`. The proof shows
`(2 * ρ * s) ^ 2 ≤ (K * φ * r) ^ 2` and compares the bases, which are nonnegative. -/
theorem div_mul_le_mul_of_sq_le {s ρ r K φ Q Qm : ℝ} (hr : 0 < r) (hρ : 0 ≤ ρ) (hs0 : 0 ≤ s)
    (hKφ : 0 ≤ K * φ) (hs : s ^ 2 ≤ K ^ 2 * φ ^ 2 * Q) (hQ : Q ≤ Qm)
    (hsmall : 4 * ρ ^ 2 * Qm ≤ r ^ 2) : 2 * ρ / r * s ≤ K * φ := by
  have hA : 0 ≤ K ^ 2 * φ ^ 2 := by positivity
  have h1 : (2 * ρ * s) ^ 2 ≤ (K * φ * r) ^ 2 := by
    calc (2 * ρ * s) ^ 2 = 4 * ρ ^ 2 * s ^ 2 := by ring
      _ ≤ 4 * ρ ^ 2 * (K ^ 2 * φ ^ 2 * Qm) := by
          refine mul_le_mul_of_nonneg_left (hs.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hQ hA
      _ = K ^ 2 * φ ^ 2 * (4 * ρ ^ 2 * Qm) := by ring
      _ ≤ K ^ 2 * φ ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hsmall hA
      _ = (K * φ * r) ^ 2 := by ring
  have h2 : 2 * ρ * s ≤ K * φ * r :=
    (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hKφ hr.le) two_ne_zero).1 h1
  rw [div_mul_eq_mul_div, div_le_iff₀ hr]
  exact h2

/-- A weighted Young inequality: for reals with `0 ≤ ch`, `0 < ρ` and `0 < s`,
`ch / ρ * x1 * x0 ≤ ch / (2 * s) * x1 ^ 2 + ch * s / 2 * (x0 ^ 2 / ρ ^ 2)`. -/
theorem div_mul_mul_le_mul_sq_add {ch ρ s x1 x0 : ℝ} (hch : 0 ≤ ch) (hρ : 0 < ρ) (hs : 0 < s) :
    ch / ρ * x1 * x0 ≤ ch / (2 * s) * x1 ^ 2 + ch * s / 2 * (x0 ^ 2 / ρ ^ 2) := by
  have e : ch / (2 * s) * x1 ^ 2 + ch * s / 2 * (x0 ^ 2 / ρ ^ 2) - ch / ρ * x1 * x0
      = ch / (2 * s) * (x1 - s * x0 / ρ) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ ch / (2 * s) * (x1 - s * x0 / ρ) ^ 2 := by positivity
  linarith

/-- For `0 ≤ M`, `0 ≤ r` and a natural number `n ≤ 4`, `M / (1 + r) ^ 4 ≤ M / (1 + r) ^ n`. -/
theorem div_one_add_pow_four_le (M r : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r) {n : ℕ} (hn : n ≤ 4) :
    M / (1 + r) ^ 4 ≤ M / (1 + r) ^ n :=
  div_le_div_of_nonneg_left hM (by positivity) (pow_le_pow_right₀ (by linarith) hn)

/-- For `0 ≤ K`, `0 ≤ r` and a natural number `n`, `K / (1 + r) ^ (n + 1) * r ≤ K / (1 + r) ^ n`. -/
theorem div_one_add_pow_succ_mul_le (K r : ℝ) (n : ℕ) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    K / (1 + r) ^ (n + 1) * r ≤ K / (1 + r) ^ n := by
  have h1 : 0 < 1 + r := by linarith
  rw [pow_succ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : K * r * (1 + r) ^ n ≤ K * ((1 + r) ^ n * (1 + r)) := by
    rw [mul_comm ((1 + r) ^ n) (1 + r), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK) (by positivity)
  linarith

/-- Let `k ≤ 3` be a natural number, `1 ≤ r` and `0 ≤ M`. If `8 * M ≤ N`, then
`M / r ^ k ≤ N * ((1 + r)⁻¹) ^ k`. The proof uses `(1 + r) ^ k ≤ (2 * r) ^ k ≤ 8 * r ^ k`. -/
theorem div_pow_le_mul_inv_pow {M N r : ℝ} {k : ℕ} (hk : k ≤ 3) (hr : 1 ≤ r) (hM : 0 ≤ M)
    (hN : 8 * M ≤ N) :
    M / r ^ k ≤ N * ((1 + r)⁻¹) ^ k := by
  have hr0 : 0 < r := by linarith
  rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (2 : ℝ) ^ k ≤ 8 := by
    calc (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
      _ = 8 := by norm_num
  have h1 : (1 + r) ^ k ≤ 8 * r ^ k :=
    calc (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * r ^ k := mul_pow _ _ _
      _ ≤ 8 * r ^ k := mul_le_mul_of_nonneg_right h2 (by positivity)
  calc M * (1 + r) ^ k ≤ M * (8 * r ^ k) := mul_le_mul_of_nonneg_left h1 hM
    _ = 8 * M * r ^ k := by ring
    _ ≤ N * r ^ k := mul_le_mul_of_nonneg_right hN (by positivity)

/-- For reals `0 < r`, `r / 2 ≤ s` and `0 ≤ C` and a natural number `k`,
`C / s ^ k ≤ 2 ^ k * C / r ^ k`. -/
theorem div_pow_le_of_half_le {r s C : ℝ} (k : ℕ) (hr : 0 < r) (hs : r / 2 ≤ s) (hC : 0 ≤ C) :
    C / s ^ k ≤ 2 ^ k * C / r ^ k := by
  have h1 : (r / 2) ^ k ≤ s ^ k := pow_le_pow_left₀ (by positivity) hs k
  calc C / s ^ k ≤ C / (r / 2) ^ k := div_le_div_of_nonneg_left hC (by positivity) h1
    _ = 2 ^ k * C / r ^ k := by rw [div_pow]; field_simp

/-- For reals with `0 < a` and `a ≤ b`, `b / a ^ 2 ≤ (1 + b / a) ^ 2 / a`. -/
theorem div_sq_le_add_div_sq_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b / a ^ 2 ≤ (1 + b / a) ^ 2 / a := by
  have h0 : 0 ≤ b / a := div_nonneg (ha.le.trans hab) ha.le
  rw [sq, ← div_div]
  exact div_le_div_of_nonneg_right (by nlinarith) ha.le

/-- For `M ≥ 0` and `ε > 0`, `ε / (2 * (M + 1)) * M < ε`. The left side equals
`ε / 2 - ε / (2 * (M + 1))`. -/
theorem div_two_mul_add_one_mul_lt {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ε / (2 * (M + 1)) * M < ε := by
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have e : ε / (2 * (M + 1)) * (M + 1) = ε / 2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right ε 2 hM1.ne']
  have hη : 0 < ε / (2 * (M + 1)) := div_pos hε (mul_pos two_pos hM1)
  have e2 : ε / (2 * (M + 1)) * M = ε / 2 - ε / (2 * (M + 1)) := by
    rw [← e]
    ring
  rw [e2]
  linarith

/-- Two reals `x` and `y` are equal if for every `ε > 0` there are reals `a` and `b` with `a = b`
and `|x - a| + |y - b| < ε`. By the triangle inequality this gives `|x - y| < ε` for every `ε > 0`.
-/
theorem eq_of_forall_exists_abs_sub_lt {x y : ℝ}
    (hc : ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ, a = b ∧ |x - a| + |y - b| < ε) : x = y := by
  refine eq_of_abs_sub_le_all ?_
  intro ε hε
  obtain ⟨a, b, hab, hlt⟩ := hc ε hε
  subst hab
  have h1 : |x - y| ≤ |x - a| + |y - a| := by
    calc |x - y| = |(x - a) - (y - a)| := by ring_nf
      _ ≤ |x - a| + |y - a| := abs_sub _ _
  linarith

/-- The real hypotheses `w * B ≤ A`, `A = E`, `E + K ≤ (2 * s) ^ 2`, `0 ≤ K` and `4 * s ^ 2 < B * w`
are contradictory. The first four give `w * B ≤ 4 * s ^ 2`, which contradicts the last one. -/
theorem false_of_mul_le_of_lt_mul {w B A E K s : ℝ} (hlow : w * B ≤ A) (he : A = E)
    (h2 : E + K ≤ (2 * s) ^ 2) (hK : 0 ≤ K) (h5 : 4 * s ^ 2 < B * w) : False := by
  nlinarith

/-- For real `p`, `q`, `r`, `s`, `k`,
`|q + k * r| + |k * s| + |s - k * p| + |-(k * q)| ≤ (1 + |k|) * (|p| + |q| + |r| + |s|)`. -/
theorem four_abs_le_one_add_abs_mul (p q r s k : ℝ) :
    |q + k * r| + |k * s| + |s - k * p| + |-(k * q)| ≤ (1 + |k|) * (|p| + |q| + |r| + |s|) := by
  have h1 : |q + k * r| ≤ |q| + |k| * |r| := (abs_add_le _ _).trans (by rw [abs_mul])
  have h2 : |s - k * p| ≤ |s| + |k| * |p| := (abs_sub _ _).trans (by rw [abs_mul])
  rw [abs_neg, abs_mul, abs_mul]
  nlinarith [abs_nonneg p, abs_nonneg q, abs_nonneg r, abs_nonneg s, abs_nonneg k]

/-- For real numbers with `w > 0` and `L = (ρ - h) / (4 * π)`,
`4 * π * (2 * (μ * (L - y))) + 4 * π * (2 * (μ * y)) + 2 * (μ * h) - 4 * π * (μ ^ 2 / (4 * π * w)) ≤
w * ρ ^ 2`. The left side equals `2 * μ * ρ - μ ^ 2 / w`, and `w * ρ ^ 2` minus this is `(w * ρ - μ)
^ 2 / w ≥ 0`. -/
theorem four_pi_mul_sub_sq_div_le {w ρ μ h y L : ℝ} (hw : 0 < w)
    (hL : L = (ρ - h) / (4 * Real.pi)) :
    4 * Real.pi * (2 * (μ * (L - y))) + 4 * Real.pi * (2 * (μ * y)) + 2 * (μ * h)
      - 4 * Real.pi * (μ ^ 2 / (4 * Real.pi * w)) ≤ w * ρ ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h4 : 4 * Real.pi * L = ρ - h := by rw [hL]; field_simp
  have e1 : 4 * Real.pi * (μ ^ 2 / (4 * Real.pi * w)) = μ ^ 2 / w := by field_simp
  have e2 : w * ρ ^ 2 - (2 * μ * ρ - μ ^ 2 / w) = (w * ρ - μ) ^ 2 / w := by field_simp; ring
  have e3 : 0 ≤ (w * ρ - μ) ^ 2 / w := div_nonneg (sq_nonneg _) hw.le
  have e4 : 4 * Real.pi * (2 * (μ * (L - y))) + 4 * Real.pi * (2 * (μ * y)) = 2 * μ *
      (4 * Real.pi * L) := by
    ring
  rw [e1, e4, h4]
  linarith

/-- Let `g`, `x`, `b` be nonnegative reals with `x ≤ C` and `g ^ 2 ≤ f`. Then
`g * x * b ≤ C * (f + b ^ 2)`. -/
theorem frozen_first_pointwise (g x b f C : ℝ) (hg : 0 ≤ g) (hx : 0 ≤ x) (hb : 0 ≤ b)
    (hxC : x ≤ C) (hgf : g ^ 2 ≤ f) : g * x * b ≤ C * (f + b ^ 2) := by
  have hC : 0 ≤ C := hx.trans hxC
  have h1 : g * x * b ≤ g * C * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxC hg) hb
  have h2 : g * b ≤ g ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (g - b), mul_nonneg hg hb]
  calc g * x * b ≤ g * C * b := h1
    _ = C * (g * b) := by ring
    _ ≤ C * (g ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_left h2 hC
    _ ≤ C * (f + b ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hC

/-- Let `0 < e`, `e ≤ eM`, `0 ≤ mu`, `mu * u ^ 2 ≤ 4 * B1`, `1 ≤ u` and `a ^ 2 / u ^ 2 ≤ E` be real
numbers. Then `(1 / 2) * e * mu ^ 2 * a ^ 2 ≤ 8 * eM * B1 ^ 2 * E`. The proof shows
`mu ^ 2 * u ^ 2 ≤ 16 * B1 ^ 2` from `u ^ 2 ≤ u ^ 4` and writes
`mu ^ 2 * a ^ 2 = (mu ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2)`. -/
theorem half_mul_sq_mul_sq_le {e eM mu u a B1 E : ℝ} (he : 0 < e) (heM : e ≤ eM) (hmu0 : 0 ≤ mu)
    (hmu : mu * u ^ 2 ≤ 4 * B1) (hu1 : 1 ≤ u) (hEa : a ^ 2 / u ^ 2 ≤ E) :
    (1 / 2) * e * mu ^ 2 * a ^ 2 ≤ 8 * eM * B1 ^ 2 * E := by
  have hu0 : 0 < u := by linarith
  have hu' : u ≠ 0 := hu0.ne'
  have heM0 : 0 ≤ eM := he.le.trans heM
  have h1 : (mu * u ^ 2) ^ 2 ≤ (4 * B1) ^ 2 := pow_le_pow_left₀ (by positivity) hmu 2
  have h2 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hm2 : mu ^ 2 * u ^ 2 ≤ 16 * B1 ^ 2 := by
    nlinarith only [h1, mul_le_mul_of_nonneg_left h2 (sq_nonneg mu)]
  have e1 : (1 / 2) * e * mu ^ 2 * a ^ 2 = (1 / 2) * e * (mu ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2) := by
    field_simp
  have hc0 : 0 ≤ (1 / 2) * eM * (16 * B1 ^ 2) := mul_nonneg (mul_nonneg (by
    norm_num) heM0) (by positivity)
  have h3 : (1 / 2) * e * (mu ^ 2 * u ^ 2) ≤ (1 / 2) * eM * (16 * B1 ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left heM (by norm_num)) hm2 (by positivity)
      (mul_nonneg (by norm_num) heM0)
  rw [e1]
  calc (1 / 2) * e * (mu ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2) ≤ (1 / 2) * eM * (16 * B1 ^ 2) *
           (a ^ 2 / u ^ 2) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ ≤ (1 / 2) * eM * (16 * B1 ^ 2) * E := mul_le_mul_of_nonneg_left hEa hc0
    _ = 8 * eM * B1 ^ 2 * E := by ring

/-- For reals `0 < L` and `0 < r` and a natural number `n`, `((r + L)⁻¹) ^ n ≤ r⁻¹ ^ n`. -/
theorem inv_add_pow_le_inv_pow {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (n : ℕ) :
    ((r + L)⁻¹) ^ n ≤ r⁻¹ ^ n := by
  have : (r + L)⁻¹ ≤ r⁻¹ := inv_anti₀ hr (by linarith)
  exact pow_le_pow_left₀ (by positivity) this n

/-- For positive reals `a` and `b` with `b ^ 2 ≤ a ^ 2 * (1 + b ^ 2)`, `a⁻¹ ≤ b⁻¹ + 1`. The proof
first shows `b ≤ a * (1 + b)`. -/
theorem inv_le_inv_add_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ^ 2 ≤ a ^ 2 * (1 + b ^ 2)) :
    a⁻¹ ≤ b⁻¹ + 1 := by
  have hs : 0 < b + a * (1 + b) := by positivity
  have key : b ≤ a * (1 + b) := by
    nlinarith [mul_pos ha hb, mul_pos (mul_pos ha ha) hb]
  have e : b⁻¹ + 1 = (1 + b) / b := by
    rw [eq_div_iff hb.ne', add_mul, inv_mul_cancel₀ hb.ne', one_mul]
  rw [e, inv_eq_one_div, div_le_div_iff₀ ha hb]
  nlinarith

/-- For real numbers with `w ≥ 0`, if `a ≤ c * w` then `a ≤ |c| * w`. -/
theorem le_abs_mul_of_le_mul {a c w : ℝ} (hw : 0 ≤ w) (h : a ≤ c * w) : a ≤ |c| * w :=
  h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)

/-- For real numbers, if `U ^ 2 = A ^ 2 + B ^ 2` and `0 ≤ U`, then `A ≤ U` and `B ≤ U`. -/
theorem le_and_le_of_sq_eq_add {A B U : ℝ} (e : U ^ 2 = A ^ 2 + B ^ 2) (h2 : 0 ≤ U) :
    A ≤ U ∧ B ≤ U := by
  constructor
  · nlinarith [sq_nonneg (A - U)]
  · nlinarith [sq_nonneg (B - U)]

/-- For real numbers, if `B ^ 2 + (1 / 4) * A ^ 2 ≤ F ^ 2`, `U ^ 2 = A ^ 2 + B ^ 2` and `0 ≤ F`,
then `A ≤ 2 * F`, `B ≤ F` and `U ^ 2 ≤ 5 * F ^ 2`. -/
theorem le_and_sq_le_five_mul_sq {A B U F : ℝ} (hb : B ^ 2 + (1 / 4 : ℝ) * A ^ 2 ≤ F ^ 2)
    (e : U ^ 2 = A ^ 2 + B ^ 2) (h2 : 0 ≤ F) :
    A ≤ 2 * F ∧ B ≤ F ∧ U ^ 2 ≤ 5 * F ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (A - 2 * F)]
  · nlinarith [sq_nonneg (B - F)]
  · nlinarith

/-- Let `0 < L`, `t' < 1` and `0 < r`. If `L * t' / (1 - t') ≤ r`, then `t' ≤ r / (r + L)`. -/
theorem le_div_add_of_mul_div_le (L t' r : ℝ) (hL : 0 < L) (ht : t' < 1)
    (hr : L * t' / (1 - t') ≤ r)
    (hr0 : 0 < r) : t' ≤ r / (r + L) := by
  rw [le_div_iff₀ (by linarith)]
  rw [div_le_iff₀ (by linarith)] at hr
  nlinarith

/-- Let `k ≤ K` and `k ≤ N` be natural numbers, `0 ≤ M`, `1 ≤ R` and `0 ≤ r`. If `u ≤ C0` whenever
`r ≤ R`, and `u ≤ M / r ^ K` whenever `R ≤ r`, then
`u ≤ (|C0| * (1 + R) ^ N + 2 ^ N * M) / (1 + r) ^ k`. The proof uses `(1 + r) ^ k ≤ (1 + R) ^ N` in
the first case, and `r ^ k ≤ r ^ K` with `(1 + r) ^ k ≤ (2 * r) ^ k` in the second. -/
theorem le_div_pow_of_le_div_pow {C0 M R r u : ℝ} {k K N : ℕ} (hkK : k ≤ K) (hkN : k ≤ N)
    (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hr : 0 ≤ r) (hnear : r ≤ R → u ≤ C0) (hfar : R ≤ r → u ≤ M / r ^ K) :
    u ≤ (|C0| * (1 + R) ^ N + 2 ^ N * M) / (1 + r) ^ k := by
  have hpos : 0 < (1 + r) ^ k := by positivity
  have hA : 0 ≤ |C0| * (1 + R) ^ N := by
    have : 0 ≤ 1 + R := by linarith
    positivity
  have hB : 0 ≤ 2 ^ N * M := by positivity
  rw [le_div_iff₀ hpos]
  rcases le_total r R with h | h
  · have h1 : (1 + r) ^ k ≤ (1 + R) ^ N :=
      (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (pow_le_pow_right₀ (by linarith) hkN)
    have h2 : u ≤ |C0| := (hnear h).trans (le_abs_self C0)
    calc u * (1 + r) ^ k ≤ |C0| * (1 + r) ^ k := mul_le_mul_of_nonneg_right h2 hpos.le
      _ ≤ |C0| * (1 + R) ^ N := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |C0| * (1 + R) ^ N + 2 ^ N * M := le_add_of_nonneg_right hB
  · have hr1 : 1 ≤ r := hR.trans h
    have hr0 : 0 < r := by linarith
    have h2 : u ≤ M / r ^ k :=
      (hfar h).trans (div_le_div_of_nonneg_left hM (by positivity) (pow_le_pow_right₀ hr1 hkK))
    have h3 : (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    have h4 : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hkN
    calc u * (1 + r) ^ k ≤ M / r ^ k * (1 + r) ^ k := mul_le_mul_of_nonneg_right h2 hpos.le
      _ ≤ M / r ^ k * (2 * r) ^ k := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 ^ k * M := by
        rw [mul_pow]
        field_simp
      _ ≤ 2 ^ N * M := mul_le_mul_of_nonneg_right h4 hM
      _ ≤ |C0| * (1 + R) ^ N + 2 ^ N * M := le_add_of_nonneg_left hA

/-- Let `k ≤ m` be natural numbers, `1 ≤ Rf`, `0 ≤ Y`, `0 ≤ Cf` and
`|Bn| * (1 + Rf) ^ m + 2 ^ m * Cf ≤ K`. If `a ≤ Bn` whenever `Y ≤ Rf`, and `a ≤ Cf * Y⁻¹ ^ k`
whenever `Rf ≤ Y`, then `a ≤ K / (1 + Y) ^ k`. The proof uses `(1 + Y) ^ k ≤ (1 + Rf) ^ m` in the
first case and `((1 + Y) * Y⁻¹) ^ k ≤ 2 ^ m` in the second. -/
theorem le_div_pow_of_le_inv_pow {a Bn Cf Rf Y K : ℝ} {k m : ℕ} (hk : k ≤ m) (hRf : 1 ≤ Rf)
    (hY : 0 ≤ Y) (hCf : 0 ≤ Cf)
    (hK : |Bn| * (1 + Rf) ^ m + 2 ^ m * Cf ≤ K) (hn : Y ≤ Rf → a ≤ Bn)
        (hf : Rf ≤ Y → a ≤ Cf * Y⁻¹ ^ k) :
    a ≤ K / (1 + Y) ^ k := by
  rw [le_div_iff₀ (by positivity)]
  have hm0 : 0 ≤ 2 ^ m * Cf := by positivity
  have hn0 : 0 ≤ |Bn| * (1 + Rf) ^ m := by positivity
  rcases le_total Y Rf with h | h
  · have ha : a ≤ |Bn| := (hn h).trans (le_abs_self Bn)
    have p1 : (1 + Y) ^ k ≤ (1 + Rf) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    have p2 : (1 + Rf) ^ k ≤ (1 + Rf) ^ m := pow_le_pow_right₀ (by linarith) hk
    have p0 : 0 ≤ (1 + Y) ^ k := by positivity
    calc a * (1 + Y) ^ k ≤ |Bn| * (1 + Y) ^ k := mul_le_mul_of_nonneg_right ha p0
      _ ≤ |Bn| * (1 + Rf) ^ m := mul_le_mul_of_nonneg_left (p1.trans p2) (abs_nonneg _)
      _ ≤ K := by linarith
  · have hY1 : 1 ≤ Y := hRf.trans h
    have hYp : 0 < Y := by linarith
    have ha := hf h
    have p0 : 0 ≤ (1 + Y) ^ k := by positivity
    have e : Y⁻¹ ^ k * (1 + Y) ^ k = ((1 + Y) * Y⁻¹) ^ k := by rw [mul_pow]; ring
    have q : (1 + Y) * Y⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hYp]; linarith
    have q2 : ((1 + Y) * Y⁻¹) ^ k ≤ 2 ^ m :=
      (pow_le_pow_left₀ (by positivity) q k).trans (pow_le_pow_right₀ (by norm_num) hk)
    calc a * (1 + Y) ^ k ≤ Cf * Y⁻¹ ^ k * (1 + Y) ^ k := mul_le_mul_of_nonneg_right ha p0
      _ = Cf * ((1 + Y) * Y⁻¹) ^ k := by rw [mul_assoc, e]
      _ ≤ Cf * 2 ^ m := mul_le_mul_of_nonneg_left q2 hCf
      _ ≤ K := by linarith

/-- Young-type bound: for reals `y`, `w > 0` and `t > 0`, `y ≤ (t * (w * y ^ 2) + (t * w)⁻¹) / 2`.
This is `two_mul_mul_le_mul_sq_add` for `y` and `1` at `β = t * w`, divided by `2`. -/
theorem le_half_mul_sq_add_inv {y w t : ℝ} (hw : 0 < w) (ht : 0 < t) :
    y ≤ (t * (w * y ^ 2) + (t * w)⁻¹) / 2 := by
  have h := two_mul_mul_le_mul_sq_add y 1 (t * w) (mul_pos ht hw)
  rw [mul_one, one_pow, one_div, mul_assoc] at h
  linarith

/-- Combines a bound near the origin with a decay bound far away. Let `M`, `2 ≤ R`, `0 ≤ r`,
`0 ≤ u` be reals and `k ≤ 3` a natural number; if `u ≤ C0` whenever `r ≤ R`, and `u ≤ M / r ^ k`
whenever `R ≤ r`, then `u ≤ max (|C0| * (1 + R) ^ 3) (8 * M) / (1 + r) ^ k`. The proof uses
`(1 + r) ^ k ≤ (1 + R) ^ 3` when `r ≤ R` and `(1 + r) ^ k ≤ 8 * r ^ k` when `R < r`. -/
theorem le_max_div_one_add_pow {C0 M R r u : ℝ} (hR : 2 ≤ R) (hr : 0 ≤ r) (hu : 0 ≤ u)
    {k : ℕ}
    (hk : k ≤ 3) (hnear : r ≤ R → u ≤ C0) (hfar : R ≤ r → u ≤ M / r ^ k) :
    u ≤ max (|C0| * (1 + R) ^ 3) (8 * M) / (1 + r) ^ k := by
  rw [le_div_iff₀ (by positivity)]
  by_cases hrR : r ≤ R
  · have h1 : (1 + r) ^ k ≤ (1 + R) ^ 3 :=
      (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (pow_le_pow_right₀ (by linarith) hk)
    have h2 : u ≤ |C0| := (hnear hrR).trans (le_abs_self C0)
    exact (mul_le_mul h2 h1 (by positivity) (abs_nonneg _)).trans (le_max_left _ _)
  · have hRr : R ≤ r := le_of_lt (not_le.1 hrR)
    have hr0 : 0 < r := by linarith
    have h1 : (1 + r) ^ k ≤ 8 * r ^ k := by
      calc (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
        _ = 2 ^ k * r ^ k := by rw [mul_pow]
        _ ≤ 8 * r ^ k := by
          have : (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
          nlinarith [pow_pos hr0 k]
    have h2 := hfar hRr
    calc u * (1 + r) ^ k ≤ M / r ^ k * (8 * r ^ k) := mul_le_mul h2 h1 (by
           positivity) ((hu).trans h2)
      _ = 8 * M := by field_simp
      _ ≤ max (|C0| * (1 + R) ^ 3) (8 * M) := le_max_right _ _

/-- Let `k ≤ 3` be a natural number, `0 ≤ r ≤ R` and `0 ≤ S`. If `c ≤ S` and `S * (1 + R) ^ 3 ≤ N`,
then `c ≤ N * ((1 + r)⁻¹) ^ k`. -/
theorem le_mul_inv_pow_of_mul_le {c S N R r : ℝ} {k : ℕ} (hk : k ≤ 3) (hr0 : 0 ≤ r) (hr : r ≤ R)
    (hS : 0 ≤ S)
    (hc : c ≤ S) (hN : S * (1 + R) ^ 3 ≤ N) : c ≤ N * ((1 + r)⁻¹) ^ k := by
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h1 : (1 + r) ^ k ≤ (1 + R) ^ 3 :=
    (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (pow_le_pow_right₀ (by linarith) hk)
  calc c * (1 + r) ^ k ≤ S * (1 + r) ^ k := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ S * (1 + R) ^ 3 := mul_le_mul_of_nonneg_left h1 hS
    _ ≤ N := hN

/-- For real numbers, if `a ≤ c * (N * N)` and `c ≤ K` then `a ≤ K * (N * N)`. -/
theorem le_mul_mul_self_of_le {a c K N : ℝ} (ha : a ≤ c * (N * N)) (hc : c ≤ K) : a ≤ K * (N * N) :=
  ha.trans (mul_le_mul_of_nonneg_right hc (mul_self_nonneg N))

/-- For reals `0 ≤ a` and `0 ≤ n` and a natural number `k`, if `a ≤ B / (1 + n) ^ k` then `a ≤ B`.
-/
theorem le_of_le_div_one_add_pow {a B n : ℝ} (ha : 0 ≤ a) (hn : 0 ≤ n) (k : ℕ)
    (h : a ≤ B / (1 + n) ^ k) :
    a ≤ B := by
  have hpos : 0 < (1 + n) ^ k := pow_pos (by linarith) k
  have hone : 1 ≤ (1 + n) ^ k := one_le_pow₀ (by linarith)
  rw [le_div_iff₀ hpos] at h
  nlinarith

/-- For real numbers, if `0 ≤ f` and `s ^ 2 + (1 / 4) * g ^ 2 ≤ f ^ 2`, then `s ≤ f`. -/
theorem le_of_sq_add_le {s g f : ℝ} (hf : 0 ≤ f)
    (h : s ^ 2 + (1 / 4 : ℝ) * g ^ 2 ≤ f ^ 2) : s ≤ f := by
  nlinarith [sq_nonneg g]

/-- Assume `Z ≤ cL * N + R + cP * vn`, `N ≤ dB + A`, `R ≤ dR + rB * A`,
`cL * dB + dR + cP * vn ≤ ρ`, `cL + rB ≤ cT`, `A ≤ af * (2 * ρ) * r` and `2 * cT * af * r < 1`, with
`0 ≤ cL`, `0 < cT`, `0 ≤ A` and `0 ≤ ρ`. Then `Z ≤ 2 * ρ`. The terms with `A` add up to at most
`cT * A`, which is at most `ρ`. -/
theorem le_two_mul_of_le_add_add {Z cL cP N R vn dB dR A ρ cT rB af r : ℝ}
    (hZ : Z ≤ cL * N + R + cP * vn) (hN : N ≤ dB + A) (hR : R ≤ dR + rB * A)
    (hcL : 0 ≤ cL) (hsize : cL * dB + dR + cP * vn ≤ ρ)
    (hT : cL + rB ≤ cT) (hcT : 0 < cT) (hA0 : 0 ≤ A) (hA : A ≤ af * (2 * ρ) * r)
    (hsmall : 2 * cT * af * r < 1) (hρ : 0 ≤ ρ) : Z ≤ 2 * ρ := by
  have h1 := mul_le_mul_of_nonneg_left hN hcL
  have h3 : (cL + rB) * A ≤ cT * A := mul_le_mul_of_nonneg_right hT hA0
  have h4 : cT * A ≤ cT * (af * (2 * ρ) * r) := mul_le_mul_of_nonneg_left hA hcT.le
  have h5 : ρ * (2 * cT * af * r) ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsmall.le hρ
  have e : cT * (af * (2 * ρ) * r) = ρ * (2 * cT * af * r) := by ring
  linarith

/-- Assume `Z ≤ cL * N + cB * NB + cP * vn`, `N ≤ dB + A`, `NB ≤ dBB + A`,
`cL * dB + cB * dBB + cP * vn ≤ ρ`, `cL + cB ≤ cT`, `A ≤ af * (2 * ρ) * r` and
`2 * cT * af * r < 1`, with `0 ≤ cL`, `0 ≤ cB`, `0 < cT`, `0 ≤ A` and `0 ≤ ρ`. Then `Z ≤ 2 * ρ`. The
terms with `A` add up to at most `cT * A`, which is at most `ρ`. -/
theorem le_two_mul_of_le_mul_add {Z cL cB cP N NB vn dB dBB A ρ cT af r : ℝ}
    (hZ : Z ≤ cL * N + cB * NB + cP * vn) (hN : N ≤ dB + A) (hNB : NB ≤ dBB + A)
    (hcL : 0 ≤ cL) (hcB : 0 ≤ cB) (hsize : cL * dB + cB * dBB + cP * vn ≤ ρ)
    (hT : cL + cB ≤ cT) (hcT : 0 < cT) (hA0 : 0 ≤ A) (hA : A ≤ af * (2 * ρ) * r)
    (hsmall : 2 * cT * af * r < 1) (hρ : 0 ≤ ρ) : Z ≤ 2 * ρ := by
  have h1 := mul_le_mul_of_nonneg_left hN hcL
  have h2 := mul_le_mul_of_nonneg_left hNB hcB
  have h3 : (cL + cB) * A ≤ cT * A := mul_le_mul_of_nonneg_right hT hA0
  have h4 : cT * A ≤ cT * (af * (2 * ρ) * r) := mul_le_mul_of_nonneg_left hA hcT.le
  have h5 : ρ * (2 * cT * af * r) ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsmall.le hρ
  have e : cT * (af * (2 * ρ) * r) = ρ * (2 * cT * af * r) := by ring
  linarith

/-- For real numbers, if `0 ≤ d`, `a ^ 2 = b ^ 2 + c ^ 2` and `c ^ 2 + 1 / 4 * b ^ 2 ≤ d ^ 2`, then
`a ≤ 2 * d`. -/
theorem le_two_mul_of_sq_eq_add {a b c d : ℝ} (hd : 0 ≤ d) (h1 : a ^ 2 = b ^ 2 + c ^ 2)
    (h2 : c ^ 2 + 1 / 4 * b ^ 2 ≤ d ^ 2) : a ≤ 2 * d := by
  have h3 : a ^ 2 ≤ (2 * d) ^ 2 := by nlinarith [sq_nonneg c]
  nlinarith

/-- Let `0 < ε`, `0 ≤ A`, `x < ε / (8 * (A + 1))`, `s < 3 * (ε / (8 * (A + 1)))`, `g ≤ 2` and
`g' ≤ 2` be real numbers. If `e ≤ A * (x + s) + ε / 8 * (g + g')`, then `e < ε`. The proof bounds
`A * (x + s)` by `ε / 2 * (A / (A + 1))`, which is less than `ε / 2`, and `ε / 8 * (g + g')` by
`ε / 2`. -/
theorem lt_of_le_mul_add_eighth_mul {ε A x s g g' e : ℝ} (hε : 0 < ε) (hA : 0 ≤ A)
    (hx : x < ε / (8 * (A + 1))) (hs : s < 3 * (ε / (8 * (A + 1)))) (hg : g ≤ 2) (hg' : g' ≤ 2)
    (h : e ≤ A * (x + s) + ε / 8 * (g + g')) : e < ε := by
  have hA1 : 0 < A + 1 := by linarith
  have hδ : A * (4 * (ε / (8 * (A + 1)))) = ε / 2 * (A / (A + 1)) := by
    field_simp
    ring
  have hq : A / (A + 1) < 1 := (div_lt_one hA1).2 (by linarith)
  have h1 : A * (x + s) ≤ A * (4 * (ε / (8 * (A + 1)))) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have h2 : ε / 8 * (g + g') ≤ ε / 2 := by nlinarith
  nlinarith

/-- For natural numbers `e0`, `e1` and real `t` with `0 ≤ t ≤ 1`:
`t * (1 - t) * |e0 * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 * (e1 * (1 - t) ^ (e1 - 1) * (-1))| ≤
(e0 + e1) * (1 - t) ^ e1`. The expression inside the absolute value is the derivative of
`t ^ e0 * (1 - t) ^ e1`, written out by the product rule. The proof bounds the absolute value by the
sum of the two terms and uses `t * (e0 * t ^ (e0 - 1)) = e0 * t ^ e0`, the same identity for
`1 - t`, and `t ^ e0 ≤ 1`. -/
theorem mul_abs_pow_pred_mul_pow_le (e0 e1 : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t * (1 - t) * |(e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 *
        ((e1 : ℝ) * (1 - t) ^ (e1 - 1) * (-1))| ≤
      (e0 + e1) * (1 - t) ^ e1 := by
  have hu : 0 ≤ 1 - t := by linarith
  have hA : 0 ≤ (e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 := by positivity
  have hB : 0 ≤ t ^ e0 * ((e1 : ℝ) * (1 - t) ^ (e1 - 1)) := by positivity
  have habs : |(e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 *
      ((e1 : ℝ) * (1 - t) ^ (e1 - 1) * (-1))| ≤
      (e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 * ((e1 : ℝ) * (1 - t) ^ (e1 - 1)) :=
    abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have ha : t * ((e0 : ℝ) * t ^ (e0 - 1)) = e0 * t ^ e0 := mul_natCast_mul_pow_pred t e0
  have hb : (1 - t) * ((e1 : ℝ) * (1 - t) ^ (e1 - 1)) = e1 * (1 - t) ^ e1 :=
      mul_natCast_mul_pow_pred (1 - t) e1
  have htp : t ^ e0 ≤ 1 := pow_le_one₀ h0 h1
  have htp0 : 0 ≤ t ^ e0 := pow_nonneg h0 e0
  have hup : 0 ≤ (1 - t) ^ e1 := pow_nonneg hu e1
  have hstep : t * (1 - t) * ((e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 *
      ((e1 : ℝ) * (1 - t) ^ (e1 - 1))) =
      ((e0 : ℝ) * (1 - t) ^ e1) * (t ^ e0 * (1 - t)) + ((e1 : ℝ) * (1 - t) ^ e1) * (t ^ e0 * t) :=
          by
    linear_combination ((1 - t) * (1 - t) ^ e1) * ha + (t ^ e0 * t) * hb
  have hp1 : ((e0 : ℝ) * (1 - t) ^ e1) * (t ^ e0 * (1 - t)) ≤ (e0 : ℝ) * (1 - t) ^ e1 :=
    mul_le_of_le_one_right (by positivity) (by nlinarith)
  have hp2 : ((e1 : ℝ) * (1 - t) ^ e1) * (t ^ e0 * t) ≤ (e1 : ℝ) * (1 - t) ^ e1 :=
    mul_le_of_le_one_right (by positivity) (by nlinarith)
  calc _ ≤ t * (1 - t) * ((e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 *
           ((e1 : ℝ) * (1 - t) ^ (e1 - 1))) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ _ := by rw [hstep]; linarith

/-- Let `C`, `s`, `y` be nonnegative reals. If `S ≤ y` and `√(C * (s + s ^ 2)) ≤ m`, then
`C * (s * y * S + (s * y) ^ 2) ≤ (m * y) ^ 2`. The proof bounds the left side by
`C * (s + s ^ 2) * y ^ 2`, which is the square of `√(C * (s + s ^ 2)) * y`. -/
theorem mul_add_le_sq_of_sqrt_le {C s y S m : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s) (hy : 0 ≤ y)
    (hS : S ≤ y) (hm : Real.sqrt (C * (s + s ^ 2)) ≤ m) :
    C * (s * y * S + (s * y) ^ 2) ≤ (m * y) ^ 2 := by
  have hq0 : 0 ≤ C * (s + s ^ 2) := mul_nonneg hC (by positivity)
  have hsq : (Real.sqrt (C * (s + s ^ 2)) * y) ^ 2 = C * (s + s ^ 2) * y ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hq0]
  have h1 : s * y * S ≤ s * y * y := mul_le_mul_of_nonneg_left hS (mul_nonneg hs hy)
  have h2 : C * (s * y * S + (s * y) ^ 2) ≤ C * (s + s ^ 2) * y ^ 2 := by
    have : C * (s * y * S + (s * y) ^ 2) ≤ C * (s * y * y + (s * y) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hC
    nlinarith
  calc C * (s * y * S + (s * y) ^ 2) ≤ (Real.sqrt (C * (s + s ^ 2)) * y) ^ 2 := by
         rw [hsq]; exact h2
    _ ≤ (m * y) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hy) (mul_le_mul_of_nonneg_right hm hy) 2

/-- For real `a`, `b`, `x`, `y` and `w > 0`:
`a * x + b * y ≤ √(a ^ 2 + b ^ 2 / w) * √(x ^ 2 + w * y ^ 2)`. The proof squares both sides and uses
that `w` times the difference of the squares is `(a * w * y - b * x) ^ 2`. -/
theorem mul_add_mul_le_sqrt_mul_sqrt {a b x y w : ℝ} (hw : 0 < w) :
    a * x + b * y ≤ Real.sqrt (a ^ 2 + b ^ 2 / w) * Real.sqrt (x ^ 2 + w * y ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  have key : w * ((a ^ 2 + b ^ 2 / w) * (x ^ 2 + w * y ^ 2) - (a * x + b * y) ^ 2) =
      (a * w * y - b * x) ^ 2 := by
    field_simp
    ring
  have h : 0 ≤ (a ^ 2 + b ^ 2 / w) * (x ^ 2 + w * y ^ 2) - (a * x + b * y) ^ 2 := by
    by_contra hneg
    push Not at hneg
    have : w * ((a ^ 2 + b ^ 2 / w) * (x ^ 2 + w * y ^ 2) - (a * x + b * y) ^ 2) < 0 :=
      mul_neg_of_pos_of_neg hw hneg
    rw [key] at this
    exact absurd this (not_lt.2 (sq_nonneg _))
  linarith

/-- If `a ^ 2 ≤ D` and `b ^ 2 ≤ D` for real numbers, then `(a * M + b * M) ^ 2 ≤ 4 * M ^ 2 * D` for
every real `M`. -/
theorem mul_add_mul_sq_le_four_mul {a b M D : ℝ} (ha : a ^ 2 ≤ D) (hb : b ^ 2 ≤ D) :
    (a * M + b * M) ^ 2 ≤ 4 * M ^ 2 * D := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg M),
    mul_le_mul_of_nonneg_left hb (sq_nonneg M), mul_nonneg (sq_nonneg M) (sq_nonneg (a - b))]

/-- For a real `t > 0` and reals `u₁ u₂ v₁ v₂`,
`0 ≤ t * (u₁ ^ 2 + u₂ ^ 2) + 2 * (v₁ * u₁ + v₂ * u₂) + (v₁ ^ 2 + v₂ ^ 2) / t`. The right side equals
`((t * u₁ + v₁) ^ 2 + (t * u₂ + v₂) ^ 2) / t`. -/
theorem mul_add_two_mul_add_div_nonneg {t : ℝ} (ht : 0 < t) (u₁ u₂ v₁ v₂ : ℝ) :
    0 ≤ t * (u₁ ^ 2 + u₂ ^ 2) + 2 * (v₁ * u₁ + v₂ * u₂) + (v₁ ^ 2 + v₂ ^ 2) / t := by
  have e : t * (u₁ ^ 2 + u₂ ^ 2) + 2 * (v₁ * u₁ + v₂ * u₂) + (v₁ ^ 2 + v₂ ^ 2) / t
      = ((t * u₁ + v₁) ^ 2 + (t * u₂ + v₂) ^ 2) / t := by
    field_simp
    ring
  rw [e]
  positivity

/-- If `0 ≤ K ≤ K'`, `0 ≤ X ≤ X'` and `0 < d`, then `K * (X / d) ≤ K' * X' / d`. -/
theorem mul_div_le_mul_div_of_le {K K' X X' d : ℝ} (hK : 0 ≤ K) (hKK : K ≤ K') (hX : 0 ≤ X)
    (hXX : X ≤ X') (hd : 0 < d) :
    K * (X / d) ≤ K' * X' / d := by
  rw [mul_div_assoc]
  exact mul_le_mul hKK (div_le_div_of_nonneg_right hXX hd.le) (by positivity) (hK.trans hKK)

/-- For real numbers with `r > 0`, `a * s = r * (a / r * s)`. -/
theorem mul_eq_mul_div_mul {r a s : ℝ} (hr : 0 < r) : a * s = r * (a / r * s) := by
  field_simp

/-- Let `p : ℝ × ℝ` have nonnegative components with `p.1 ≤ r` and `p.2 ≤ z`, and let `a ≥ 0`. Then
`a * p.1 ≤ (r ^ 2 + z ^ 2) * (a / (p.1 ^ 2 + p.2 ^ 2) * p.1)`. If `p.1 ^ 2 + p.2 ^ 2 = 0` both sides
are zero, and otherwise the left side is the right side with `p.1 ^ 2 + p.2 ^ 2` in place of
`r ^ 2 + z ^ 2`. -/
theorem mul_fst_le_sq_add_sq_mul (p : ℝ × ℝ) (a r z : ℝ) (ha : 0 ≤ a) (h1 : 0 ≤ p.1) (h2 : 0 ≤ p.2)
    (hr : p.1 ≤ r)
    (hz : p.2 ≤ z) : a * p.1 ≤ (r ^ 2 + z ^ 2) * (a / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
  by_cases h0 : p.1 ^ 2 + p.2 ^ 2 = 0
  · have e : p.1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by
      nlinarith [sq_nonneg p.1, sq_nonneg p.2])
    simp [e]
  · have hpos : 0 < p.1 ^ 2 + p.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have hle : p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2 + z ^ 2 := by
      have := pow_le_pow_left₀ h1 hr 2
      have := pow_le_pow_left₀ h2 hz 2
      linarith
    have e : a * p.1 = (p.1 ^ 2 + p.2 ^ 2) * (a / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hle (mul_nonneg (div_nonneg ha hpos.le) h1)

/-- Let `w ≥ 0` and `a ≥ 0` be real numbers. If `a ≤ C * (1 + w) ^ (-1)` and
`e ≤ C * (1 + w) ^ (-2)`, with real powers, then `w * a ≤ C` and `e ≤ C`. The proof first gets
`C ≥ 0` from `a ≥ 0`, then uses `w * (1 + w)⁻¹ ≤ 1` and `(1 + w) ^ (-2) ≤ 1`. -/
theorem mul_le_and_le_of_rpow_neg {C w a e : ℝ} (hw : 0 ≤ w) (ha : a ≤ C * (1 + w) ^ (-(1 : ℝ)))
    (he : e ≤ C * (1 + w) ^ (-(2 : ℝ))) (ha0 : 0 ≤ a) : w * a ≤ C ∧ e ≤ C := by
  have h1 : (1 + w) ^ (-(1 : ℝ)) = (1 + w)⁻¹ := Real.rpow_neg_one _
  have hpos : 0 < 1 + w := by linarith
  have hC : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have : C * (1 + w) ^ (-(1 : ℝ)) < 0 := mul_neg_of_neg_of_pos hneg (Real.rpow_pos_of_pos hpos _)
    linarith
  have h2 : (1 + w) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  refine ⟨?_, he.trans (by nlinarith)⟩
  rw [h1] at ha
  have hw1 : w * (1 + w)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hpos]; linarith
  calc w * a ≤ w * (C * (1 + w)⁻¹) := mul_le_mul_of_nonneg_left ha hw
    _ = C * (w * (1 + w)⁻¹) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hw1 hC
    _ = C := mul_one C

/-- Young's inequality with the weight `u / v`: for real `a`, `b` and `u > 0`, `v > 0`,
`a * b ≤ (u / v * a ^ 2 + v / u * b ^ 2) / 2`. This is `two_mul_mul_le_mul_sq_add` at `β = u / v`,
divided by `2`. -/
theorem mul_le_half_div_mul_sq_add {a b u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    a * b ≤ (u / v * a ^ 2 + v / u * b ^ 2) / 2 := by
  have h := two_mul_mul_le_mul_sq_add a b (u / v) (div_pos hu hv)
  rw [show b ^ 2 / (u / v) = v / u * b ^ 2 by field_simp] at h
  linarith

/-- Young's inequality with the weight `u / v`: for real `a`, `b` and `u > 0`, `v > 0`,
`a * b ≤ (a ^ 2 * u / v + b ^ 2 * v / u) / 2`. This is `mul_le_half_div_mul_sq_add` with the factors
in another order. -/
theorem mul_le_half_sq_mul_div_add (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    a * b ≤ (a ^ 2 * u / v + b ^ 2 * v / u) / 2 := by
  have h := mul_le_half_div_mul_sq_add (a := a) (b := b) hu hv
  rwa [show u / v * a ^ 2 = a ^ 2 * u / v by ring, show v / u * b ^ 2 = b ^ 2 * v / u by ring] at h

/-- For nonnegative reals `a`, `b`: `a * b ≤ a ^ 6 + b ^ ((6 : ℝ) / 5)`, a Young-type bound for the
conjugate exponents `6` and `6 / 5`. The proof splits on whether `a ≤ b ^ ((1 : ℝ) / 5)`: in the
first case `a * b ≤ b ^ ((6 : ℝ) / 5)`, in the second `b ≤ a ^ 5` and `a * b ≤ a ^ 6`. -/
theorem mul_le_pow_six_add_rpow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ a ^ 6 + b ^ ((6 : ℝ) / 5) := by
  by_cases h : a ≤ b ^ ((1 : ℝ) / 5)
  · have e : b ^ ((6 : ℝ) / 5) = b ^ ((1 : ℝ) / 5) * b := by
      rw [show (6 : ℝ) / 5 = 1 / 5 + 1 by norm_num, Real.rpow_add' hb (by norm_num), Real.rpow_one]
    have h1 : a * b ≤ b ^ ((1 : ℝ) / 5) * b := mul_le_mul_of_nonneg_right h hb
    linarith [pow_nonneg ha 6]
  · replace h := not_le.1 h
    have e : (b ^ ((1 : ℝ) / 5)) ^ (5 : ℕ) = b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
      norm_num
    have hb5 : b ≤ a ^ 5 := by
      calc b = (b ^ ((1 : ℝ) / 5)) ^ (5 : ℕ) := e.symm
        _ ≤ a ^ 5 := pow_le_pow_left₀ (Real.rpow_nonneg hb _) h.le 5
    have h1 : a * b ≤ a * a ^ 5 := mul_le_mul_of_nonneg_left hb5 ha
    have h6 : a * a ^ 5 = a ^ 6 := by ring
    linarith [Real.rpow_nonneg hb ((6 : ℝ) / 5)]

/-- For reals `a`, `b` and `u > 0`, `a * b ≤ u * a ^ 2 / 2 + b ^ 2 / (2 * u)`. This is
`two_mul_mul_le_mul_sq_add` divided by `2`. -/
theorem mul_le_split_squares {a b u : ℝ} (hu : 0 < u) :
    a * b ≤ u * a ^ 2 / 2 + b ^ 2 / (2 * u) := by
  have h := two_mul_mul_le_mul_sq_add a b u hu
  rw [show b ^ 2 / (2 * u) = b ^ 2 / u / 2 by rw [div_div, mul_comm]]
  linarith

/-- For `0 ≤ a`, `0 ≤ b` and `0 < s`, `a * b ≤ a ^ 2 / s ^ 2 + s ^ 2 * b ^ 2`. -/
theorem mul_le_sq_div_add_mul_sq (a b s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) :
    a * b ≤ a ^ 2 / s ^ 2 + s ^ 2 * b ^ 2 := by
  have h1 : a * b = (a / s) * (s * b) := by field_simp
  have h2 : a ^ 2 / s ^ 2 = (a / s) ^ 2 := by rw [div_pow]
  have h3 : s ^ 2 * b ^ 2 = (s * b) ^ 2 := by rw [mul_pow]
  have h4 : 0 ≤ a / s := div_nonneg ha hs.le
  have h5 : 0 ≤ s * b := mul_nonneg hs.le hb
  rw [h1, h2, h3]
  nlinarith [sq_nonneg (a / s - s * b), mul_nonneg h4 h5]

/-- Young-type inequality with a parameter: for real numbers `u`, `v` and `K > 0`,
`u * v ≤ u ^ 2 * K / 4 + v ^ 2 / K`. This is `two_mul_mul_le_mul_sq_add` at `β = K / 2`, divided by
`2`. -/
theorem mul_le_sq_mul_add_sq_div {u v K : ℝ} (hK : 0 < K) : u * v ≤ u ^ 2 * K / 4 + v ^ 2 / K := by
  have h := two_mul_mul_le_mul_sq_add u v (K / 2) (half_pos hK)
  rw [show v ^ 2 / (K / 2) = 2 * (v ^ 2 / K) by field_simp] at h
  linarith

/-- For real numbers with `0 ≤ c`, `0 ≤ F` and `N ≤ 2 * F`, one has `0 ≤ (2 + 2 * c) * F`,
`2 * F ≤ (2 + 2 * c) * F` and `c * N ≤ (2 + 2 * c) * F`. -/
theorem mul_le_two_add_two_mul_mul {c F N : ℝ} (hc : 0 ≤ c) (hF : 0 ≤ F) (hNF : N ≤ 2 * F) :
    0 ≤ (2 + 2 * c) * F ∧ 2 * F ≤ (2 + 2 * c) * F ∧ c * N ≤ (2 + 2 * c) * F := by
  refine ⟨by positivity, by nlinarith, ?_⟩
  have : c * N ≤ c * (2 * F) := mul_le_mul_of_nonneg_left hNF hc
  nlinarith

/-- For real numbers with `0 ≤ c`, `1 ≤ r`, `0 ≤ s`, `0 ≤ t` and `r * c ≤ B`,
`c * (s * t) ≤ B * (s ^ 2 + t ^ 2 / r ^ 2) / 2`. The proof uses `c ≤ B / r` and
`s * (t / r) ≤ (s ^ 2 + t ^ 2 / r ^ 2) / 2`. -/
theorem mul_mul_le_half_mul_add_sq {c r s t B : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t)
    (hcB : r * c ≤ B) : c * (s * t) ≤ B * (s ^ 2 + t ^ 2 / r ^ 2) / 2 := by
  have hr0 : 0 < r := by linarith
  have hB : 0 ≤ B := le_trans (mul_nonneg hr0.le hc) hcB
  have h1 : c ≤ B / r := by
    rw [le_div_iff₀ hr0]
    linarith [mul_comm r c]
  have h2 : s * (t / r) ≤ (s ^ 2 + t ^ 2 / r ^ 2) / 2 := by
    have h3 := sq_nonneg (s - t / r)
    have e : (t / r) ^ 2 = t ^ 2 / r ^ 2 := div_pow t r 2
    nlinarith [h3, e]
  calc c * (s * t) ≤ (B / r) * (s * t) := mul_le_mul_of_nonneg_right h1 (mul_nonneg hs ht)
    _ = B * (s * (t / r)) := by field_simp
    _ ≤ B * ((s ^ 2 + t ^ 2 / r ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 hB
    _ = B * (s ^ 2 + t ^ 2 / r ^ 2) / 2 := by ring

/-- For real numbers with `0 < u`, `0 ≤ X`, `X * u ≤ A`, `0 ≤ g` and `0 ≤ a`,
`X * g * a ≤ A * (g ^ 2 + a ^ 2 / u ^ 2)`. The proof writes `a = (a / u) * u`, so that
`X * g * a = (X * u) * (g * (a / u))`, and uses `g * (a / u) ≤ g ^ 2 + (a / u) ^ 2`. -/
theorem mul_mul_le_mul_add_div_sq {X u g a A : ℝ} (hu : 0 < u) (hX : 0 ≤ X) (hXu : X * u ≤ A)
    (hg : 0 ≤ g) (ha : 0 ≤ a) :
    X * g * a ≤ A * (g ^ 2 + a ^ 2 / u ^ 2) := by
  have hA : 0 ≤ A := le_trans (mul_nonneg hX hu.le) hXu
  set r := a / u with hr
  have hr0 : 0 ≤ r := div_nonneg ha hu.le
  have ha' : a = r * u := by rw [hr]; field_simp
  have hr2 : a ^ 2 / u ^ 2 = r ^ 2 := by rw [hr, div_pow]
  rw [hr2, ha']
  have h1 : X * g * (r * u) = (X * u) * (g * r) := by ring
  rw [h1]
  have h2 : (X * u) * (g * r) ≤ A * (g * r) := mul_le_mul_of_nonneg_right hXu (mul_nonneg hg hr0)
  have h3 : g * r ≤ g ^ 2 + r ^ 2 := by nlinarith [sq_nonneg (g - r)]
  nlinarith [mul_le_mul_of_nonneg_left h3 hA]

/-- Let `d`, `m`, `a` be nonnegative reals with `d ≤ C * a`, and let `b` be any real. Then
`d * m * b ≤ C ^ 2 * (a ^ 3 + m ^ 6) + b ^ 2`. The proof uses `d * m * b ≤ (d * m) ^ 2 + b ^ 2` and
`a ^ 2 * m ^ 2 ≤ a ^ 3 + m ^ 6`. -/
theorem mul_mul_le_sq_mul_add_sq (d m b a C : ℝ) (hd : 0 ≤ d) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (hda : d ≤ C * a) : d * m * b ≤ C ^ 2 * (a ^ 3 + m ^ 6) + b ^ 2 := by
  have h1 : d * m * b ≤ (d * m) ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (2 * (d * m) - b), sq_nonneg b]
  have h2 : d ^ 2 ≤ (C * a) ^ 2 := pow_le_pow_left₀ hd hda 2
  have h3 : a ^ 2 * m ^ 2 ≤ a ^ 3 + m ^ 6 := by
    have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
    have hk : 0 ≤ (a - m ^ 2) ^ 2 * (2 * a + m ^ 2) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    nlinarith [pow_nonneg ha 3, pow_nonneg hm 6]
  have h4 : (d * m) ^ 2 ≤ C ^ 2 * (a ^ 3 + m ^ 6) := by
    calc (d * m) ^ 2 = d ^ 2 * m ^ 2 := by ring
      _ ≤ (C * a) ^ 2 * m ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg m)
      _ = C ^ 2 * (a ^ 2 * m ^ 2) := by ring
      _ ≤ C ^ 2 * (a ^ 3 + m ^ 6) := mul_le_mul_of_nonneg_left h3 (sq_nonneg C)
  linarith

/-- For real numbers with `0 ≤ δ` and `δ ≤ 1`,
`δ * (3 * b ^ 2 * (1 + R ^ 2)) * (δ * (3 * M ^ 2)) ≤ 9 * b ^ 2 * (1 + R ^ 2) * δ * M ^
2`. The left side is the right side with `δ * δ` in place of `δ`, and `δ * δ ≤ δ`. -/
theorem mul_mul_mul_le_of_le_one {b R M δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ * (3 * b ^ 2 * (1 + R ^ 2)) * (δ * (3 * M ^ 2)) ≤ 9 * b ^ 2 * (1 + R ^ 2) * δ * M ^ 2 := by
  have hδδ : δ * δ ≤ δ := by nlinarith
  have hq : 0 ≤ 9 * b ^ 2 * (1 + R ^ 2) * M ^ 2 := by positivity
  calc δ * (3 * b ^ 2 * (1 + R ^ 2)) * (δ * (3 * M ^ 2)) = (9 * b ^ 2 * (1 + R ^ 2) * M ^ 2) *
           (δ * δ) := by ring
    _ ≤ (9 * b ^ 2 * (1 + R ^ 2) * M ^ 2) * δ := mul_le_mul_of_nonneg_left hδδ hq
    _ = _ := by ring

/-- If `0 ≤ m ≤ M1`, `0 ≤ b ≤ B1` and `0 ≤ K`, then `m * (1 + b * K) ^ 2 ≤ M1 * (1 + B1 * K) ^ 2`.
-/
theorem mul_one_add_mul_sq_le {m b M1 B1 K : ℝ} (hm0 : 0 ≤ m) (hb0 : 0 ≤ b) (hK : 0 ≤ K)
    (hm : m ≤ M1) (hb : b ≤ B1) :
    m * (1 + b * K) ^ 2 ≤ M1 * (1 + B1 * K) ^ 2 := by
  have h0 : 0 ≤ 1 + b * K := add_nonneg zero_le_one (mul_nonneg hb0 hK)
  have h1 : 1 + b * K ≤ 1 + B1 * K := by linarith [mul_le_mul_of_nonneg_right hb hK]
  exact mul_le_mul hm (pow_le_pow_left₀ h0 h1 2) (sq_nonneg _) (hm0.trans hm)

/-- A binary quadratic form with nonpositive discriminant is nonnegative: for reals with `0 ≤ A`,
`0 ≤ B` and `c ^ 2 ≤ 4 * A * B`, `0 ≤ A * x ^ 2 + B * y ^ 2 - c * x * y`. For `A > 0` the proof
completes the square,
`4 * A * (A * x ^ 2 + B * y ^ 2 - c * x * y) = (2 * A * x - c * y) ^ 2 + (4 * A * B - c ^ 2) * y ^
2`; for `A = 0` the hypothesis gives `c = 0`. -/
theorem mul_sq_add_mul_sq_sub_nonneg {A B c x y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : c ^ 2 ≤ 4 * A * B) :
    0 ≤ A * x ^ 2 + B * y ^ 2 - c * x * y := by
  rcases hA.eq_or_lt with h0 | hpos
  · subst h0
    have hc : c = 0 := by nlinarith [sq_nonneg c]
    subst hc
    nlinarith [sq_nonneg y]
  · have key : 4 * A * (A * x ^ 2 + B * y ^ 2 - c * x * y) =
        (2 * A * x - c * y) ^ 2 + (4 * A * B - c ^ 2) * y ^ 2 := by ring
    have hr : 0 ≤ (2 * A * x - c * y) ^ 2 + (4 * A * B - c ^ 2) * y ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
    rcases lt_or_ge (A * x ^ 2 + B * y ^ 2 - c * x * y) 0 with hn | hn
    · have := mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < 4 * A) hn
      linarith
    · exact hn

/-- For real numbers with `0 < u` and `X * u ^ 2 ≤ A`, `X * a ^ 2 ≤ A * (a ^ 2 / u ^ 2)`. -/
theorem mul_sq_le_mul_sq_div_sq {X u a A : ℝ} (hu : 0 < u) (hXu : X * u ^ 2 ≤ A) :
    X * a ^ 2 ≤ A * (a ^ 2 / u ^ 2) := by
  have hu2 : 0 < u ^ 2 := by positivity
  rw [mul_div_assoc', le_div_iff₀ hu2]
  nlinarith [mul_le_mul_of_nonneg_right hXu (sq_nonneg a)]

/-- For real numbers with `0 ≤ c ≤ 1`, `T ≥ 0`, `r ≥ 0` and `m ≥ 0`,
`((1 - c) ^ 2 * Pv ^ 2 + m * ((-(1 / δ) * Pv + c * Dv) ^ 2 + c ^ 2 * T)) * r ≤
2 * m * ((Dv ^ 2 + T) * r) + ((1 - c) ^ 2 + 2 * m / δ ^ 2) * (Pv ^ 2 * r)`. The statement also takes
a real `x` with `x = Pv / δ`, which does not occur in the conclusion. The proof bounds
`(-x + c * Dv) ^ 2` by `2 * x ^ 2 + 2 * Dv ^ 2` and `c ^ 2 * T` by `T`. -/
theorem mul_sq_neg_div_add_mul_le (c x Dv T r m Pv δ : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hT : 0 ≤ T)
    (hr : 0 ≤ r)
    (hm : 0 ≤ m) (hx : x = Pv / δ) :
    ((1 - c) ^ 2 * Pv ^ 2 + m * ((-(1 / δ) * Pv + c * Dv) ^ 2 + c ^ 2 * T)) * r
      ≤ 2 * m * ((Dv ^ 2 + T) * r) + ((1 - c) ^ 2 + 2 * m / δ ^ 2) * (Pv ^ 2 * r) := by
  have hx2 : Pv ^ 2 / δ ^ 2 = x ^ 2 := by rw [hx, div_pow]
  have e1 : -(1 / δ) * Pv = -x := by rw [hx]; ring
  rw [e1]
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have h1 : (-x + c * Dv) ^ 2 ≤ 2 * x ^ 2 + 2 * Dv ^ 2 := by
    nlinarith [sq_nonneg (x + c * Dv), mul_le_mul_of_nonneg_right hc2 (sq_nonneg Dv)]
  have h2 : c ^ 2 * T ≤ T := by nlinarith
  have h3 : m * ((-x + c * Dv) ^ 2 + c ^ 2 * T) ≤ 2 * m * (Dv ^ 2 + T) + 2 * m / δ ^ 2 * Pv ^ 2 :=
      by
    have : 2 * m / δ ^ 2 * Pv ^ 2 = 2 * m * x ^ 2 := by rw [← hx2]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left h1 hm, mul_le_mul_of_nonneg_left h2 hm]
  nlinarith [mul_le_mul_of_nonneg_right h3 hr]

/-- Young-type bound for a cross term: for real numbers, if `0 ≤ χ`, `|c| ≤ L` and `|q| ≤ p * d`,
then `-(2 * χ * c * q) ≤ (1 / 2) * χ ^ 2 * d ^ 2 + 2 * L ^ 2 * p ^ 2`. The proof bounds the left
side by `2 * χ * (L * (p * d))` and uses `0 ≤ (χ * d - 2 * L * p) ^ 2`. -/
theorem neg_mul_le_half_sq_add_sq {χ c L p d q : ℝ} (hχ : 0 ≤ χ) (hc : |c| ≤ L)
    (hq : |q| ≤ p * d) : -(2 * χ * c * q) ≤ (1 / 2) * χ ^ 2 * d ^ 2 + 2 * L ^ 2 * p ^ 2 := by
  have hL : 0 ≤ L := (abs_nonneg c).trans hc
  have h1 : |2 * χ * c * q| = 2 * χ * (|c| * |q|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hχ, abs_two]
    ring
  have h2 : |c| * |q| ≤ L * (p * d) := mul_le_mul hc hq (abs_nonneg q) hL
  have h3 : 2 * χ * (|c| * |q|) ≤ 2 * χ * (L * (p * d)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 2 * χ * (L * (p * d)) ≤ (1 / 2) * χ ^ 2 * d ^ 2 + 2 * L ^ 2 * p ^ 2 := by
    nlinarith [sq_nonneg (χ * d - 2 * L * p)]
  linarith [neg_le_abs (2 * χ * c * q)]

/-- For a natural number `N`, `-(N : ℝ) ≤ N`. -/
theorem neg_natCast_le_natCast (N : ℕ) : -(N : ℝ) ≤ N := neg_le_self (Nat.cast_nonneg N)

/-- For nonnegative real numbers `a`, `b`, `c`, `d`, `e`, `-a - b - c - d * e ≤ 0`. -/
theorem neg_sub_sub_sub_mul_nonpos {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) :
    -a - b - c - d * e ≤ 0 := by
  nlinarith [mul_nonneg hd he]

/-- Let `0 < c`, `0 ≤ d`, `d ≤ BD`, `|z| ≤ BZ`, `hd ≤ HD`, `w ≤ Bw`, `0 < 1 + r` and
`(1 + r) ^ 2 * hz ≤ BZ` be real numbers, and let `X2`, `Xc`, `Xo`, `X1`, `X0` be nonnegative real
numbers. Then `-((d - c) * X2 + (1 - d) * Xc + (1 / 4 - z) * Xo + (z - hd - c * w) * X1 - hz * X0) ≤
(c + BD + 1 + BZ + |HD| + c * |Bw|) * (X2 + Xc + Xo + X1) + BZ * (X0 / (1 + r) ^
2)`. The proof bounds each of the five terms separately. -/
theorem neg_sum_five_mul_le {c d z hd hz w BD BZ HD Bw r X2 Xc Xo X1 X0 : ℝ} (hc : 0 < c)
    (hd0 : 0 ≤ d) (hdB : d ≤ BD)
    (hz0 : |z| ≤ BZ) (hhd : hd ≤ HD) (hw : w ≤ Bw) (hr : 0 < 1 + r) (hhz : (1 + r) ^ 2 * hz ≤ BZ)
    (h2 : 0 ≤ X2) (hcX : 0 ≤ Xc) (ho : 0 ≤ Xo) (h1 : 0 ≤ X1) (h0 : 0 ≤ X0) :
    -((d - c) * X2 + (1 - d) * Xc + (1 / 4 - z) * Xo + (z - hd - c * w) * X1 - hz * X0) ≤
      (c + BD + 1 + BZ + |HD| + c * |Bw|) * (X2 + Xc + Xo + X1) + BZ * (X0 / (1 + r) ^ 2) := by
  have hBZ : 0 ≤ BZ := (abs_nonneg z).trans hz0
  have hzz := abs_le.1 hz0
  have hA : 0 ≤ |HD| + c * |Bw| := add_nonneg (abs_nonneg _) (mul_nonneg hc.le (abs_nonneg _))
  have hcw : c * w ≤ c * |Bw| := mul_le_mul_of_nonneg_left (hw.trans (le_abs_self _)) hc.le
  have e1 : (c - d) * X2 ≤ (c + BD + 1 + BZ + |HD| + c * |Bw|) * X2 :=
    mul_le_mul_of_nonneg_right (by linarith) h2
  have e2 : (d - 1) * Xc ≤ (c + BD + 1 + BZ + |HD| + c * |Bw|) * Xc :=
    mul_le_mul_of_nonneg_right (by linarith) hcX
  have e3 : (z - 1 / 4) * Xo ≤ (c + BD + 1 + BZ + |HD| + c * |Bw|) * Xo :=
    mul_le_mul_of_nonneg_right (by linarith) ho
  have e4 : (-z + hd + c * w) * X1 ≤ (c + BD + 1 + BZ + |HD| + c * |Bw|) * X1 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self HD]) h1
  have hr2 : 0 < (1 + r) ^ 2 := by positivity
  have e5 : hz * X0 ≤ BZ * (X0 / (1 + r) ^ 2) := by
    rw [mul_div_assoc', le_div_iff₀ hr2]
    nlinarith [mul_le_mul_of_nonneg_right hhz h0]
  nlinarith [e1, e2, e3, e4, e5]

/-- Let `|cD| ≤ Bd`, `hD ≤ K1`, `|cZ| ≤ Bz`, `hZ ≤ Bz * q`, `0 < c`, `wv ≤ Bw`, `0 ≤ q`,
`xc ^ 2 ≤ 729 * x2 ^ 2`, `xo ^ 2 ≤ 243 * x1 ^ 2`, `0 ≤ Bd`, `0 ≤ Bz`, `0 ≤ K1` and `0 ≤ Bw` be real
numbers. Then `-((cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2 +
(cZ - hD - c * wv) * x1 ^ 2 - hZ * x0 ^ 2) ≤ (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz +
K1 + c * Bw + Bz) * (x2 ^ 2 + x1 ^ 2 + q * x0 ^ 2)`. The proof bounds each of the five terms, moving
`xc ^ 2` to `x2 ^ 2` and `xo ^ 2` to `x1 ^ 2` with the two hypotheses on squares. -/
theorem neg_sum_five_mul_sq_le {x2 xc x1 xo x0 cD hD cZ hZ c wv Bd Bz K1 Bw q : ℝ}
    (hcD : |cD| ≤ Bd) (hhD : hD ≤ K1) (hcZ : |cZ| ≤ Bz) (hhZ : hZ ≤ Bz * q) (hc : 0 < c)
    (hwB : wv ≤ Bw) (hq : 0 ≤ q) (hxc : xc ^ 2 ≤ 729 * x2 ^ 2) (hxo : xo ^ 2 ≤ 243 * x1 ^ 2)
    (hBd : 0 ≤ Bd) (hBz : 0 ≤ Bz) (hK1 : 0 ≤ K1) (hBw : 0 ≤ Bw) :
    -((cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2 + (cZ - hD - c * wv) * x1 ^ 2 -
        hZ * x0 ^ 2)
      ≤ (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz)
          * (x2 ^ 2 + x1 ^ 2 + q * x0 ^ 2) := by
  have a1 := abs_le.1 hcD
  have a2 := abs_le.1 hcZ
  have s2 := sq_nonneg x2
  have sc := sq_nonneg xc
  have s1 := sq_nonneg x1
  have so := sq_nonneg xo
  have s0 := sq_nonneg x0
  have t1 : -(cD - c) * x2 ^ 2 ≤ (Bd + c) * x2 ^ 2 := mul_le_mul_of_nonneg_right (by linarith) s2
  have t2 : -(1 - cD) * xc ^ 2 ≤ 729 * (1 + Bd) * x2 ^ 2 := by
    have := mul_le_mul_of_nonneg_right (show -(1 - cD) ≤ 1 + Bd by linarith) sc
    nlinarith
  have t3 : -(1 / 4 - cZ) * xo ^ 2 ≤ 243 * (1 / 4 + Bz) * x1 ^ 2 := by
    have := mul_le_mul_of_nonneg_right (show -(1 / 4 - cZ) ≤ 1 / 4 + Bz by linarith) so
    nlinarith
  have t4 : -(cZ - hD - c * wv) * x1 ^ 2 ≤ (Bz + K1 + c * Bw) * x1 ^ 2 := by
    have : c * wv ≤ c * Bw := mul_le_mul_of_nonneg_left hwB hc.le
    exact mul_le_mul_of_nonneg_right (by linarith) s1
  have t5 : hZ * x0 ^ 2 ≤ Bz * (q * x0 ^ 2) := by
    have := mul_le_mul_of_nonneg_right hhZ s0
    linarith [mul_assoc Bz q (x0 ^ 2)]
  have hq0 : 0 ≤ q * x0 ^ 2 := mul_nonneg hq s0
  have hcB : 0 ≤ c * Bw := mul_nonneg hc.le hBw
  have k2 : (Bd + c + 729 * (1 + Bd)) * x2 ^ 2
      ≤ (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * x2 ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) s2
  have k1 : (243 * (1 / 4 + Bz) + (Bz + K1 + c * Bw)) * x1 ^ 2
      ≤ (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * x1 ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) s1
  have k0 : Bz * (q * x0 ^ 2)
      ≤ (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * (q * x0 ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hq0
  have ex : (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) *
      (x2 ^ 2 + x1 ^ 2 + q * x0 ^ 2)
      = (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * x2 ^ 2
        + (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * x1 ^ 2
        + (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * (q * x0 ^ 2) :=
    by ring
  rw [ex]
  linarith

/-- For nonnegative real numbers `a`, `b`, `c`, `d`, `e`, `-a - b - c - d - e ≤ 0`. -/
theorem neg_sum_five_nonpos {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) :
    -a - b - c - d - e ≤ 0 := by linarith

/-- For `0 < t < 1` and complex numbers `y`, `w`, `‖y + w‖ ^ 2 ≤ ‖y‖ ^ 2 / t + ‖w‖ ^ 2 / (1 - t)`.
The proof uses the triangle inequality and the identity that the right side minus `(‖y‖ + ‖w‖) ^ 2`
equals `((1 - t) * ‖y‖ - t * ‖w‖) ^ 2 / (t * (1 - t))`. -/
theorem norm_add_sq_le_div_add_div {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y w : ℂ) :
    ‖y + w‖ ^ 2 ≤ ‖y‖ ^ 2 / t + ‖w‖ ^ 2 / (1 - t) := by
  have h1 : 0 < 1 - t := by linarith
  have htri : ‖y + w‖ ≤ ‖y‖ + ‖w‖ := norm_add_le y w
  have hsq : ‖y + w‖ ^ 2 ≤ (‖y‖ + ‖w‖) ^ 2 := by
    have := norm_nonneg (y + w); nlinarith
  have key : ‖y‖ ^ 2 / t + ‖w‖ ^ 2 / (1 - t) - (‖y‖ + ‖w‖) ^ 2 =
      ((1 - t) * ‖y‖ - t * ‖w‖) ^ 2 / (t * (1 - t)) := by
    field_simp; ring
  have : 0 ≤ ((1 - t) * ‖y‖ - t * ‖w‖) ^ 2 / (t * (1 - t)) := by positivity
  linarith

/-- For real numbers with `|t| ≤ 1` and `|e| ≤ C`, the product satisfies `‖t * e‖ ≤ C`. -/
theorem norm_mul_le_of_abs_le_one {C t e : ℝ} (ht : |t| ≤ 1) (he : |e| ≤ C) : ‖t * e‖ ≤ C := by
  rw [Real.norm_eq_abs, abs_mul]
  calc |t| * |e| ≤ 1 * C := mul_le_mul ht he (abs_nonneg _) zero_le_one
    _ = C := one_mul _

/-- For `0 < a` and any real `b`, `0 ≤ (1 + b / a) ^ 2 / a`. -/
theorem one_add_div_sq_div_nonneg {a : ℝ} (ha : 0 < a) (b : ℝ) : 0 ≤ (1 + b / a) ^ 2 / a := by
    positivity

/-- For `0 < s` and `0 ≤ r`, `1 + r ≤ (1 + s⁻¹) * (1 + s * r)`. -/
theorem one_add_le_one_add_inv_mul {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    1 + r ≤ (1 + s⁻¹) * (1 + s * r) := by
  have h1 : s⁻¹ * (s * r) = r := by field_simp
  have h2 : 0 ≤ s⁻¹ := (inv_pos.2 hs).le
  nlinarith [mul_nonneg hs.le hr]

/-- For reals with `0 < a` and `a ≤ b`, `1 / a ≤ (1 + b / a) ^ 2 / a`. -/
theorem one_div_le_add_div_sq_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 / a ≤ (1 + b / a) ^ 2 / a := by
  have h0 : 0 ≤ b / a := div_nonneg (ha.le.trans hab) ha.le
  exact div_le_div_of_nonneg_right (by nlinarith) ha.le

/-- The real number `501 / 500` lies strictly between `1` and `5 / 4`: `1 < 501 / 500` and
`501 / 500 < 5 / 4`. -/
theorem one_lt_501_div_500_and_lt : (1 : ℝ) < 501 / 500 ∧ (501 / 500 : ℝ) < 5 / 4 := by
  constructor <;> norm_num

/-- For real `L > 0` and `r > 1`, the number `σ = 1 - r / (r + L)` satisfies `σ = L / (r + L)`,
`0 < σ`, `σ < 1`, `σ ≤ L / r` and `r⁻¹ ≤ (1 + L) / L * σ`. -/
theorem one_sub_div_add_eq_and_bounds (L r : ℝ) (hL : 0 < L) (hr : 1 < r) :
    1 - r / (r + L) = L / (r + L) ∧ 0 < 1 - r / (r + L) ∧ 1 - r / (r + L) < 1 ∧ 1 - r / (r + L) ≤
        L / r ∧
      r⁻¹ ≤ (1 + L) / L * (1 - r / (r + L)) := by
  have hr0 : 0 < r := by linarith
  have hrl : 0 < r + L := by linarith
  have he : 1 - r / (r + L) = L / (r + L) := by field_simp; ring
  rw [he]
  refine ⟨rfl, div_pos hL hrl, (div_lt_one hrl).2 (by
    linarith), div_le_div_of_nonneg_left hL.le hr0 (by linarith), ?_⟩
  rw [inv_eq_one_div, div_mul_div_comm, div_le_div_iff₀ hr0 (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left hr (mul_pos hL hL)]

/-- For every real `x`, `1 - x ^ 2 ≤ 1`. -/
theorem one_sub_sq_le_one (x : ℝ) : 1 - x ^ 2 ≤ 1 := by
  have := sq_nonneg x
  linarith

/-- For real `x` with `|x| ≤ 1`, `0 ≤ 1 - x ^ 2`. -/
theorem one_sub_sq_nonneg_of_abs_le {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ 1 - x ^ 2 := by
  have := (sq_le_one_iff_abs_le_one x).2 hx
  linarith

/-- The interval from `-π` to `π` has positive length: `0 < π - -π`. -/
theorem pi_sub_neg_pi_pos : (0 : ℝ) < π - -π := by linarith [Real.pi_pos]

/-- For real numbers with `a ≤ M`, `0 ≤ a`, `0 ≤ x` and `0 ≤ z`, `a * x * z ≤ M * (x ^ 2 + z ^ 2)`.
-/
theorem mul_mul_le_mul_sq_add_sq {a M x z : ℝ} (hA : a ≤ M) (ha : 0 ≤ a) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    a * x * z ≤ M * (x ^ 2 + z ^ 2) := by
  have hM : 0 ≤ M := ha.trans hA
  have h1 : a * x * z ≤ M * x * z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hx) hz
  have h2 : x * z ≤ x ^ 2 + z ^ 2 := by nlinarith [sq_nonneg (x - z)]
  calc a * x * z ≤ M * x * z := h1
    _ = M * (x * z) := by ring
    _ ≤ M * (x ^ 2 + z ^ 2) := mul_le_mul_of_nonneg_left h2 hM

/-- For complex numbers `f` and `u`, the real part of `2 * (f * conj u) + (-1) * (u * conj u)` is at
most the real part of the real number `‖f‖ ^ 2` viewed in `ℂ`. -/
theorem re_two_mul_conj_sub_le (f u : ℂ) :
    (2 * (f * (starRingEnd ℂ) u) + (-1) * (u * (starRingEnd ℂ) u)).re ≤ ((‖f‖ ^ 2 : ℝ) : ℂ).re := by
  rw [Complex.ofReal_re, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
  norm_num
  nlinarith [sq_nonneg (f.re - u.re), sq_nonneg (f.im - u.im)]

/-- For reals `a`, `b`, `x` and `c` with `0 ≤ c`, `a ^ 2 + (1 / 4) * b ^ 2 ≤ x` and `x ≤ c * a`, one
has `a ^ 2 + (1 / 4) * b ^ 2 ≤ c ^ 2`, `a ≤ c` and `b ≤ 2 * c`. -/
theorem sq_add_le_sq_of_le_mul {a b c : ℝ} (hc : 0 ≤ c) (x : ℝ)
    (hx : x ≤ c * a) (h : a ^ 2 + (1 / 4 : ℝ) * b ^ 2 ≤ x) :
    a ^ 2 + (1 / 4 : ℝ) * b ^ 2 ≤ c ^ 2 ∧ a ≤ c ∧ b ≤ 2 * c := by
  have hac : a ≤ c := by nlinarith
  have hfin : a ^ 2 + (1 / 4 : ℝ) * b ^ 2 ≤ c ^ 2 := by nlinarith
  refine ⟨hfin, hac, ?_⟩
  nlinarith

/-- Let `0 ≤ u`, `0 < r`, `0 < L`, `0 ≤ A`, `0 ≤ Ct` and `u ≤ cL / (1 + r)`. Then
`A * (u ^ 2 / r) + 8 * Ct * (u ^ 3 / L) ≤ (A * cL ^ 2 + 8 * Ct * cL ^ 3 / L) / (r * (1 + r) ^
2)`. The proof bounds `u ^ 2` and `u ^ 3` by the powers of `cL / (1 + r)` and uses `r / (1 + r) ≤
1` in the cubic term. -/
theorem sq_div_add_cube_div_le {u r L cL A Ct : ℝ} (hu : 0 ≤ u) (hr : 0 < r) (hL : 0 < L)
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct)
    (hucL : u ≤ cL / (1 + r)) :
    A * (u ^ 2 / r) + 8 * Ct * (u ^ 3 / L) ≤ (A * cL ^ 2 + 8 * Ct * cL ^ 3 / L) /
        (r * (1 + r) ^ 2) := by
  have h1r : 0 < 1 + r := by linarith
  have hcL : 0 ≤ cL := by
    have : 0 ≤ cL / (1 + r) := hu.trans hucL
    exact (div_nonneg_iff.1 this).elim (fun h ↦ h.1) (fun h ↦ by linarith [h.2])
  have hu2 : u ^ 2 ≤ cL ^ 2 / (1 + r) ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ hu hucL 2
  have hu3 : u ^ 3 ≤ cL ^ 3 / (1 + r) ^ 3 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ hu hucL 3
  have e1 : u ^ 2 / r ≤ cL ^ 2 / (r * (1 + r) ^ 2) := by
    rw [div_le_div_iff₀ hr (by positivity)]
    have := mul_le_mul_of_nonneg_right hu2 (le_of_lt (by positivity : (0 : ℝ) < r * (1 + r) ^ 2))
    calc u ^ 2 * (r * (1 + r) ^ 2) ≤ cL ^ 2 / (1 + r) ^ 2 * (r * (1 + r) ^ 2) := this
      _ = cL ^ 2 * r := by field_simp
  have e2 : u ^ 3 / L ≤ cL ^ 3 / L / (r * (1 + r) ^ 2) := by
    rw [div_div, div_le_div_iff₀ hL (by positivity)]
    have h3 : cL ^ 3 / (1 + r) ^ 3 * (L * (r * (1 + r) ^ 2)) ≤ cL ^ 3 * L := by
      rw [show cL ^ 3 / (1 + r) ^ 3 * (L * (r * (1 + r) ^ 2)) = cL ^ 3 * L * (r / (1 + r)) by
        field_simp]
      have : r / (1 + r) ≤ 1 := (div_le_one h1r).2 (by linarith)
      have : 0 ≤ cL ^ 3 * L := by positivity
      nlinarith
    calc u ^ 3 * (L * (r * (1 + r) ^ 2)) ≤ cL ^ 3 / (1 + r) ^ 3 * (L * (r * (1 + r) ^ 2)) :=
          mul_le_mul_of_nonneg_right hu3 (by positivity)
      _ ≤ cL ^ 3 * L := h3
  have e3 : (A * cL ^ 2 + 8 * Ct * cL ^ 3 / L) / (r * (1 + r) ^ 2) =
      A * (cL ^ 2 / (r * (1 + r) ^ 2)) + 8 * Ct * (cL ^ 3 / L / (r * (1 + r) ^ 2)) := by ring
  rw [e3]
  have := mul_le_mul_of_nonneg_left e1 hA
  have := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 8 * Ct)
  linarith

/-- For reals with `0 < y0 ^ 2 + y1 ^ 2`,
`(a0 * y0 + a1 * y1 + a2 * y2) ^ 2 / (y0 ^ 2 + y1 ^ 2 + y2 ^ 2) +
(a1 * y0 - a0 * y1) ^ 2 / (y0 ^ 2 + y1 ^ 2) ≤ a0 ^ 2 + a1 ^ 2 + a2 ^ 2`. In words, the squared
components of the vector `(a0, a1, a2)` along `(y0, y1, y2)` and along the orthogonal horizontal
direction `(-y1, y0, 0)` add up to at most its squared length. -/
theorem sq_div_add_sq_div_le (a0 a1 a2 y0 y1 y2 : ℝ) (hr : 0 < y0 ^ 2 + y1 ^ 2) :
    (a0 * y0 + a1 * y1 + a2 * y2) ^ 2 / (y0 ^ 2 + y1 ^ 2 + y2 ^ 2)
      + (a1 * y0 - a0 * y1) ^ 2 / (y0 ^ 2 + y1 ^ 2) ≤ a0 ^ 2 + a1 ^ 2 + a2 ^ 2 := by
  have hs : 0 < y0 ^ 2 + y1 ^ 2 + y2 ^ 2 := by positivity
  rw [div_add_div _ _ hs.ne' hr.ne', div_le_iff₀ (mul_pos hs hr)]
  nlinarith [sq_nonneg (a2 * (y0 ^ 2 + y1 ^ 2) - (a0 * y0 + a1 * y1) * y2)]

/-- For reals with `0 < r`, `0 ≤ m` and `0 ≤ u`, if `m * u ≤ r * v` then
`m ^ 2 / r ^ 2 * u ^ 2 ≤ v ^ 2`. -/
theorem sq_div_sq_mul_sq_le_sq {m u r v : ℝ} (hr : 0 < r) (hm : 0 ≤ m) (hu : 0 ≤ u)
    (h : m * u ≤ r * v) :
    m ^ 2 / r ^ 2 * u ^ 2 ≤ v ^ 2 := by
  have hsq : (m * u) ^ 2 ≤ (r * v) ^ 2 := pow_le_pow_left₀ (mul_nonneg hm hu) h 2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [hsq]

/-- For real numbers `t` and `s > 0`, `t ^ 2 ≤ s + t ^ 6 / s ^ 2`. This is
`sq_le_pow_six_div_sq_add` with the two summands exchanged. -/
theorem sq_le_add_pow_six_div_sq {t s : ℝ} (hs : 0 < s) : t ^ 2 ≤ s + t ^ 6 / s ^ 2 := by
  rw [add_comm]
  exact sq_le_pow_six_div_sq_add hs

/-- For real numbers, if `U ^ 2 ≤ 5 * F ^ 2`, `F ^ 2 ≤ C ^ 2` and `0 ≤ V`, then
`U ^ 2 ≤ 5 * C ^ 2 * (V + 1)`. -/
theorem sq_le_mul_add_one {U F C V : ℝ} (hu : U ^ 2 ≤ 5 * F ^ 2) (hf : F ^ 2 ≤ C ^ 2) (hV : 0 ≤ V) :
    U ^ 2 ≤ 5 * C ^ 2 * (V + 1) := by
  nlinarith [sq_nonneg C]

/-- Let `X ≥ 0`, `P ≥ 0` and `Q > 0` be reals. If `X ≤ (t * P + t⁻¹ * Q) / 2` for every `t > 0`,
then `X ^ 2 ≤ P * Q`. The proof takes `t = X / P` when `P > 0` and `t = Q / X` when `P = 0`. -/
theorem sq_le_mul_of_forall_pos_le {X P Q : ℝ} (hX : 0 ≤ X) (hP : 0 ≤ P) (hQ : 0 < Q)
    (h : ∀ t : ℝ, 0 < t → X ≤ (t * P + t⁻¹ * Q) / 2) : X ^ 2 ≤ P * Q := by
  refine le_of_not_gt fun hc ↦ ?_
  have hXp : 0 < X := by
    rcases hX.lt_or_eq with h1 | h1
    · exact h1
    · subst h1
      nlinarith [mul_nonneg hP hQ.le]
  rcases hP.lt_or_eq with hP1 | hP1
  · have ht : 0 < X / P := div_pos hXp hP1
    have h2 := h (X / P) ht
    have e1 : X / P * P = X := by field_simp
    have e2 : (X / P)⁻¹ * Q = P * Q / X := by
      rw [inv_div]
      field_simp
    rw [e1, e2] at h2
    have h3 : P * Q / X < X := by
      rw [div_lt_iff₀ hXp]
      nlinarith
    linarith
  · subst hP1
    have ht : 0 < Q / X := div_pos hQ hXp
    have h2 := h (Q / X) ht
    have e2 : (Q / X)⁻¹ * Q = X := by
      rw [inv_div]
      field_simp
    rw [e2] at h2
    linarith

/-- Let `R`, `n`, `q`, `w` be nonnegative reals. If `n ≤ s1 + s2`, `w ≤ D / (1 + R)` and
`s1 ^ 2 ≤ 3 * w ^ 2 * q`, then `n ^ 2 ≤ 6 * D ^ 2 / (1 + R) * q + 2 * s2 ^ 2`. The proof uses
`(s1 + s2) ^ 2 ≤ 2 * s1 ^ 2 + 2 * s2 ^ 2` and `(D / (1 + R)) ^ 2 ≤ D ^ 2 / (1 + R)`. -/
theorem sq_le_six_mul_div_add_sq {n s1 s2 q w D R : ℝ} (hR : 0 ≤ R) (hn : n ≤ s1 + s2) (hn0 : 0 ≤ n)
    (hq : 0 ≤ q) (hw0 : 0 ≤ w) (hw : w ≤ D / (1 + R)) (hf : s1 ^ 2 ≤ 3 * w ^ 2 * q) :
    n ^ 2 ≤ 6 * D ^ 2 / (1 + R) * q + 2 * s2 ^ 2 := by
  have hRpos : 0 < 1 + R := by linarith
  have h1 : w ^ 2 ≤ (D / (1 + R)) ^ 2 := pow_le_pow_left₀ hw0 hw 2
  have h2 : (D / (1 + R)) ^ 2 ≤ D ^ 2 / (1 + R) := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg D) hRpos (by nlinarith)
  have e2 : s1 ^ 2 ≤ 3 * (D ^ 2 / (1 + R)) * q :=
    hf.trans (mul_le_mul_of_nonneg_right (by linarith) hq)
  have e3 : 6 * D ^ 2 / (1 + R) * q = 2 * (3 * (D ^ 2 / (1 + R)) * q) := by ring
  have e1 : n ^ 2 ≤ (s1 + s2) ^ 2 := pow_le_pow_left₀ hn0 hn 2
  nlinarith [sq_nonneg (s1 - s2)]

/-- Let `D`, `n`, `q`, `w`, `v`, `s2` be nonnegative reals and `g` a real. If `n ≤ s1 + s2`, `w ≤
D`, `g ≤ D`,
`s1 ^ 2 ≤ 3 * w ^ 2 * q` and `s2 ≤ g * v`, then `n ^ 2 ≤ 6 * D ^ 2 * (v ^ 2 + q)`. The proof uses
`(s1 + s2) ^ 2 ≤ 2 * s1 ^ 2 + 2 * s2 ^ 2`. -/
theorem sq_le_six_mul_sq_mul_add {n s1 s2 q v w g D : ℝ} (hD : 0 ≤ D) (hn : n ≤ s1 + s2)
    (hn0 : 0 ≤ n)
    (hq : 0 ≤ q) (hw0 : 0 ≤ w) (hw : w ≤ D) (hf : s1 ^ 2 ≤ 3 * w ^ 2 * q) (hg : g ≤ D)
    (hv : 0 ≤ v) (h2 : s2 ≤ g * v) (hs2 : 0 ≤ s2) : n ^ 2 ≤ 6 * D ^ 2 * (v ^ 2 + q) := by
  have e1 : n ^ 2 ≤ (s1 + s2) ^ 2 := pow_le_pow_left₀ hn0 hn 2
  have e2 : s1 ^ 2 ≤ 3 * D ^ 2 * q :=
    hf.trans (mul_le_mul_of_nonneg_right (by nlinarith) hq)
  have e3 : s2 ≤ D * v := h2.trans (mul_le_mul_of_nonneg_right hg hv)
  have e4 : (s1 + s2) ^ 2 ≤ 2 * s1 ^ 2 + 2 * s2 ^ 2 := by nlinarith [sq_nonneg (s1 - s2)]
  have e5 : s2 ^ 2 ≤ (D * v) ^ 2 := pow_le_pow_left₀ hs2 e3 2
  nlinarith [sq_nonneg (D * v), mul_nonneg (sq_nonneg D) (sq_nonneg v)]

/-- Let `m`, `c`, `a`, `Z`, `sE`, `φ'` be nonnegative reals, `V` a real and `K > 0`. If `E ≤ Z ^ 2`,
`sE ≤ Z`, `V ≤ Z`, `φ' ≤ φ`, `Z ≤ K * φ` and `s ^ 2 ≤ m * E + 2 * c * (φ' + a * V) * sE`, then
`s ^ 2 ≤ K ^ 2 * φ ^ 2 * (m + 2 * c * a + 2 * c / K)`. The proof replaces `E`, `sE`, `V`, `φ'` by
their bounds and then `Z` by `K * φ`. -/
theorem sq_le_sq_mul_sq_mul_add {s E sE V φ' φ Z m c a K : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hK : 0 < K) (hZ0 : 0 ≤ Z) (hsE0 : 0 ≤ sE) (hφ'0 : 0 ≤ φ')
    (hE : E ≤ Z ^ 2) (hsE : sE ≤ Z) (hV : V ≤ Z) (hφ' : φ' ≤ φ) (hZ : Z ≤ K * φ)
    (hs : s ^ 2 ≤ m * E + 2 * c * (φ' + a * V) * sE) :
    s ^ 2 ≤ K ^ 2 * φ ^ 2 * (m + 2 * c * a + 2 * c / K) := by
  have hφ0 : 0 ≤ φ := hφ'0.trans hφ'
  have h1 : m * E ≤ m * Z ^ 2 := mul_le_mul_of_nonneg_left hE hm
  have h2 : (φ' + a * V) * sE ≤ (φ + a * Z) * Z :=
    mul_le_mul (add_le_add hφ' (mul_le_mul_of_nonneg_left hV ha)) hsE hsE0
      (add_nonneg hφ0 (mul_nonneg ha hZ0))
  have hZ2 : Z ^ 2 ≤ (K * φ) ^ 2 := pow_le_pow_left₀ hZ0 hZ 2
  have hφZ : φ * Z ≤ φ * (K * φ) := mul_le_mul_of_nonneg_left hZ hφ0
  have e : K ^ 2 * φ ^ 2 * (m + 2 * c * a + 2 * c / K) =
      m * (K * φ) ^ 2 + 2 * c * (φ * (K * φ) + a * (K * φ) ^ 2) := by
    field_simp
    ring
  rw [e]
  calc s ^ 2 ≤ m * Z ^ 2 + 2 * c * ((φ + a * Z) * Z) := by
        nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg zero_le_two hc)]
    _ = m * Z ^ 2 + 2 * c * (φ * Z + a * Z ^ 2) := by ring
    _ ≤ m * (K * φ) ^ 2 + 2 * c * (φ * (K * φ) + a * (K * φ) ^ 2) := by
        gcongr

/-- Let `c`, `E`, `q`, `B`, `a`, `v`, `s` be nonnegative reals and `ρ` a real with `c ≤ cm`,
`E ≤ (2 * ρ) ^ 2`, `q ≤ qm`, `B ≤ Bm`, `v ≤ 2 * ρ` and `s ≤ 2 * ρ`. If
`S ^ 2 ≤ c * E + 2 * q * (B + a * v) * s` and
`4 * cm * ρ ^ 2 + 4 * qm * ρ * (Bm + 2 * a * ρ) ≤ r ^ 2`, then `S ^ 2 ≤ r ^ 2`. The proof replaces
each factor by its upper bound. -/
theorem sq_le_sq_of_sq_le_add {S c cm E q qm B Bm a v s ρ r : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ cm)
    (hE0 : 0 ≤ E)
    (hE : E ≤ (2 * ρ) ^ 2) (hq0 : 0 ≤ q) (hq : q ≤ qm) (hB0 : 0 ≤ B) (hB : B ≤ Bm) (ha : 0 ≤ a)
    (hv0 : 0 ≤ v) (hv : v ≤ 2 * ρ) (hs0 : 0 ≤ s) (hs : s ≤ 2 * ρ)
    (hS : S ^ 2 ≤ c * E + 2 * q * (B + a * v) * s)
    (hsmall : 4 * cm * ρ ^ 2 + 4 * qm * ρ * (Bm + 2 * a * ρ) ≤ r ^ 2) : S ^ 2 ≤ r ^ 2 := by
  have h1 : c * E ≤ cm * (2 * ρ) ^ 2 := mul_le_mul hc hE hE0 (hc0.trans hc)
  have h2 : B + a * v ≤ Bm + a * (2 * ρ) := add_le_add hB (mul_le_mul_of_nonneg_left hv ha)
  have h3 : 2 * q * (B + a * v) ≤ 2 * qm * (Bm + a * (2 * ρ)) :=
    mul_le_mul (by linarith) h2 (add_nonneg hB0 (mul_nonneg ha hv0)) (by linarith)
  have h4 : 2 * q * (B + a * v) * s ≤ 2 * qm * (Bm + a * (2 * ρ)) * (2 * ρ) :=
    mul_le_mul h3 hs hs0 (mul_nonneg (by linarith) (by nlinarith))
  have e1 : cm * (2 * ρ) ^ 2 = 4 * cm * ρ ^ 2 := by ring
  have e2 : 2 * qm * (Bm + a * (2 * ρ)) * (2 * ρ) = 4 * qm * ρ * (Bm + 2 * a * ρ) := by ring
  linarith

/-- For real numbers, if `U ^ 2 ≤ 5 * F ^ 2`, `F ^ 2 ≤ C ^ 2` and `0 ≤ V`, then
`U ^ 2 * V ≤ 5 * C ^ 2 * (V + 1)`. -/
theorem sq_mul_le_mul_add_one {U F C V : ℝ} (hu : U ^ 2 ≤ 5 * F ^ 2) (hf : F ^ 2 ≤ C ^ 2)
    (hV : 0 ≤ V) :
    U ^ 2 * V ≤ 5 * C ^ 2 * (V + 1) := by
  have h0 : 0 ≤ U ^ 2 := sq_nonneg U
  nlinarith [sq_nonneg C]

/-- Let `D`, `A`, `S`, `c`, `ρ` be nonnegative reals, `1 ≤ r`, `ρ ≤ 1 / r` and `s ≤ S * (A + √D)`.
Then `c * (A ^ 2 * s * ρ) ≤ D / 8 + (c * S * A ^ 3 + 2 * c ^ 2 * S ^ 2 * A ^ 4) / r`. The proof
inserts the bound on `s` and uses `b * √D ≤ D / 8 + 2 * b ^ 2` with `b = c * S * A ^ 2 * ρ`. -/
theorem sq_mul_mul_le_div_eight_add {D A r s S c ρ : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hS : 0 ≤ S) (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / r) (hso : s ≤ S * (A + √D)) :
    c * (A ^ 2 * s * ρ) ≤ D / 8 + (c * S * A ^ 3 + 2 * c ^ 2 * S ^ 2 * A ^ 4) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hir : 1 / r ≤ 1 := by rw [div_le_one hr0]; exact hr
  have hρ1 : ρ ≤ 1 := hρ.trans hir
  have ht := Real.sqrt_nonneg D
  have hD2 : √D ^ 2 = D := Real.sq_sqrt hD
  have step1 : c * (A ^ 2 * s * ρ) ≤ c * (A ^ 2 * ρ) * (S * (A + √D)) := by
    calc c * (A ^ 2 * s * ρ) = c * (A ^ 2 * ρ) * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hso (by positivity)
  set b := c * S * A ^ 2 * ρ
  have hb : b * √D ≤ √D ^ 2 / 8 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (√D - 4 * b)]
  have hρ2 : ρ ^ 2 ≤ 1 / r := by nlinarith
  have hb2 : b ^ 2 ≤ c ^ 2 * S ^ 2 * A ^ 4 / r := by
    calc b ^ 2 = c ^ 2 * S ^ 2 * A ^ 4 * ρ ^ 2 := by ring
      _ ≤ c ^ 2 * S ^ 2 * A ^ 4 * (1 / r) := mul_le_mul_of_nonneg_left hρ2 (by positivity)
      _ = c ^ 2 * S ^ 2 * A ^ 4 / r := by ring
  have h3 : c * S * A ^ 3 * ρ ≤ c * S * A ^ 3 * (1 / r) :=
    mul_le_mul_of_nonneg_left hρ (by positivity)
  calc c * (A ^ 2 * s * ρ) ≤ c * (A ^ 2 * ρ) * (S * (A + √D)) := step1
    _ = c * S * A ^ 3 * ρ + b * √D := by ring
    _ ≤ c * S * A ^ 3 * (1 / r) + (√D ^ 2 / 8 + 2 * (c ^ 2 * S ^ 2 * A ^ 4 / r)) := by linarith
    _ = _ := by rw [hD2]; ring

/-- Let `1 ≤ u`, `0 < emin`, `emin ≤ e`, `0 ≤ f`, `f ≤ 12 * D / u ^ 2` and `a ^ 2 / u ^ 2 ≤ E` be
real numbers. Then `f ^ 2 * a ^ 2 / e ≤ 144 * D ^ 2 / emin * E`. The proof shows
`f ^ 2 * u ^ 2 ≤ 144 * D ^ 2` from `f * u ^ 2 ≤ 12 * D` and `u ^ 2 ≤ u ^ 4`, and writes
`f ^ 2 * a ^ 2 = (f ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2)`. -/
theorem sq_mul_sq_div_le_of_le {f a u E e emin D : ℝ} (hu1 : 1 ≤ u) (hemin : 0 < emin)
    (he : emin ≤ e)
    (hf0 : 0 ≤ f) (hfd : f ≤ 12 * D / u ^ 2) (hEa : a ^ 2 / u ^ 2 ≤ E) :
    f ^ 2 * a ^ 2 / e ≤ 144 * D ^ 2 / emin * E := by
  have hu0 : 0 < u := by linarith
  have hu' : u ≠ 0 := hu0.ne'
  have hu2 : 0 < u ^ 2 := by positivity
  have h0 : f * u ^ 2 ≤ 12 * D := by rwa [le_div_iff₀ hu2] at hfd
  have h1 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have h2 : (f * u ^ 2) ^ 2 ≤ (12 * D) ^ 2 := pow_le_pow_left₀ (by positivity) h0 2
  have hf2 : f ^ 2 * u ^ 2 ≤ 144 * D ^ 2 := by
    nlinarith only [h2, mul_le_mul_of_nonneg_left h1 (sq_nonneg f)]
  have hq : f ^ 2 * a ^ 2 / e ≤ f ^ 2 * a ^ 2 / emin := div_le_div_of_nonneg_left (by
    positivity) hemin he
  have e1 : f ^ 2 * a ^ 2 = (f ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2) := by
    field_simp
  have h3 : (f ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2) ≤ 144 * D ^ 2 * E :=
    mul_le_mul hf2 hEa (by positivity) (by positivity)
  calc f ^ 2 * a ^ 2 / e ≤ f ^ 2 * a ^ 2 / emin := hq
    _ ≤ 144 * D ^ 2 * E / emin := by rw [e1]; exact div_le_div_of_nonneg_right h3 hemin.le
    _ = 144 * D ^ 2 / emin * E := by ring

/-- For real numbers, `(a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)`. -/
theorem sq_sum_five_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
      sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)]

/-- Young-type bound: for reals `a ≥ 0`, `b ≥ 0` and `ℓ > 0`, `√a * √b ≤ (1 / 2) * (ℓ * b + a / ℓ)`.
This is `two_mul_mul_le_mul_sq_add` for `√b` and `√a`, divided by `2`. -/
theorem sqrt_mul_sqrt_le_half_mul_add (a b ℓ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hℓ : 0 < ℓ) :
    Real.sqrt a * Real.sqrt b ≤ (1 / 2) * (ℓ * b + a / ℓ) := by
  have h := two_mul_mul_le_mul_sq_add (Real.sqrt b) (Real.sqrt a) ℓ hℓ
  rw [Real.sq_sqrt hb, Real.sq_sqrt ha] at h
  linarith

/-- Let `E ≥ 0`, `a ≥ 0`, `n > 0`, `wm ≥ 0`, `cl ≤ gc`, `n ^ 2 * W ≤ ww` and `n * Mn ≤ wm` be real
numbers. If `gc * E - W * a ^ 2 - Mn * a * √E ≤ LD`, then
`(cl - wm) * E - (ww + wm / 4) * (a ^ 2 / n ^ 2) ≤ LD`. The proof writes `a = n * (a / n)` and
bounds the cross term by `(a / n) * √E ≤ (a / n) ^ 2 / 4 + E`. -/
theorem sub_le_of_sub_mul_sqrt_le {E a n LD gc cl W Mn ww wm : ℝ} (hE : 0 ≤ E) (ha : 0 ≤ a)
    (hn : 0 < n)
    (hwm : 0 ≤ wm) (h2 : gc * E - W * a ^ 2 - Mn * a * Real.sqrt E ≤ LD) (hcl : cl ≤ gc)
    (hW : n ^ 2 * W ≤ ww) (hM : n * Mn ≤ wm) :
    (cl - wm) * E - (ww + wm / 4) * (a ^ 2 / n ^ 2) ≤ LD := by
  have hn0 : n ≠ 0 := hn.ne'
  have hq : 0 ≤ a / n := div_nonneg ha hn.le
  have hs : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hs2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  have han : a = n * (a / n) := by field_simp
  have hq2 : a ^ 2 / n ^ 2 = (a / n) ^ 2 := (div_pow a n 2).symm
  have e1 : W * a ^ 2 = (n ^ 2 * W) * (a / n) ^ 2 := by
    conv_lhs => rw [han]
    ring
  have e2 : Mn * a * Real.sqrt E = (n * Mn) * (a / n) * Real.sqrt E := by
    conv_lhs => rw [han]
    ring
  have k1 : (n ^ 2 * W) * (a / n) ^ 2 ≤ ww * (a / n) ^ 2 :=
      mul_le_mul_of_nonneg_right hW (sq_nonneg _)
  have k2 : (n * Mn) * (a / n) * Real.sqrt E ≤ wm * (a / n) * Real.sqrt E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hq) hs
  have k3 : (a / n) * Real.sqrt E ≤ (a / n) ^ 2 / 4 + E := by
    nlinarith [sq_nonneg (a / n / 2 - Real.sqrt E)]
  have k4 : wm * ((a / n) * Real.sqrt E) ≤ wm * ((a / n) ^ 2 / 4 + E) :=
      mul_le_mul_of_nonneg_left k3 hwm
  have k5 : cl * E ≤ gc * E := mul_le_mul_of_nonneg_right hcl hE
  rw [hq2]
  rw [e1, e2] at h2
  nlinarith [k1, k2, k4, k5]

/-- Let `c1`, `c2`, `c3`, `c4` be real numbers that are at most `K`, with `c1`, `c3`, `c4`
nonnegative, and let `S1`, `S2`, `S3`, `S4` be nonnegative real numbers. Then
`c1 * S2 * S1 + c2 * S1 ^ 2 + c3 * S4 * S1 + c4 * S3 * S1 ≤ 4 * K * (S1 ^ 2 + S2 ^ 2 + S3 ^ 2 + S4 ^
2)`. The proof bounds each mixed term with `c * x * z ≤ K * (x ^ 2 + z ^ 2)`, valid for `0 ≤ c`, `c
≤ K` and nonnegative `x`, `z`. -/
theorem sum_four_mul_mul_le_sum_sq {c1 c2 c3 c4 K S1 S2 S3 S4 : ℝ} (h1 : 0 ≤ c1)
    (h3 : 0 ≤ c3) (h4 : 0 ≤ c4)
    (k1 : c1 ≤ K) (k2 : c2 ≤ K) (k3 : c3 ≤ K) (k4 : c4 ≤ K)
    (s1 : 0 ≤ S1) (s2 : 0 ≤ S2) (s3 : 0 ≤ S3) (s4 : 0 ≤ S4) :
    c1 * S2 * S1 + c2 * S1 ^ 2 + c3 * S4 * S1 + c4 * S3 * S1 ≤ 4 * K *
        (S1 ^ 2 + S2 ^ 2 + S3 ^ 2 + S4 ^ 2) := by
  have hK : 0 ≤ K := le_trans h1 k1
  have pr : ∀ {c x z : ℝ}, 0 ≤ c → c ≤ K → 0 ≤ x → 0 ≤ z → c * x * z ≤ K * (x ^ 2 + z ^ 2) := by
    intro c x z hc hcK hx hz
    have hxz : x * z ≤ x ^ 2 + z ^ 2 := by nlinarith [sq_nonneg (x - z)]
    calc c * x * z = c * (x * z) := by ring
      _ ≤ K * (x * z) := mul_le_mul_of_nonneg_right hcK (mul_nonneg hx hz)
      _ ≤ K * (x ^ 2 + z ^ 2) := mul_le_mul_of_nonneg_left hxz hK
  have t1 := pr h1 k1 s2 s1
  have t3 := pr h3 k3 s4 s1
  have t4 := pr h4 k4 s3 s1
  have t2 : c2 * S1 ^ 2 ≤ K * S1 ^ 2 := mul_le_mul_of_nonneg_right k2 (sq_nonneg _)
  nlinarith [sq_nonneg S1, sq_nonneg S2, sq_nonneg S3, sq_nonneg S4]

/-- For `0 < w`, a complex `z`, `d : Fin k → ℂ` and `κ : Fin k → ℝ`,
`∑ i, κ i * (z * conj (d i)).re ≤ w * ‖z‖ ^ 2 + (4 * w)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ‖d i‖ ^
2`. The proof bounds the left side by `‖z‖ * ∑ i, |κ i| * ‖d
i‖`, then uses Young's inequality and the Cauchy-Schwarz inequality. -/
theorem sum_mul_re_mul_conj_le_young {k : ℕ} {w : ℝ} (hw : 0 < w) (z : ℂ) (d : Fin k → ℂ)
    (κ : Fin k → ℝ) :
    ∑ i, κ i * (z * starRingEnd ℂ (d i)).re
      ≤ w * ‖z‖ ^ 2 + (4 * w)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ‖d i‖ ^ 2 := by
  set S := ∑ i, |κ i| * ‖d i‖ with hS
  have h1 : ∑ i, κ i * (z * starRingEnd ℂ (d i)).re ≤ ‖z‖ * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    calc κ i * (z * starRingEnd ℂ (d i)).re ≤ |κ i * (z * starRingEnd ℂ (d i)).re| := le_abs_self _
      _ = |κ i| * |(z * starRingEnd ℂ (d i)).re| := abs_mul _ _
      _ ≤ |κ i| * ‖z * starRingEnd ℂ (d i)‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
      _ = ‖z‖ * (|κ i| * ‖d i‖) := by rw [norm_mul, Complex.norm_conj]; ring
  have h2 : S ^ 2 ≤ (∑ i, κ i ^ 2) * ∑ i, ‖d i‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ |κ i|) (fun i ↦ ‖d i‖)
    simpa only [sq_abs] using h
  have hw0 : w ≠ 0 := hw.ne'
  have h3 : ‖z‖ * S ≤ w * ‖z‖ ^ 2 + (4 * w)⁻¹ * S ^ 2 := by
    have e : w * ‖z‖ ^ 2 + (4 * w)⁻¹ * S ^ 2 - ‖z‖ * S = (4 * w)⁻¹ * (2 * w * ‖z‖ - S) ^ 2 := by
      field_simp
      ring
    have : 0 ≤ (4 * w)⁻¹ * (2 * w * ‖z‖ - S) ^ 2 := by positivity
    linarith
  have h4 : (4 * w)⁻¹ * S ^ 2 ≤ (4 * w)⁻¹ * ((∑ i, κ i ^ 2) * ∑ i, ‖d i‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [mul_assoc ((4 * w)⁻¹)]
  linarith

/-- Young's inequality with the weight `u / v`, for absolute values: for real `a`, `b` and `u > 0`,
`v > 0`, `2 * (|a| * |b|) ≤ a ^ 2 * u / v + b ^ 2 * v / u`. This is `two_mul_mul_le_mul_sq_add` for
`|a|`, `|b|` at `β = u / v`. -/
theorem two_abs_mul_le_sq_mul_div (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * (|a| * |b|) ≤ a ^ 2 * u / v + b ^ 2 * v / u := by
  have h := two_mul_mul_le_mul_sq_add |a| |b| (u / v) (div_pos hu hv)
  rwa [sq_abs, sq_abs, show b ^ 2 / (u / v) = b ^ 2 * v / u by field_simp,
    show u / v * a ^ 2 = a ^ 2 * u / v by ring] at h

/-- Weighted Young inequality for a product: for `t > 0` and real `a`, `b`,
`2 * a * b ≤ t * a ^ 2 + b ^ 2 / t`. This is `two_mul_mul_le_mul_sq_add` with the product written
`2 * a * b`. -/
theorem two_mul_le_mul_sq_add_div {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    2 * a * b ≤ t * a ^ 2 + b ^ 2 / t := by
  linarith [two_mul_mul_le_mul_sq_add a b t ht]

/-- If `0 < Y` and `X ^ 2 = Y * Z` for real numbers, then `2 * t * X ≤ t ^ 2 * Y + Z` for every real
`t`. -/
theorem two_mul_le_of_sq_eq_mul {t X Y Z : ℝ} (hY : 0 < Y) (hXYZ : X ^ 2 = Y * Z) :
    2 * t * X ≤ t ^ 2 * Y + Z := by
  have h : 0 ≤ Y * (t ^ 2 * Y + Z - 2 * t * X) := by nlinarith [sq_nonneg (t * Y - X)]
  have := (mul_nonneg_iff_of_pos_left hY).1 h
  linarith

/-- Young's inequality with a weight: for real `a`, `b` and `c > 0`,
`2 * (a * b) ≤ c * a ^ 2 + c⁻¹ * b ^ 2`. This is `two_mul_mul_le_mul_sq_add` with the quotient
written `c⁻¹ * b ^ 2`. -/
theorem two_mul_le_mul_sq_add_inv_mul_sq {a b c : ℝ} (hc : 0 < c) :
    2 * (a * b) ≤ c * a ^ 2 + c⁻¹ * b ^ 2 := by
  simpa only [div_eq_inv_mul] using two_mul_mul_le_mul_sq_add a b c hc

/-- If `E0 ≤ Qh`, `E1 ≤ Qh` and `N0`, `N1`, `x` are nonnegative, then
`2 * E0 * N0 * x + 2 * E1 * N1 * x ≤ 2 * Qh * (N0 + N1) * x`. -/
theorem two_mul_mul_add_le_of_le {E0 E1 Qh N0 N1 x : ℝ} (h0 : E0 ≤ Qh) (h1 : E1 ≤ Qh) (hN0 : 0 ≤ N0)
    (hN1 : 0 ≤ N1)
    (hx : 0 ≤ x) : 2 * E0 * N0 * x + 2 * E1 * N1 * x ≤ 2 * Qh * (N0 + N1) * x := by
  have a0 := mul_le_mul_of_nonneg_right h0 (mul_nonneg hN0 hx)
  have a1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hN1 hx)
  have e : 2 * Qh * (N0 + N1) * x = 2 * (Qh * (N0 * x)) + 2 * (Qh * (N1 * x)) := by ring
  have e0 : 2 * E0 * N0 * x = 2 * (E0 * (N0 * x)) := by ring
  have e1 : 2 * E1 * N1 * x = 2 * (E1 * (N1 * x)) := by ring
  rw [e, e0, e1]
  linarith

/-- A two-term Young inequality with weight `ϱ > 0`: for reals `g`, `a`, `b`, `W₁`, `W₂`,
`2 * g * (a * W₁ + b * W₂) ≤ (a ^ 2 + b ^ 2) * ϱ + g ^ 2 * ((W₁ ^ 2 + W₂ ^ 2) / ϱ)`. It is the sum
of `two_mul_mul_le_mul_sq_add` for `a`, `g * W₁` and for `b`, `g * W₂` at `β = ϱ`. -/
theorem two_mul_mul_add_mul_le {ϱ g a b W₁ W₂ : ℝ} (hϱ : 0 < ϱ) :
    2 * g * (a * W₁ + b * W₂) ≤ (a ^ 2 + b ^ 2) * ϱ + g ^ 2 * ((W₁ ^ 2 + W₂ ^ 2) / ϱ) := by
  have h1 := two_mul_mul_le_mul_sq_add a (g * W₁) ϱ hϱ
  have h2 := two_mul_mul_le_mul_sq_add b (g * W₂) ϱ hϱ
  have e : g ^ 2 * ((W₁ ^ 2 + W₂ ^ 2) / ϱ) = (g * W₁) ^ 2 / ϱ + (g * W₂) ^ 2 / ϱ := by ring
  linarith

/-- For real `a`, `b` and `t > 0`, `2 * a * b - a ^ 2 / t ≤ t * b ^ 2`. This is Young's inequality
`2 * a * b ≤ t * b ^ 2 + a ^ 2 / t` (`two_mul_mul_le_mul_sq_add`) with one term moved to the left.
-/
theorem two_mul_sub_sq_div_le {t a b : ℝ} (ht : 0 < t) :
    2 * a * b - a ^ 2 / t ≤ t * b ^ 2 := by
  linarith [two_mul_mul_le_mul_sq_add b a t ht]

/-- For complex numbers `f` and `u`, `2 * (f * conj u).re - ‖u‖ ^ 2 ≤ ‖f‖ ^ 2`. -/
theorem two_re_mul_conj_sub_le (f u : ℂ) : 2 * (f * (starRingEnd ℂ) u).re - ‖u‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := Complex.normSq_nonneg (f - u)
  rw [Complex.normSq_sub] at h
  rw [Complex.sq_norm, Complex.sq_norm]
  linarith

/-- Young-type bound: for reals `x ≥ 0`, `y ≥ 0` and `c > 0`, `2 * (√x * √y) ≤ c * x + y / c`. This
is `two_mul_mul_le_mul_sq_add` for `√x` and `√y`. -/
theorem two_sqrt_mul_le (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 < c) :
    2 * (Real.sqrt x * Real.sqrt y) ≤ c * x + y / c := by
  have h := two_mul_mul_le_mul_sq_add (Real.sqrt x) (Real.sqrt y) c hc
  rwa [Real.sq_sqrt hx, Real.sq_sqrt hy] at h

/-- For real `a`, `b` and `0 < l`, `a * b ≤ l * a ^ 2 + b ^ 2 / (4 * l)`. This is Young's inequality
`two_mul_mul_le_mul_sq_add` at `β = 2 * l`, divided by `2`. -/
theorem mul_le_mul_sq_add_sq_div_four_mul (a b l : ℝ) (hl : 0 < l) :
    a * b ≤ l * a ^ 2 + b ^ 2 / (4 * l) := by
  have h := two_mul_mul_le_mul_sq_add a b (2 * l) (by positivity)
  rw [show b ^ 2 / (2 * l) = 2 * (b ^ 2 / (4 * l)) by field_simp; ring] at h
  linarith

/-- For real numbers, `|c * a + d * b + f * e| ≤ |c| * |a| + |d| * |b| + |f| * |e|`. -/
theorem abs_mul_add_mul_add_mul_le (a b e c d f : ℝ) :
    |c * a + d * b + f * e| ≤ |c| * |a| + |d| * |b| + |f| * |e| :=
  (abs_add_le _ _).trans (add_le_add (abs_mul_add_mul_le a b c d) (by rw [abs_mul]))

open Classical in
/-- Let `x ≥ 0`, `c`, `pi`, `q1`, `q2` be real numbers (here `pi` is a variable, not the constant
`π`) and let `a`, `b`, `c'`, `d` be propositions. Then
`|c * pi * (if a then (if b then 0 else x * q1) else if c' then (if d then 0 else x * q2) else 0)| ≤
|c| * x * (pi ^ 2 + q1 ^ 2 + q2 ^ 2)`. The proof bounds the two nonzero cases `c * pi * (x *
q1)` and `c * pi * (x * q2)` with `|c * (p * q)| ≤ |c| * (p ^ 2 + q ^ 2)`. -/
theorem abs_mul_ite_le_mul_add_sq {a b c' d : Prop} {x pi q1 q2 c : ℝ} (hX : 0 ≤ x) :
    |c * pi * (if a then (if b then 0 else x * q1) else if c' then (if d then 0 else x * q2) else
        0)|
      ≤ |c| * x * (pi ^ 2 + q1 ^ 2 + q2 ^ 2) := by
  have h0 : 0 ≤ |c| * x * (pi ^ 2 + q1 ^ 2 + q2 ^ 2) :=
    mul_nonneg (mul_nonneg (abs_nonneg c) hX) (by positivity)
  have k1 : |c * pi * (x * q1)| ≤ |c| * x * (pi ^ 2 + q1 ^ 2 + q2 ^ 2) := by
    have := abs_mul_mul_le_mul_add_sq (c := c) (p := pi) (q := q1)
    rw [show c * pi * (x * q1) = x * (c * (pi * q1)) by ring, abs_mul, abs_of_nonneg hX]
    nlinarith [mul_le_mul_of_nonneg_left this hX, mul_nonneg (mul_nonneg (abs_nonneg c) hX)
        (sq_nonneg q2)]
  have k2 : |c * pi * (x * q2)| ≤ |c| * x * (pi ^ 2 + q1 ^ 2 + q2 ^ 2) := by
    have := abs_mul_mul_le_mul_add_sq (c := c) (p := pi) (q := q2)
    rw [show c * pi * (x * q2) = x * (c * (pi * q2)) by ring, abs_mul, abs_of_nonneg hX]
    nlinarith [mul_le_mul_of_nonneg_left this hX, mul_nonneg (mul_nonneg (abs_nonneg c) hX)
        (sq_nonneg q1)]
  split_ifs <;> simp_all

/-- For real numbers with `|c| ≤ M`, `0 ≤ a`, `0 ≤ a'`, `|a' - a| ≤ d` and `0 < t`,
`|c * a' ^ 2 - c * a ^ 2| ≤ (2 * M) * (1 + 1 / t) * d ^ 2 + (2 * M) * t * a ^ 2`. The proof factors
out `c` and bounds `|a' * a' - a * a|` by `(1 + 1 / t) * (d ^ 2 + d ^ 2) + t * (a ^ 2 + a ^ 2)`. -/
theorem abs_mul_sq_sub_mul_sq_le {c M a a' d t : ℝ} (hc : |c| ≤ M) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (hd : |a' - a| ≤ d)
    (ht : 0 < t) :
    |c * a' ^ 2 - c * a ^ 2| ≤ (2 * M) * (1 + 1 / t) * d ^ 2 + (2 * M) * t * a ^ 2 := by
  have h := abs_mul_sub_mul_le_add_sq (b := a) (b' := a') ha ha' hd hd ht
  have hM : 0 ≤ M := (abs_nonneg _).trans hc
  have eq : c * a' ^ 2 - c * a ^ 2 = c * (a' * a' - a * a) := by ring
  rw [eq, abs_mul]
  calc |c| * |a' * a' - a * a| ≤ M * ((1 + 1 / t) * (d ^ 2 + d ^ 2) + t * (a ^ 2 + a ^ 2)) :=
        mul_le_mul hc h (abs_nonneg _) hM
    _ = (2 * M) * (1 + 1 / t) * d ^ 2 + (2 * M) * t * a ^ 2 := by ring

/-- For a natural number `k` and reals `x`, `x'` with `|x| ≤ 1` and `|x'| ≤ 1`:
`|(1 - x ^ 2) ^ k - (1 - x' ^ 2) ^ k| ≤ 2 * k * |x - x'|`. The proof uses
`|a ^ k - b ^ k| ≤ |a - b| * k * max |a| |b| ^ (k - 1)` with `a = 1 - x ^ 2` and `b = 1 - x' ^ 2`,
which lie between `0` and `1`, and `|a - b| ≤ 2 * |x - x'|`. -/
theorem abs_one_sub_sq_pow_sub_le (k : ℕ) {x x' : ℝ} (hx : |x| ≤ 1) (hx' : |x'| ≤ 1) :
    |(1 - x ^ 2) ^ k - (1 - x' ^ 2) ^ k| ≤ 2 * k * |x - x'| := by
  have h := abs_pow_sub_pow_le (1 - x ^ 2) (1 - x' ^ 2) k
  have h0 := one_sub_sq_nonneg_of_abs_le hx
  have h0' := one_sub_sq_nonneg_of_abs_le hx'
  have hm : max |1 - x ^ 2| |1 - x' ^ 2| ^ (k - 1) ≤ 1 := by
    refine pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) (max_le ?_ ?_)
    · rw [abs_of_nonneg h0]
      exact one_sub_sq_le_one x
    · rw [abs_of_nonneg h0']
      exact one_sub_sq_le_one x'
  have hd : |(1 - x ^ 2) - (1 - x' ^ 2)| ≤ 2 * |x - x'| := by
    rw [show (1 - x ^ 2) - (1 - x' ^ 2) = (x' - x) * (x' + x) by ring, abs_mul, abs_sub_comm x' x]
    have : |x' + x| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    have := abs_nonneg (x - x')
    nlinarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc _ ≤ |(1 - x ^ 2) - (1 - x' ^ 2)| * (k : ℝ) * max |1 - x ^ 2| |1 - x' ^ 2| ^ (k - 1) := h
    _ ≤ (2 * |x - x'|) * (k : ℝ) * 1 := by
      have := abs_nonneg ((1 - x ^ 2) - (1 - x' ^ 2))
      have := pow_nonneg (le_max_of_le_left (abs_nonneg (1 - x ^ 2)) : (0 : ℝ) ≤ max |1 -
          x ^ 2| |1 - x' ^ 2|) (k - 1)
      gcongr
    _ = 2 * k * |x - x'| := by ring

/-- Let `0 < a`, `0 < s`, `0 ≤ C`, `0 ≤ r` and `K = a * (1 + s⁻¹) * C + a * s * (1 + s⁻¹) ^ 2 * C`.
Then `a * (C / (1 + s * r)) ≤ K / (1 + r)` and `a * s * (C / (1 + s * r) ^ 2) ≤ K / (1 + r) ^ 2`.
Both bounds follow from `1 + r ≤ (1 + s⁻¹) * (1 + s * r)`. -/
theorem div_one_add_mul_le_div_add {a s C r : ℝ} (ha : 0 < a) (hs : 0 < s) (hC : 0 ≤ C)
    (hr : 0 ≤ r) :
    a * (C / (1 + s * r)) ≤ (a * (1 + s⁻¹) * C + a * s * (1 + s⁻¹) ^ 2 * C) / (1 + r) ∧
      a * s * (C / (1 + s * r) ^ 2) ≤
        (a * (1 + s⁻¹) * C + a * s * (1 + s⁻¹) ^ 2 * C) / (1 + r) ^ 2 := by
  have hp : 0 < 1 + s * r := by positivity
  have hq : 0 < 1 + r := by positivity
  have hK : 0 < 1 + s⁻¹ := by positivity
  have key := one_add_le_one_add_inv_mul hs hr
  have sq : (1 + r) ^ 2 ≤ ((1 + s⁻¹) * (1 + s * r)) ^ 2 := pow_le_pow_left₀ hq.le key 2
  have hA : 0 ≤ a * (1 + s⁻¹) * C := by positivity
  have hB : 0 ≤ a * s * (1 + s⁻¹) ^ 2 * C := by positivity
  constructor
  · have step : a * (C / (1 + s * r)) ≤ a * (1 + s⁻¹) * C / (1 + r) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hp hq]
      have := mul_le_mul_of_nonneg_left key (mul_nonneg ha.le hC)
      nlinarith [this]
    refine step.trans ?_
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  · have hr1 : 1 ≤ 1 + r := by linarith
    have step : a * s * (C / (1 + s * r) ^ 2) ≤ a * s * (1 + s⁻¹) ^ 2 * C / (1 + r) ^ 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left sq (mul_nonneg (mul_nonneg ha.le hs.le) hC)
      nlinarith [this]
    refine step.trans ?_
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- Young-type inequality with a parameter: for real numbers `u`, `v` and `t > 0`,
`u * v ≤ (1 / 2) * t * u ^ 2 + (1 / 2) * v ^ 2 / t`. -/
theorem mul_le_half_mul_sq_add_div {u v t : ℝ} (ht : 0 < t) :
    u * v ≤ (1 / 2) * t * u ^ 2 + (1 / 2) * v ^ 2 / t := by
  have h := mul_le_sq_mul_add_sq_div (u := u) (v := v) (mul_pos two_pos ht)
  have e1 : u ^ 2 * (2 * t) / 4 = (1 / 2) * t * u ^ 2 := by ring
  have e2 : v ^ 2 / (2 * t) = (1 / 2) * v ^ 2 / t := by field_simp
  linarith

/-- For a natural number `k` and real `x` with `|x| ≤ 1`, `(1 - x ^ 2) ^ k ≤ 1`. -/
theorem one_sub_sq_pow_le_one (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) : (1 - x ^ 2) ^ k ≤ 1 :=
  pow_le_one₀ (one_sub_sq_nonneg_of_abs_le hx) (one_sub_sq_le_one x)

/-- For a natural number `k` and real `x` with `|x| ≤ 1`, `0 ≤ (1 - x ^ 2) ^ k`. -/
theorem one_sub_sq_pow_nonneg (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ (1 - x ^ 2) ^ k :=
  pow_nonneg (one_sub_sq_nonneg_of_abs_le hx) k

/-- Let `X`, `I`, `J` be nonnegative reals. If `X ≤ (t * (l * I + J / l) + t⁻¹ * (1 / (4 * π))) / 2`
for all `l > 0` and all `t > 0`, then `X ^ 2 ≤ (l * I + J / l) * (1 / (4 * π))` for every `l > 0`.
-/
theorem sq_le_mul_add_div_of_forall {X I J : ℝ} (hX : 0 ≤ X) (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (h : ∀ l : ℝ, 0 < l → ∀ t : ℝ, 0 < t → X ≤ (t * (l * I + J / l) + t⁻¹ * (1 / (4 * π))) / 2)
    (l : ℝ) (hl : 0 < l) : X ^ 2 ≤ (l * I + J / l) * (1 / (4 * π)) :=
  sq_le_mul_of_forall_pos_le hX (add_nonneg (mul_nonneg hl.le hI) (div_nonneg hJ hl.le))
    (by positivity) (h l hl)

/-- Let `W ≥ 0` and suppose `g i ≤ cg i * W` and `h i ≤ ch i * W` for all `i ∈ s`. Then
`∑ i ∈ s, (|u i| * g i + |v i| * h i) ≤ (∑ i ∈ s, (|u i| * |cg i| + |v i| * |ch i|)) *
W`, for real-valued functions on any index type. -/
theorem sum_abs_mul_add_le_sum_mul {ι : Type*} (s : Finset ι) (u v g h cg ch : ι → ℝ) (W : ℝ)
    (hW : 0 ≤ W)
    (hg : ∀ i ∈ s, g i ≤ cg i * W) (hh : ∀ i ∈ s, h i ≤ ch i * W) :
    ∑ i ∈ s, (|u i| * g i + |v i| * h i) ≤ (∑ i ∈ s, (|u i| * |cg i| + |v i| * |ch i|)) * W := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  calc |u i| * g i + |v i| * h i ≤ |u i| * (|cg i| * W) + |v i| * (|ch i| * W) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_abs_mul_of_le_mul hW (hg i hi)) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (le_abs_mul_of_le_mul hW (hh i hi)) (abs_nonneg _))
    _ = (|u i| * |cg i| + |v i| * |ch i|) * W := by ring

/-- For `0 < w`, `g : Fin 3 → Fin 3 → ℂ`, `d : Fin k → Fin 3 → Fin 3 → ℂ` and `κ : Fin k → ℝ`,
`∑ i, κ i * (∑ a, ∑ b, g a b * conj (d i a b)).re ≤ w * ∑ a, ∑ b, ‖g a b‖ ^ 2 + (4 * w)⁻¹ * (∑ i, κ
i ^ 2) * ∑ i, ∑ a, ∑ b, ‖d i a b‖ ^
2`. The proof exchanges the sums and applies the bound for a single complex number to each pair
`(a, b)`. -/
theorem sum_mul_re_sum_mul_conj_le {k : ℕ} {w : ℝ} (hw : 0 < w) (g : Fin 3 → Fin 3 → ℂ)
    (d : Fin k → Fin 3 → Fin 3 → ℂ) (κ : Fin k → ℝ) :
    ∑ i, κ i * (∑ a : Fin 3, ∑ b : Fin 3, g a b * starRingEnd ℂ (d i a b)).re
      ≤ w * ∑ a : Fin 3, ∑ b : Fin 3, ‖g a b‖ ^ 2
        + (4 * w)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ∑ a : Fin 3, ∑ b : Fin 3, ‖d i a b‖ ^ 2 := by
  have hL : ∑ i, κ i * (∑ a : Fin 3, ∑ b : Fin 3, g a b * starRingEnd ℂ (d i a b)).re
      = ∑ a : Fin 3, ∑ b : Fin 3, ∑ i, κ i * (g a b * starRingEnd ℂ (d i a b)).re := by
    simp only [Complex.re_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
  have hR : (4 * w)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ∑ a : Fin 3, ∑ b : Fin 3, ‖d i a b‖ ^ 2
      = ∑ a : Fin 3, ∑ b : Fin 3, (4 * w)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ‖d i a b‖ ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
  rw [hL, hR, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ ↦ sum_mul_re_mul_conj_le_young hw (g a b) (fun i ↦ d i a b) κ

/-- For reals with `0 ≤ ϱ` and `0 < z`, and with `q = ϱ ^ 2 + z ^ 2`,
`2 * g * (a * (-2 * ϱ ^ 2 / q) + b * (ϱ * (ϱ ^ 2 - z ^ 2) / (z * q))) + g ^ 2 * (-4 * ϱ * z ^ 2 / q
^ 2 + ϱ * (z ^ 4 - 4 * ϱ ^ 2 * z ^ 2 - ϱ ^ 4) / (z ^ 2 * q ^ 2)) ≤ (a ^ 2 + b ^ 2) * ϱ - 2 * (g ^ 2
/ q * ϱ)`. The proof applies the two-term Young inequality `2 * g * (a * W₁ + b * W₂) ≤ (a ^ 2 + b ^
2) * ϱ + g ^ 2 * ((W₁ ^ 2 + W₂ ^ 2) / ϱ)` to the two weights and uses that `(W₁ ^ 2 + W₂ ^ 2) /
ϱ` plus the coefficient of `g ^ 2` on the left equals `-2 * (ϱ / q)`; the case `ϱ =
0` is trivial. -/
theorem young_rational_weights_le {ϱ z g a b : ℝ} (hϱ : 0 ≤ ϱ) (hz : 0 < z) :
    2 * g * (a * (-2 * ϱ ^ 2 / (ϱ ^ 2 + z ^ 2)) + b * (ϱ * (ϱ ^ 2 - z ^ 2) / (z * (ϱ ^ 2 + z ^ 2))))
      + g ^ 2 * (-4 * ϱ * z ^ 2 / (ϱ ^ 2 + z ^ 2) ^ 2
        + ϱ * (z ^ 4 - 4 * ϱ ^ 2 * z ^ 2 - ϱ ^ 4) / (z ^ 2 * (ϱ ^ 2 + z ^ 2) ^ 2))
      ≤ (a ^ 2 + b ^ 2) * ϱ - 2 * (g ^ 2 / (ϱ ^ 2 + z ^ 2) * ϱ) := by
  rcases hϱ.eq_or_lt with h | h
  · subst h; simp
  have hq : 0 < ϱ ^ 2 + z ^ 2 := by positivity
  have key := two_mul_mul_add_mul_le (g := g) (a := a) (b := b) (W₁ := -2 * ϱ ^ 2 / (ϱ ^ 2 + z ^ 2))
    (W₂ := ϱ * (ϱ ^ 2 - z ^ 2) / (z * (ϱ ^ 2 + z ^ 2))) h
  have hid : ((-2 * ϱ ^ 2 / (ϱ ^ 2 + z ^ 2)) ^ 2 + (ϱ * (ϱ ^ 2 - z ^ 2) / (z * (ϱ ^ 2 + z ^ 2))) ^
      2) / ϱ
      + (-4 * ϱ * z ^ 2 / (ϱ ^ 2 + z ^ 2) ^ 2
        + ϱ * (z ^ 4 - 4 * ϱ ^ 2 * z ^ 2 - ϱ ^ 4) / (z ^ 2 * (ϱ ^ 2 + z ^ 2) ^ 2))
      = -2 * (ϱ / (ϱ ^ 2 + z ^ 2)) := by
    field_simp
    ring
  have : g ^ 2 / (ϱ ^ 2 + z ^ 2) * ϱ = g ^ 2 * (ϱ / (ϱ ^ 2 + z ^ 2)) := by ring
  rw [this]
  nlinarith [hid, key]

/-- For reals with `0 < ϱ`, and with `q = ϱ ^ 2 + z ^ 2`,
`2 * g * (a * ((z ^ 2 - ϱ ^ 2) / q) + b * (-2 * ϱ * z / q)) + g ^ 2 * (-4 * ϱ * z ^ 2 / q ^ 2 + -2 *
ϱ * (ϱ ^ 2 - z ^ 2) / q ^ 2) ≤ (a ^ 2 + b ^ 2 + g ^ 2 / ϱ ^ 2) * ϱ - 2 * (g ^ 2 / q *
ϱ)`. The proof applies the two-term Young inequality `2 * g * (a * W₁ + b * W₂) ≤ (a ^ 2 + b ^ 2) *
ϱ + g ^ 2 * ((W₁ ^ 2 + W₂ ^ 2) /
ϱ)` to the two weights, whose squares add up to `1`, and uses that the coefficient of `g ^ 2` on the
left equals `-2 * (ϱ / q)`. -/
theorem young_unit_rational_weights_le {ϱ z g a b : ℝ} (hϱ : 0 < ϱ) :
    2 * g * (a * ((z ^ 2 - ϱ ^ 2) / (ϱ ^ 2 + z ^ 2)) + b * (-2 * ϱ * z / (ϱ ^ 2 + z ^ 2)))
      + g ^ 2 * (-4 * ϱ * z ^ 2 / (ϱ ^ 2 + z ^ 2) ^ 2 + -2 * ϱ * (ϱ ^ 2 - z ^ 2) /
          (ϱ ^ 2 + z ^ 2) ^ 2)
      ≤ (a ^ 2 + b ^ 2 + g ^ 2 / ϱ ^ 2) * ϱ - 2 * (g ^ 2 / (ϱ ^ 2 + z ^ 2) * ϱ) := by
  have key := two_mul_mul_add_mul_le (g := g) (a := a) (b := b)
      (W₁ := (z ^ 2 - ϱ ^ 2) / (ϱ ^ 2 + z ^ 2))
    (W₂ := -2 * ϱ * z / (ϱ ^ 2 + z ^ 2)) hϱ
  have hid : (((z ^ 2 - ϱ ^ 2) / (ϱ ^ 2 + z ^ 2)) ^ 2 + (-2 * ϱ * z / (ϱ ^ 2 + z ^ 2)) ^ 2) / ϱ
      = ϱ / ϱ ^ 2 := by
    field_simp
    ring
  have hid2 : -4 * ϱ * z ^ 2 / (ϱ ^ 2 + z ^ 2) ^ 2 + -2 * ϱ * (ϱ ^ 2 - z ^ 2) / (ϱ ^ 2 + z ^ 2) ^ 2
      = -2 * (ϱ / (ϱ ^ 2 + z ^ 2)) := by
    field_simp
    ring
  have e1 : g ^ 2 / (ϱ ^ 2 + z ^ 2) * ϱ = g ^ 2 * (ϱ / (ϱ ^ 2 + z ^ 2)) := by ring
  have e2 : (a ^ 2 + b ^ 2 + g ^ 2 / ϱ ^ 2) * ϱ = (a ^ 2 + b ^ 2) * ϱ + g ^ 2 * (ϱ / ϱ ^ 2) := by
    ring
  rw [e1, e2, hid2]
  rw [hid] at key
  nlinarith [key]

/-- Let `X`, `I`, `J` be nonnegative reals. If `X ≤ (t * (l * I + J / l) + t⁻¹ * (1 / (4 * π))) / 2`
for all `l > 0` and all `t > 0`, then `X ^ 2 ≤ (1 / (2 * π)) * √I * √J`. The proof first optimizes
in `t` to get `X ^ 2 ≤ (l * I + J / l) * (1 / (4 * π))`, then takes `l = √J / √I`, with a separate
choice of `l` when `I = 0` or `J = 0`. -/
theorem sq_le_sqrt_mul_sqrt_of_forall {X I J : ℝ} (hX : 0 ≤ X) (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (h : ∀ l : ℝ, 0 < l → ∀ t : ℝ, 0 < t → X ≤ (t * (l * I + J / l) + t⁻¹ * (1 / (4 * π))) / 2) :
    X ^ 2 ≤ (1 / (2 * π)) * Real.sqrt I * Real.sqrt J := by
  have hk := sq_le_mul_add_div_of_forall hX hI hJ h
  have hpi : 0 < π := Real.pi_pos
  rcases hI.lt_or_eq with hI1 | hI1
  · rcases hJ.lt_or_eq with hJ1 | hJ1
    · have sI : 0 < Real.sqrt I := Real.sqrt_pos.mpr hI1
      have sJ : 0 < Real.sqrt J := Real.sqrt_pos.mpr hJ1
      have h2 := hk (Real.sqrt J / Real.sqrt I) (div_pos sJ sI)
      have eI : Real.sqrt I ^ 2 = I := Real.sq_sqrt hI
      have eJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ
      have e : ∀ a b : ℝ, 0 < a → 0 < b →
          (b / a * a ^ 2 + b ^ 2 / (b / a)) * (1 / (4 * π)) = (1 / (2 * π)) * a * b := by
        intro a b ha hb
        field_simp
        ring
      have e2 := e _ _ sI sJ
      rw [eI, eJ] at e2
      rw [e2] at h2
      exact h2
    · subst hJ1
      refine le_of_not_gt fun hc ↦ ?_
      have hX2 : 0 < X ^ 2 := lt_of_le_of_lt (by positivity) hc
      have hX0 : X ≠ 0 := fun h0 ↦ by simp [h0] at hX2
      have hl : 0 < 2 * π * X ^ 2 / (I + 1) := by positivity
      have h2 := hk _ hl
      have e : (2 * π * X ^ 2 / (I + 1) * I + 0 / (2 * π * X ^ 2 / (I + 1))) * (1 / (4 * π)) =
          X ^ 2 * (I / (2 * (I + 1))) := by
        field_simp
        ring
      rw [e] at h2
      have h3 : I / (2 * (I + 1)) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      nlinarith
  · subst hI1
    refine le_of_not_gt fun hc ↦ ?_
    have hX2 : 0 < X ^ 2 := lt_of_le_of_lt (by positivity) hc
    have hX0 : X ≠ 0 := fun h0 ↦ by simp [h0] at hX2
    have hl : 0 < (J + 1) / (4 * π * X ^ 2) := by positivity
    have h2 := hk _ hl
    have e : ((J + 1) / (4 * π * X ^ 2) * 0 + J / ((J + 1) / (4 * π * X ^ 2))) * (1 / (4 * π)) =
        X ^ 2 * (J / (J + 1)) := by
      field_simp
      ring
    rw [e] at h2
    have h3 : J / (J + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    nlinarith

/-- The inequality `0 < π - -π`, stated as a `Fact`. -/
theorem fact_zero_lt_pi_sub_neg_pi : Fact ((0 : ℝ) < π - -π) := ⟨pi_sub_neg_pi_pos⟩

end PDE.Analysis
