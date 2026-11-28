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

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.IntervalCases
public import PDE.Analysis.Scalar.Powers.Basic

set_option linter.style.header false

/-!
# Inequalities between real numbers: first lemmas

The lemmas bound squares, products, absolute values and fractions of real numbers: Young-type bounds
of a product by squares, bounds of a sum by the sum of the bounds, comparisons of two expressions
under sign conditions. Almost every proof is a short calculation closed by `nlinarith`, `linarith`,
`positivity` or `field_simp`, sometimes after a case split.

## Main results

* `PDE.Analysis.add_half_sq_add_half_sq_le`: For real `A ≥ 0` and `δ > 0`,
  `(A + δ / 2) ^ 2 + (δ / 2) ^ 2 ≤ (A + δ) ^ 2`.
* `PDE.Analysis.add_mul_sub_div_cancel`: For real `μ ≠ 0` and reals `x`, `y`,
  `x + μ * ((y - x) / μ) = y`.
* `PDE.Analysis.exists_pos_le_one_mul_le`: For every real `K` and every `δ > 0` there is a real `ε`
  with `0 < ε`, `ε ≤ 1` and `ε * K ≤ δ`.
* `PDE.Analysis.le_two_mul_of_half_sq_le`: For real `N` and `K ≥ 0`, if `(1 / 2) * N ^ 2 ≤ K * N`
  then `N ≤ 2 * K`.
* `PDE.Analysis.mul_one_add_mul_le_of_le`: For real `q ≥ 0`, `0 ≤ a ≤ A`, `0 ≤ c ≤ Cc` and
  `0 ≤ d ≤ D`, `q * (1 + a * 2 * c * d * q) ≤ q * (1 + A * 2 * Cc * D * q)`.
* `PDE.Analysis.one_add_mul_mul_le_of_le`: For real `a ≥ 0`, `0 ≤ x ≤ X` and `0 ≤ y ≤ Y`,
  `1 + a * x * y ≤ 1 + a * X * Y`.
* `PDE.Analysis.abs_add_mul_le_add_abs_mul`: If `|u| ≤ B₁` and `|v| ≤ B₂`, then
  `|u + a * v| ≤ B₁ + |a| * B₂` for every real `a`.
* `PDE.Analysis.abs_add_quarter_mul_add_le`: Let `0 ≤ D`, `0 ≤ M`, `0 ≤ B`, `0 ≤ fr`,
  `fr ≤ 3 * c ^ 2 * H ^ 2`, `0 ≤ cu`, `cu ≤ c ^ 2 * B ^ 2`,
  `|st| ≤ 3 * (3 * (c * B * dW * (c * B))) + M * hWv * B`, `dW ≤ D` and `hWv ≤ D * A` be real
  numbers. Then `|fr + (1 / 4) * cu + st| ≤ 3 * c ^ 2 * H ^ 2 + (c ^ 2 / 4 + 9 * c ^ 2 * D + M * D /
  2) * B ^ 2 + M * D / 2 * A ^ 2`.

There are 63 further lemmas of the same kind.

## Implementation notes

`two_mul_mul_le_mul_sq_add` is Young's inequality for a product, Mathlib's `two_mul_le_add_mul_sq`
in the notation of these modules. Its consequences include `mul_le_mul_sq_add_div_two` and
`add_sq_le_one_add_mul_sq` here and further forms in `PDE.Analysis.Scalar.Inequalities`.
`add_sq_le_two_mul_sq_add_two_mul_sq` is Mathlib's `add_sq_le` with the factor `2` multiplied out.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Real Filter Topology

namespace PDE.Analysis

/-- If `|u| ≤ B₁` and `|v| ≤ B₂`, then `|u + a * v| ≤ B₁ + |a| * B₂` for every real `a`. -/
theorem abs_add_mul_le_add_abs_mul {a u v B₁ B₂ : ℝ} (hu : |u| ≤ B₁) (hv : |v| ≤ B₂) :
    |u + a * v| ≤ B₁ + |a| * B₂ :=
  calc |u + a * v| ≤ |u| + |a * v| := abs_add_le _ _
    _ = |u| + |a| * |v| := by rw [abs_mul]
    _ ≤ B₁ + |a| * B₂ := add_le_add hu (mul_le_mul_of_nonneg_left hv (abs_nonneg a))

/-- Let `0 ≤ D`, `0 ≤ M`, `0 ≤ B`, `0 ≤ fr`, `fr ≤ 3 * c ^ 2 * H ^ 2`, `0 ≤ cu`,
`cu ≤ c ^ 2 * B ^ 2`, `|st| ≤ 3 * (3 * (c * B * dW * (c * B))) + M * hWv * B`, `dW ≤ D` and
`hWv ≤ D * A` be real numbers. Then
`|fr + (1 / 4) * cu + st| ≤ 3 * c ^ 2 * H ^ 2 + (c ^ 2 / 4 + 9 * c ^ 2 * D + M * D / 2) * B ^ 2 +
M * D / 2 * A ^ 2`. The proof uses the triangle inequality and `A * B ≤ (A ^ 2 + B ^ 2) / 2`. -/
theorem abs_add_quarter_mul_add_le {fr cu st H B dW hWv A c D M : ℝ} (hD0 : 0 ≤ D) (hM0 : 0 ≤ M)
    (hB0 : 0 ≤ B) (hfr0 : 0 ≤ fr) (hfr : fr ≤ 3 * c ^ 2 * H ^ 2) (hcu0 : 0 ≤ cu)
    (hcu : cu ≤ c ^ 2 * B ^ 2) (hst : |st| ≤ 3 * (3 * (c * B * dW * (c * B))) + M * hWv * B)
    (hdW : dW ≤ D) (hW : hWv ≤ D * A) :
    |fr + (1 / 4 : ℝ) * cu + st| ≤
      3 * c ^ 2 * H ^ 2 + (c ^ 2 / 4 + 9 * c ^ 2 * D + M * D / 2) * B ^ 2 + M * D / 2 * A ^ 2 := by
  have s1 : |fr + (1 / 4 : ℝ) * cu + st| ≤ |fr + (1 / 4 : ℝ) * cu| + |st| := abs_add_le _ _
  have s2 : |fr + (1 / 4 : ℝ) * cu| = fr + (1 / 4 : ℝ) * cu := abs_of_nonneg (by positivity)
  have q1 : 3 * (3 * (c * B * dW * (c * B))) ≤ 9 * (c ^ 2 * B ^ 2) * D := by
    have e : 3 * (3 * (c * B * dW * (c * B))) = 9 * (c ^ 2 * B ^ 2) * dW := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hdW (by positivity)
  have q2 : M * hWv * B ≤ M * (D * A) * B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hM0) hB0
  have q3 : A * B ≤ (A ^ 2 + B ^ 2) / 2 := by nlinarith [sq_nonneg (A - B)]
  have q4 : M * (D * A) * B ≤ M * D * ((A ^ 2 + B ^ 2) / 2) := by
    have e : M * (D * A) * B = M * D * (A * B) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left q3 (mul_nonneg hM0 hD0)
  have e2 : M * D * ((A ^ 2 + B ^ 2) / 2) = M * D / 2 * A ^ 2 + M * D / 2 * B ^ 2 := by ring
  have e3 : (c ^ 2 / 4 + 9 * c ^ 2 * D + M * D / 2) * B ^ 2
      = (1 / 4 : ℝ) * (c ^ 2 * B ^ 2) + 9 * (c ^ 2 * B ^ 2) * D + M * D / 2 * B ^ 2 := by ring
  rw [s2] at s1
  rw [e3]
  linarith

/-- For real numbers, if `|a - c| ≤ o` and `|b| ≤ s`, then `|a + b - c| ≤ s + o`. -/
theorem abs_add_sub_le {a b c s o : ℝ} (hac : |a - c| ≤ o) (hb : |b| ≤ s) :
    |a + b - c| ≤ s + o := by
  have h : a + b - c = (a - c) + b := by ring
  rw [h]
  exact le_trans (abs_add_le _ _) (by linarith)

/-- For real numbers, if `0 ≤ c` and `|a| ≤ B`, then `|c * a| ≤ c * B`. -/
theorem abs_const_mul_le {c a B : ℝ} (hc : 0 ≤ c) (h : |a| ≤ B) : |c * a| ≤ c * B := by
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left h hc

/-- If `|a| ≤ A` and `0 < c` for real numbers, then `|a / c| ≤ A / c`. -/
theorem abs_div_le_div_of_abs_le {a A c : ℝ} (ha : |a| ≤ A) (hc : 0 < c) : |a / c| ≤ A / c := by
  rw [abs_div, abs_of_pos hc]; exact div_le_div_of_nonneg_right ha hc.le

/-- For reals with `c⁻¹ ≤ x` and `x ≤ c`, `|x⁻¹| ≤ |c| + |c⁻¹|`. The proof splits by the sign of
`c`: for `c < 0` it shows `|x⁻¹| ≤ |c⁻¹|`, for `c = 0` it gets `x = 0`, and for `c > 0` it shows
`|x⁻¹| ≤ |c|`. -/
theorem abs_inv_le_abs_add_abs_inv {c x : ℝ} (h1 : c⁻¹ ≤ x) (h2 : x ≤ c) : |x⁻¹| ≤ |c| + |c⁻¹| := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have hx : x < 0 := lt_of_le_of_lt h2 hc
    have : |x⁻¹| ≤ |c⁻¹| := by
      rw [abs_inv, abs_inv, abs_of_neg hx, abs_of_neg hc]
      exact inv_anti₀ (by linarith) (by linarith)
    linarith [abs_nonneg c]
  · subst hc
    simp only [_root_.inv_zero] at h1
    have : x = 0 := le_antisymm h2 h1
    simp [this]
  · have hci : 0 < c⁻¹ := inv_pos.2 hc
    have hx : 0 < x := lt_of_lt_of_le hci h1
    have : |x⁻¹| ≤ |c| := by
      rw [abs_of_pos (inv_pos.2 hx), abs_of_pos hc]
      calc x⁻¹ ≤ (c⁻¹)⁻¹ := inv_anti₀ hci h1
        _ = c := inv_inv c
    linarith [abs_nonneg c⁻¹]

/-- If `|a| ≤ B` and `0 ≤ B` for real numbers, then `|if p then a else 0| ≤ B` for every decidable
proposition `p`. -/
theorem abs_ite_zero_le (p : Prop) [Decidable p] {a B : ℝ} (h : |a| ≤ B) (hB : 0 ≤ B) :
    |if p then a else 0| ≤ B := by
  split_ifs <;> simp [h, hB]

/-- For reals with `c⁻¹ ≤ x` and `x ≤ c`, `|x| ≤ |c| + |c⁻¹|`. -/
theorem abs_le_abs_add_abs_inv {c x : ℝ} (h1 : c⁻¹ ≤ x) (h2 : x ≤ c) : |x| ≤ |c| + |c⁻¹| := by
  rw [abs_le]
  constructor
  · linarith [neg_abs_le c⁻¹, abs_nonneg c]
  · linarith [le_abs_self c, abs_nonneg c⁻¹]

/-- Let `0 ≤ wabs`, `wabs ≤ e`, `0 ≤ a`, `0 ≤ b`, `a ≤ 2 * A` and `b ≤ 2 * B` be real numbers. If
`|r| ≤ wabs * ((1 * a + b / 1) / 2)`, then `|r| ≤ e * (A + B)`. -/
theorem abs_le_mul_add_of_abs_le {r wabs e a b A B : ℝ} (h1 : |r| ≤ wabs * ((1 * a + b / 1) / 2))
    (h4 : wabs ≤ e) (h0 : 0 ≤ wabs) (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ 2 * A) (hB : b ≤ 2 * B) :
    |r| ≤ e * (A + B) := by
  rw [one_mul, div_one] at h1
  have he : 0 ≤ e := h0.trans h4
  have h2 : wabs * ((a + b) / 2) ≤ e * ((a + b) / 2) := mul_le_mul_of_nonneg_right h4 (by linarith)
  have h3 : e * ((a + b) / 2) ≤ e * (A + B) := mul_le_mul_of_nonneg_left (by linarith) he
  linarith

/-- For a real `b` with `0 ≤ b ≤ 2` and a natural number `i ≤ 3`, the falling factorial polynomial
`descPochhammer ℝ i` evaluated at `-b` has absolute value at most `24`. The proof checks
`i = 0, 1, 2, 3`, where the values are `1`, `-b`, `b * (b + 1)` and `-(b * (b + 1) * (b + 2))`. -/
theorem abs_descPochhammer_eval_neg_le {b : ℝ} (hb0 : 0 ≤ b) (hb2 : b ≤ 2) {i : ℕ} (hi : i ≤ 3) :
    |(descPochhammer ℝ i).eval (-b)| ≤ 24 := by
  interval_cases i
  · simp
  · simp only [descPochhammer_one, Polynomial.eval_X, abs_neg]
    rw [abs_of_nonneg hb0]
    linarith
  · have he : (descPochhammer ℝ 2).eval (-b) = b * (b + 1) := by
      simp only [descPochhammer_succ_right, descPochhammer_zero, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_natCast, Polynomial.eval_one]
      push_cast
      ring
    rw [he, abs_of_nonneg (by positivity)]
    nlinarith
  · have he : (descPochhammer ℝ 3).eval (-b) = -(b * (b + 1) * (b + 2)) := by
      simp only [descPochhammer_succ_right, descPochhammer_zero, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_natCast, Polynomial.eval_one]
      push_cast
      ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
    have h1 : b * (b + 1) ≤ 6 := by nlinarith
    have h2 : 0 ≤ b * (b + 1) := by positivity
    nlinarith

/-- Let `A`, `C`, `T` be real and `B`, `P`, `V`, `s`, `a`, `b` nonnegative reals with `A ≤ P * s`
and `B ≤ V * s`. If `|T| ≤ C * a * b * √(A * B)`, then `|T| ≤ max C 0 * √(P * V) * a * b * s`. The
proof shows `√(A * B) ≤ √(P * V) * s` and replaces `C` by `max C 0`. -/
theorem abs_le_max_mul_sqrt_of_le {C A B P V s a b T : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h2 : A ≤ P * s) (h6 : B ≤ V * s)
    (hT : |T| ≤ C * a * b * Real.sqrt (A * B)) :
    |T| ≤ max C 0 * Real.sqrt (P * V) * a * b * s := by
  have hsq : Real.sqrt (A * B) ≤ Real.sqrt (P * V) * s := by
    rw [show Real.sqrt (P * V) * s = Real.sqrt (P * V * s ^ 2) by
      rw [Real.sqrt_mul (mul_nonneg hP hV), Real.sqrt_sq hs]]
    apply Real.sqrt_le_sqrt
    calc A * B ≤ (P * s) * (V * s) := mul_le_mul h2 h6 hB (mul_nonneg hP hs)
      _ = P * V * s ^ 2 := by ring
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  calc |T| ≤ C * a * b * Real.sqrt (A * B) := hT
    _ = C * (a * b * Real.sqrt (A * B)) := by ring
    _ ≤ max C 0 * (a * b * Real.sqrt (A * B)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hab (Real.sqrt_nonneg _))
    _ ≤ max C 0 * (a * b * (Real.sqrt (P * V) * s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hab) (le_max_right _ _)
    _ = max C 0 * Real.sqrt (P * V) * a * b * s := by ring

/-- For real numbers with `0 < l` and `|x| ≤ U`,
`|x * y * h| ≤ U * (l / 2 * y ^ 2 + h ^ 2 / (2 * l))`. This is Young's inequality
`|y| * |h| ≤ l / 2 * y ^ 2 + h ^ 2 / (2 * l)` multiplied by the bound on `|x|`. -/
theorem abs_mul_mul_le_of_left_le {x y h U l : ℝ} (hl : 0 < l) (hx : |x| ≤ U) :
    |x * y * h| ≤ U * (l / 2 * y ^ 2 + h ^ 2 / (2 * l)) := by
  have key : 2 * l * (|y| * |h|) ≤ l ^ 2 * y ^ 2 + h ^ 2 := by
    nlinarith [sq_nonneg (l * |y| - |h|), sq_abs y, sq_abs h]
  have e : l / 2 * y ^ 2 + h ^ 2 / (2 * l) = (l ^ 2 * y ^ 2 + h ^ 2) / (2 * l) := by
    field_simp
  have hyh : |y| * |h| ≤ l / 2 * y ^ 2 + h ^ 2 / (2 * l) := by
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  rw [abs_mul, abs_mul, mul_assoc]
  exact mul_le_mul hx hyh (by positivity) ((abs_nonneg x).trans hx)

/-- Let `δ > 0`, `M ≥ 0`, `D ≥ 0`, `|q| ≤ 1` and `|s| ≤ D` be real numbers, and suppose
`|p| ≤ M * (2 * δ)` whenever `s ≠ 0`. Then `|p * (s * (1 / δ) * q)| ≤ 2 * M * D`. The proof treats
`s = 0` separately and otherwise multiplies the three bounds. -/
theorem abs_mul_mul_one_div_mul_le {p s q δ M D : ℝ} (hδ : 0 < δ) (hq : |q| ≤ 1) (hs : |s| ≤ D)
    (hp : s ≠ 0 → |p| ≤ M * (2 * δ)) (hM : 0 ≤ M) (hD : 0 ≤ D) :
    |p * (s * (1 / δ) * q)| ≤ 2 * M * D := by
  by_cases hs0 : s = 0
  · simp only [hs0, one_div, zero_mul, mul_zero, abs_zero]; positivity
  have h1 : |p| * |s| * |q| ≤ M * (2 * δ) * D * 1 :=
    mul_le_mul (mul_le_mul (hp hs0) hs (abs_nonneg _) (by
      positivity)) hq (abs_nonneg _) (by positivity)
  have e : |p * (s * (1 / δ) * q)| = |p| * |s| * |q| / δ := by
    rw [abs_mul, abs_mul, abs_mul, abs_div, abs_one, abs_of_pos hδ]
    ring
  rw [e, div_le_iff₀ hδ]
  nlinarith

/-- For every real `t`, `|-2 * π * t| = 2 * π * |t|`. -/
theorem abs_neg_two_pi_mul (t : ℝ) : |-2 * π * t| = 2 * π * |t| := by
  rw [abs_mul, abs_of_neg (by linarith [pi_pos] : -2 * π < 0)]
  ring

/-- For real `a ≥ 0` and `b ≥ 0`, `|b ^ 3 - a ^ 3| ≤ 3 / 2 * |b - a| * (a ^ 2 + b ^ 2)`. This
follows from `b ^ 3 - a ^ 3 = (b - a) * (a ^ 2 + a * b + b ^ 2)` and `a * b ≤ (a ^ 2 + b ^ 2) / 2`.
-/
theorem abs_pow_three_sub_le_abs_sub {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    |b ^ 3 - a ^ 3| ≤ 3 / 2 * |b - a| * (a ^ 2 + b ^ 2) := by
  have e : b ^ 3 - a ^ 3 = (b - a) * (a ^ 2 + a * b + b ^ 2) := by ring
  have hq : 0 ≤ a ^ 2 + a * b + b ^ 2 := by positivity
  rw [e, abs_mul, abs_of_nonneg hq]
  have hab : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
  have hd : 0 ≤ |b - a| := abs_nonneg _
  nlinarith

/-- For real `a` and `b` with `0 ≤ a ≤ 1` and `0 ≤ b ≤ 1`, `|b ^ 3 - a ^ 3| ≤ 1`. -/
theorem abs_pow_three_sub_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |b ^ 3 - a ^ 3| ≤ 1 := by
  have h1 : a ^ 3 ≤ 1 := pow_le_one₀ ha0 ha1
  have h2 : b ^ 3 ≤ 1 := pow_le_one₀ hb0 hb1
  have h3 : 0 ≤ a ^ 3 := by positivity
  have h4 : 0 ≤ b ^ 3 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- For real `A ≥ 0` and `δ > 0`, `(A + δ / 2) ^ 2 + (δ / 2) ^ 2 ≤ (A + δ) ^ 2`. -/
theorem add_half_sq_add_half_sq_le {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) :
    (A + δ / 2) ^ 2 + (δ / 2) ^ 2 ≤ (A + δ) ^ 2 := by
  nlinarith

/-- For real `μ ≠ 0` and reals `x`, `y`, `x + μ * ((y - x) / μ) = y`. -/
theorem add_mul_sub_div_cancel {μ : ℝ} (hμ : μ ≠ 0) (x y : ℝ) : x + μ * ((y - x) / μ) = y := by
  rw [mul_div_cancel₀ _ hμ]
  ring

/-- For real `u ≥ 0` and `v ≥ 0` and a natural number `m`, `(u + v) ^ m ≤ 2 ^ m * (u ^ m + v ^ m)`.
The sum `u + v` is at most twice the larger of `u` and `v`. -/
theorem add_pow_le_two_pow_mul_add (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (m : ℕ) :
    (u + v) ^ m ≤ 2 ^ m * (u ^ m + v ^ m) := by
  rcases le_total u v with h | h
  · calc (u + v) ^ m ≤ (2 * v) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * v ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (u ^ m + v ^ m) := by
        have := pow_nonneg hu m
        gcongr
        linarith
  · calc (u + v) ^ m ≤ (2 * u) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * u ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (u ^ m + v ^ m) := by
        have := pow_nonneg hv m
        gcongr
        linarith

/-- Let `k` be a natural number and `s > 0` a real number with `k + 1 ≤ s / 2 < k + 1 + 1`. Then
`2 / (4 * k + 5) + 8 * (k + 1) ^ 2 / ((4 * k + 3) * s ^ 2) ≤ 4 / √3 * s⁻¹`. The proof replaces
`4 / √3` by the smaller constant `23 / 10` and proves the resulting quadratic inequality in `s` from
its values at the endpoints `2 * k + 2` and `2 * k + 4`. -/
theorem div_add_div_le_div_sqrt_three (k : ℕ) (s : ℝ) (hs0 : 0 < s) (hmle : (k : ℝ) + 1 ≤ s / 2)
    (hmlt : s / 2 < (k : ℝ) + 1 + 1) :
    2 / (4 * (k : ℝ) + 5) + 8 * ((k : ℝ) + 1) ^ 2 / ((4 * k + 3) * s ^ 2) ≤ 4 / Real.sqrt 3 *
        s⁻¹ := by
  have hK0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd5 : (0 : ℝ) < 4 * k + 5 := by positivity
  have hd3 : (0 : ℝ) < 4 * k + 3 := by positivity
  have hsq3 : Real.sqrt 3 ≤ 40 / 23 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hsq3p : 0 < Real.sqrt 3 := by positivity
  have h4 : (23 : ℝ) / 10 ≤ 4 / Real.sqrt 3 := by
    rw [le_div_iff₀ hsq3p]
    linarith
  have ha : 0 ≤ s - (2 * k + 2) := by linarith
  have hb : 0 ≤ (2 * k + 4) - s := by linarith
  have hfa : 2 * (4 * (k : ℝ) + 3) * (2 * k + 2) ^ 2 - 23 / 10 * (4 * k + 5) * (4 * k + 3) *
      (2 * k + 2)
      + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5) ≤ 0 := by
    nlinarith [mul_nonneg hK0 hK0, mul_nonneg (mul_nonneg hK0 hK0) hK0]
  have hfb : 2 * (4 * (k : ℝ) + 3) * (2 * k + 4) ^ 2 - 23 / 10 * (4 * k + 5) * (4 * k + 3) *
      (2 * k + 4)
      + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5) ≤ 0 := by
    nlinarith [mul_nonneg hK0 hK0, mul_nonneg (mul_nonneg hK0 hK0) hK0]
  have hf : 2 * (4 * (k : ℝ) + 3) * s ^ 2 - 23 / 10 * (4 * k + 5) * (4 * k + 3) * s
      + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5) ≤ 0 := by
    have hq : 0 ≤ (s - (2 * k + 2)) * ((2 * k + 4) - s) := mul_nonneg ha hb
    have e : 2 * (2 * (4 * (k : ℝ) + 3) * s ^ 2 - 23 / 10 * (4 * k + 5) * (4 * k + 3) * s
        + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5))
        = ((2 * k + 4) - s) * (2 * (4 * (k : ℝ) + 3) * (2 * k + 2) ^ 2
            - 23 / 10 * (4 * k + 5) * (4 * k + 3) * (2 * k + 2) + 8 * ((k : ℝ) + 1) ^ 2 *
                (4 * k + 5))
          + (s - (2 * k + 2)) * (2 * (4 * (k : ℝ) + 3) * (2 * k + 4) ^ 2
            - 23 / 10 * (4 * k + 5) * (4 * k + 3) * (2 * k + 4) + 8 * ((k : ℝ) + 1) ^ 2 *
                (4 * k + 5))
          - 4 * (4 * k + 3) * ((s - (2 * k + 2)) * ((2 * k + 4) - s)) := by ring
    have t1 := mul_nonpos_of_nonneg_of_nonpos hb hfa
    have t2 := mul_nonpos_of_nonneg_of_nonpos ha hfb
    have t3 : 0 ≤ 4 * (4 * (k : ℝ) + 3) * ((s - (2 * k + 2)) * ((2 * k + 4) - s)) := by positivity
    linarith
  have hlhs : 2 / (4 * (k : ℝ) + 5) + 8 * ((k : ℝ) + 1) ^ 2 / ((4 * k + 3) * s ^ 2)
      = (2 * (4 * k + 3) * s ^ 2 + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5)) /
          ((4 * k + 5) * (4 * k + 3) * s ^ 2) := by
    field_simp
  rw [hlhs, div_le_iff₀ (by positivity)]
  calc 2 * (4 * (k : ℝ) + 3) * s ^ 2 + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5)
      ≤ 23 / 10 * s⁻¹ * ((4 * k + 5) * (4 * k + 3) * s ^ 2) := by
        rw [show 23 / 10 * s⁻¹ * ((4 * k + 5) * (4 * k + 3) * s ^ 2) = 23 / 10 * (4 * k + 5) *
            (4 * k + 3) * s by
          field_simp]
        linarith
    _ ≤ 4 / Real.sqrt 3 * s⁻¹ * ((4 * k + 5) * (4 * k + 3) * s ^ 2) := by gcongr

/-- For real `c > 0`, `t ≥ 0` and `a ≥ 0`, `a / (1 + c * t) ≤ a * max 1 c⁻¹ / (1 + t)`. The proof
uses `1 + t ≤ max 1 c⁻¹ * (1 + c * t)`. -/
theorem div_one_add_mul_le {c t a : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (ha : 0 ≤ a) :
    a / (1 + c * t) ≤ a * max 1 c⁻¹ / (1 + t) := by
  have hm1 : 1 ≤ max 1 c⁻¹ := le_max_left _ _
  have hmc : 1 ≤ max 1 c⁻¹ * c := by
    calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ max 1 c⁻¹ * c := mul_le_mul_of_nonneg_right (le_max_right _ _) hc.le
  have key : 1 + t ≤ max 1 c⁻¹ * (1 + c * t) := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key ha]

/-- For real `c > 0`, `t ≥ 0` and `a ≥ 0`, `a / (1 + c * t) ^ 2 ≤ a * max 1 c⁻¹ ^ 2 / (1 + t) ^ 2`.
The proof squares the bound `1 + t ≤ max 1 c⁻¹ * (1 + c * t)`. -/
theorem div_one_add_mul_sq_le {c t a : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (ha : 0 ≤ a) :
    a / (1 + c * t) ^ 2 ≤ a * max 1 c⁻¹ ^ 2 / (1 + t) ^ 2 := by
  have hm1 : 1 ≤ max 1 c⁻¹ := le_max_left _ _
  have hmc : 1 ≤ max 1 c⁻¹ * c := by
    calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ max 1 c⁻¹ * c := mul_le_mul_of_nonneg_right (le_max_right _ _) hc.le
  have key : 1 + t ≤ max 1 c⁻¹ * (1 + c * t) := by nlinarith
  have key2 : (1 + t) ^ 2 ≤ max 1 c⁻¹ ^ 2 * (1 + c * t) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) key 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key2 ha]

/-- If real numbers `a`, `b`, `P`, `Q` satisfy `|a - b| ≤ P * ρ ^ 2 + Q * ρ` for every real `ρ > 0`,
then `a = b`. The right side tends to `0` as `ρ` tends to `0` from the right. -/
theorem eq_of_abs_sub_le_quadratic {a b P Q : ℝ}
    (h : ∀ ρ : ℝ, 0 < ρ → |a - b| ≤ P * ρ ^ 2 + Q * ρ) :
    a = b := by
  have ht : Tendsto (fun ρ : ℝ ↦ P * ρ ^ 2 + Q * ρ) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun ρ : ℝ ↦ P * ρ ^ 2 + Q * ρ) := by fun_prop
    have := hcont.tendsto (0 : ℝ)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ρ hρ ↦ h ρ hρ)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- If real numbers `A`, `B`, `C`, `S` satisfy `|A + B / √s| ≤ C / s` for all real `s ≥ S`, then
`A = 0` and `B = 0`. Letting `s` tend to infinity gives `A = 0`, and then `|B| ≤ C / √s` for large
`s` gives `B = 0`. -/
theorem eq_zero_of_add_div_sqrt_le {A B C S : ℝ}
    (h : ∀ s ≥ S, |A + B / √s| ≤ C / s) : A = 0 ∧ B = 0 := by
  have hC : Tendsto (fun s : ℝ ↦ C / s) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h1 : Tendsto (fun s : ℝ ↦ A + B / √s) atTop (𝓝 0) :=
    squeeze_zero_norm' ((eventually_ge_atTop S).mono fun s hs ↦ by
      rw [Real.norm_eq_abs]; exact h s hs) hC
  have h2 : Tendsto (fun s : ℝ ↦ A + B / √s) atTop (𝓝 (A + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop)
  have hA : A = 0 := by simpa using tendsto_nhds_unique h2 h1
  subst hA
  have hC' : Tendsto (fun s : ℝ ↦ C / √s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h3 : Tendsto (fun _ : ℝ ↦ B) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hC'
    filter_upwards [eventually_ge_atTop (max S 1)] with s hs
    have hs1 : 1 ≤ s := le_of_max_le_right hs
    have hsS : S ≤ s := le_of_max_le_left hs
    have hs0 : 0 < s := by linarith
    have hr : 0 < √s := Real.sqrt_pos.2 hs0
    have := h s hsS
    rw [zero_add, abs_div, abs_of_pos hr, div_le_div_iff₀ hr hs0] at this
    rw [Real.norm_eq_abs, le_div_iff₀ hr]
    have hrs : √s ^ 2 = s := Real.sq_sqrt hs0.le
    nlinarith [abs_nonneg B]
  exact ⟨rfl, tendsto_nhds_unique tendsto_const_nhds h3⟩

/-- For every real `K` and every `δ > 0` there is a real `ε` with `0 < ε`, `ε ≤ 1` and `ε * K ≤ δ`.
The proof takes `ε = min 1 (δ / (|K| + 1))`. -/
theorem exists_pos_le_one_mul_le (K δ : ℝ) (hδ : 0 < δ) : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * K ≤ δ := by
  refine ⟨min 1 (δ / (|K| + 1)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  have h1 : min 1 (δ / (|K| + 1)) ≤ δ / (|K| + 1) := min_le_right _ _
  have h0 : 0 ≤ min 1 (δ / (|K| + 1)) := le_of_lt (lt_min one_pos (by positivity))
  calc min 1 (δ / (|K| + 1)) * K ≤ min 1 (δ / (|K| + 1)) * |K| :=
        mul_le_mul_of_nonneg_left (le_abs_self K) h0
    _ ≤ δ / (|K| + 1) * |K| := mul_le_mul_of_nonneg_right h1 (abs_nonneg K)
    _ ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg K]

/-- For real numbers `μ`, `D`, `I`, `Q`, `K` with `μ ≠ 0`, if `D + μ * I + μ * Q = 0` and `K = -Q`,
then `μ⁻¹ * D + I = K`. -/
theorem inv_mul_add_eq_of_eq_zero {μ D I Q K : ℝ} (hμ : μ ≠ 0) (e : D + μ * I + μ * Q = 0)
    (hK : K = -Q) :
    μ⁻¹ * D + I = K := by
  have hD : D = -(μ * I) - μ * Q := by linarith
  rw [hK, hD]
  field_simp
  ring

/-- For real `r ≠ 0` and real `x`, `(r⁻¹ * x) ^ 2 * r = r⁻¹ * x ^ 2`. -/
theorem inv_mul_sq_mul_self {r : ℝ} (hr : r ≠ 0) (x : ℝ) : (r⁻¹ * x) ^ 2 * r = r⁻¹ * x ^ 2 := by
  field_simp

/-- Let `r > 0`, `1 / (16 * r) ≤ ρ`, `C ≥ 0`, `G ≥ 0` and `B₁ ≥ 0` be reals, and suppose
`n ≤ e₁ * n₁ + e₂ * n₂ + r * (x₁ + x₂)` with `e₁ ≤ 1`, `0 ≤ n₁ ≤ C / (1 + ρ) ^ 2`, `e₂ ≤ r * B₁`,
`0 ≤ n₂ ≤ C / (1 + ρ)`, `x₁ ≤ G * (2 * C / ρ)` and `x₂ ≤ r * B₂ * C`. Then
`n ≤ C / (1 + ρ) ^ 2 + r ^ 2 * (16 * B₁ * C + 32 * G * C + B₂ * C)`. The proof uses `1 ≤ 16 * r * ρ`
to bound `C / (1 + ρ)` by `16 * r * C` and `2 * C / ρ` by `32 * r * C`. -/
theorem le_div_add_sq_mul_of_le {n e₁ n₁ e₂ n₂ x₁ x₂ r ρ C B₁ B₂ G : ℝ} (hr : 0 < r)
    (hρ : 1 / (16 * r) ≤ ρ)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hn : n ≤ e₁ * n₁ + e₂ * n₂ + r * (x₁ + x₂))
    (he₁1 : e₁ ≤ 1) (hn₁0 : 0 ≤ n₁) (hn₁ : n₁ ≤ C / (1 + ρ) ^ 2) (he₂ : e₂ ≤ r * B₁)
    (hn₂0 : 0 ≤ n₂) (hn₂ : n₂ ≤ C / (1 + ρ)) (hx₁ : x₁ ≤ G * (2 * C / ρ)) (hx₂ : x₂ ≤ r * B₂ * C)
    (hB₁ : 0 ≤ B₁) :
    n ≤ C / (1 + ρ) ^ 2 + r ^ 2 * (16 * B₁ * C + 32 * G * C + B₂ * C) := by
  have hq : 0 < 1 / (16 * r) := by positivity
  have hρ0 : 0 < ρ := hq.trans_le hρ
  have h16 : 1 ≤ 16 * r * ρ := by
    rw [div_le_iff₀ (by positivity)] at hρ
    linarith
  have k1 : C / (1 + ρ) ≤ 16 * r * C := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hr.le hC) hρ0.le]
  have k2 : 2 * C / ρ ≤ 32 * r * C := by
    rw [div_le_iff₀ hρ0]
    nlinarith
  have t1 : e₁ * n₁ ≤ C / (1 + ρ) ^ 2 := by
    rcases le_or_gt 0 e₁ with h | h
    · exact (mul_le_of_le_one_left hn₁0 he₁1).trans hn₁
    · exact (mul_nonpos_of_nonpos_of_nonneg h.le hn₁0).trans (by positivity)
  have t2 : e₂ * n₂ ≤ (r * B₁) * (16 * r * C) := by
    rcases le_or_gt 0 e₂ with h | h
    · exact mul_le_mul he₂ (hn₂.trans k1) hn₂0 (by positivity)
    · exact (mul_nonpos_of_nonpos_of_nonneg h.le hn₂0).trans (by positivity)
  have t3 : x₁ ≤ G * (32 * r * C) := hx₁.trans (mul_le_mul_of_nonneg_left k2 hG)
  have t4 : r * (x₁ + x₂) ≤ r * (G * (32 * r * C) + r * B₂ * C) :=
    mul_le_mul_of_nonneg_left (add_le_add t3 hx₂) hr.le
  linarith

/-- For real `t > 0` and `c`, `c ≤ (t⁻¹ + t * c ^ 2) / 2`. This is Mathlib's
`two_mul_le_add_mul_sq` for `c` and `1` at the parameter `t`, divided by `2`. -/
theorem le_half_inv_add_mul_sq (t c : ℝ) (ht : 0 < t) : c ≤ (t⁻¹ + t * c ^ 2) / 2 := by
  have h := two_mul_le_add_mul_sq (a := c) (b := 1) ht
  rw [mul_one, one_pow, mul_one] at h
  linarith

/-- For real `a` and `b ≥ 0`, if `a ^ 2 ≤ b * a` then `a ≤ b`. -/
theorem le_of_sq_le_mul {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b * a) : a ≤ b := by
  nlinarith

/-- For real `N` and `K ≥ 0`, if `(1 / 2) * N ^ 2 ≤ K * N` then `N ≤ 2 * K`. -/
theorem le_two_mul_of_half_sq_le {N K : ℝ} (hK : 0 ≤ K)
    (h : (1 / 2) * N ^ 2 ≤ K * N) : N ≤ 2 * K := by
  nlinarith

/-- Let `A ≥ 0` and `q ≥ 0` be reals with `8 * q * A ≤ 1`. If `0 ≤ s ≤ 2 * A` and
`x ≤ A + q * s ^ 2`, then `x ≤ 2 * A`. -/
theorem le_two_mul_of_le_add_sq {A q x s : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) (hqA : 8 * q * A ≤ 1)
    (hs0 : 0 ≤ s)
    (hs : s ≤ 2 * A) (hx : x ≤ A + q * s ^ 2) : x ≤ 2 * A := by
  have h2 : s ^ 2 ≤ (2 * A) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  nlinarith [mul_le_mul_of_nonneg_left h2 hq, mul_le_mul_of_nonneg_left hqA hA]

/-- Let `s ≥ 0`, `ρ > 0`, `a ≥ 0`, `b ≥ 0` and `C` be reals. If `a ≤ C / (1 + s * ρ)` and
`b ≤ C / (1 + s * ρ) ^ 2`, then `s * (a + b * s * ρ) ≤ 2 * C / ρ`. -/
theorem mul_add_mul_le_of_le_div {s ρ C a b : ℝ} (hs0 : 0 ≤ s) (hρ : 0 < ρ) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (ha : a ≤ C / (1 + s * ρ)) (hb : b ≤ C / (1 + s * ρ) ^ 2) :
    s * (a + b * s * ρ) ≤ 2 * C / ρ := by
  have h1 : 0 < 1 + s * ρ := by positivity
  have hsρ : 0 ≤ s * ρ := by positivity
  rw [le_div_iff₀ h1] at ha
  rw [le_div_iff₀ (by positivity)] at hb
  rw [le_div_iff₀ hρ]
  nlinarith [mul_nonneg hb0 hsρ]

/-- For real `Q`, `N`, `K ≥ 0` and `s > 0`,
`Q ^ 2 * N * (2 / (2 * (2 * K + 2) + 1)) + (s ^ 2)⁻¹ * (Q ^ 4 / 2 * N + Q ^ 2 * N * ((2 * K + 2) *
(2 * K + 1) * (2 / (2 * K + 1) - 2 / (2 * (2 * K + 1) + 1))))` equals
`Q ^ 2 * N * (2 / (4 * K + 5) + 8 * (K + 1) ^ 2 / ((4 * K + 3) * s ^ 2)) + 1 / 2 * Q ^ 4 *
(s ^ 2)⁻¹ * N`. The proof clears the denominators, which are nonzero because `K ≥ 0` and `s > 0`. -/
theorem mul_div_add_inv_sq_mul_eq (Q N K s : ℝ) (hs : 0 < s) (hK : 0 ≤ K) :
    Q ^ 2 * N * (2 / (2 * (2 * K + 2) + 1))
        + (s ^ 2)⁻¹ * (Q ^ 4 / 2 * N
          + Q ^ 2 * N * ((2 * K + 2) * (2 * K + 1) * (2 / (2 * K + 1) - 2 / (2 * (2 * K + 1) + 1))))
      = Q ^ 2 * N * (2 / (4 * K + 5) + 8 * (K + 1) ^ 2 / ((4 * K + 3) * s ^ 2)) + 1 / 2 * Q ^ 4 *
          (s ^ 2)⁻¹ * N := by
  have h5 : 4 * K + 5 ≠ 0 := by positivity
  have h3 : 4 * K + 3 ≠ 0 := by positivity
  have h1 : 2 * K + 1 ≠ 0 := by positivity
  have h5' : 2 * (2 * K + 2) + 1 ≠ 0 := by positivity
  have h3' : 2 * (2 * K + 1) + 1 ≠ 0 := by positivity
  have hs' : s ≠ 0 := hs.ne'
  field_simp
  ring

/-- For real `c ≥ 0` and `δ > 0`, `c * (δ / (2 * (c + 1))) ≤ δ / 2`. -/
theorem mul_div_two_mul_add_one_le {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    c * (δ / (2 * (c + 1))) ≤ δ / 2 := by
  have hc1 : 0 < c + 1 := by linarith
  have e : c * (δ / (2 * (c + 1))) = δ / 2 - δ / (2 * (c + 1)) := by
    field_simp
    ring
  have : 0 < δ / (2 * (c + 1)) := by positivity
  linarith

/-- For real `C` and `t ≥ 0`, `C * t ≤ |C| * t`. -/
theorem mul_le_abs_mul_of_nonneg {C t : ℝ} (ht0 : 0 ≤ t) : C * t ≤ |C| * t :=
    mul_le_mul_of_nonneg_right (le_abs_self C) ht0

/-- Let `u` be real with `0 < u ≤ 1` and `u * u = T`. If `M ≤ 2 * m + 2 * (K / u)` and
`u ≤ (δ / 2) ^ 2 / (2 * |m| + 2 * |K| + 1)`, then `T * M ≤ (δ / 2) ^ 2`. The proof bounds `T * M` by
`(2 * |m| + 2 * |K| + 1) * u`. -/
theorem mul_le_half_sq_of_le_div {T u m K M δ : ℝ} (hupos : 0 < u) (hTu : u * u = T) (hu1 : u ≤ 1)
    (hM : M ≤ 2 * m + 2 * (K / u)) (huδ : u ≤ (δ / 2) ^ 2 / (2 * |m| + 2 * |K| + 1)) :
    T * M ≤ (δ / 2) ^ 2 := by
  have hLpos : 0 < 2 * |m| + 2 * |K| + 1 := by positivity
  have hT : 0 ≤ T := by rw [← hTu]; positivity
  have e : T * (2 * m + 2 * (K / u)) = 2 * (u * u) * m + 2 * K * u := by
    rw [← hTu]
    field_simp
  have hm1 : u * u * m ≤ u * |m| := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self m) (mul_nonneg hupos.le hupos.le)
    have h2 := mul_le_mul_of_nonneg_right hu1 (abs_nonneg m)
    nlinarith [abs_nonneg m]
  have hK1 : K * u ≤ |K| * u := mul_le_mul_of_nonneg_right (le_abs_self K) hupos.le
  calc T * M ≤ T * (2 * m + 2 * (K / u)) := mul_le_mul_of_nonneg_left hM hT
    _ = 2 * (u * u) * m + 2 * K * u := e
    _ ≤ (2 * |m| + 2 * |K| + 1) * u := by linarith [hupos.le]
    _ ≤ (2 * |m| + 2 * |K| + 1) * ((δ / 2) ^ 2 / (2 * |m| + 2 * |K| + 1)) :=
        mul_le_mul_of_nonneg_left huδ hLpos.le
    _ = (δ / 2) ^ 2 := by field_simp

/-- For real `q ≥ 0`, `0 ≤ a ≤ A`, `0 ≤ c ≤ Cc` and `0 ≤ d ≤ D`,
`q * (1 + a * 2 * c * d * q) ≤ q * (1 + A * 2 * Cc * D * q)`. The proof bounds `a * c * d` by
`A * Cc * D`. -/
theorem mul_one_add_mul_le_of_le {q a A c Cc d D : ℝ} (hq : 0 ≤ q) (ha0 : 0 ≤ a) (ha : a ≤ A)
    (hc0 : 0 ≤ c) (hc : c ≤ Cc)
    (hd0 : 0 ≤ d) (hd : d ≤ D) : q * (1 + a * 2 * c * d * q) ≤ q * (1 + A * 2 * Cc * D * q) := by
  refine mul_le_mul_of_nonneg_left ?_ hq
  have h1 : a * c ≤ A * Cc := mul_le_mul ha hc hc0 (ha0.trans ha)
  have h2 : a * c * d ≤ A * Cc * D := mul_le_mul h1 hd hd0 ((mul_nonneg ha0 hc0).trans h1)
  have h3 : a * 2 * c * d * q ≤ A * 2 * Cc * D * q := by
    calc a * 2 * c * d * q = (a * c * d) * (2 * q) := by ring
      _ ≤ (A * Cc * D) * (2 * q) := mul_le_mul_of_nonneg_right h2 (mul_nonneg zero_le_two hq)
      _ = A * 2 * Cc * D * q := by ring
  linarith

/-- For real `a ≥ 0` and `c ≥ 0`, `a * c ^ 5 ≤ (a ^ 6 + 5 * c ^ 6) / 6`. This is Young's inequality
with the exponents `6` and `6 / 5`. -/
theorem mul_pow_five_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) : a * c ^ 5 ≤ (a ^ 6 + 5 * c ^ 6) / 6 :=
    by
  have hq : 0 ≤ a ^ 4 + 2 * a ^ 3 * c + 3 * a ^ 2 * c ^ 2 + 4 * a * c ^ 3 + 5 * c ^ 4 := by
    positivity
  nlinarith [mul_nonneg (sq_nonneg (a - c)) hq]

/-- Let `X`, `A`, `S`, `c`, `D`, `ρ` be nonnegative real numbers and `r ≥ 1`, with `ρ ≤ 1 / r`, and
let `s` be a real number with `s ≤ S * (√X + c * A / r)`. Then
`D * (A ^ 2 * s * ρ) ≤ X / 4 + (D ^ 2 * S ^ 2 * A ^ 4 + D * S * c * A ^ 3) / r`. The proof inserts
the bound on `s` and uses `u * √X ≤ X / 4 + u ^ 2` with `u = D * S * A ^ 2 * ρ`. -/
theorem mul_sq_mul_mul_le_quarter_add {X A r s S c D ρ : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hS : 0 ≤ S) (hc : 0 ≤ c) (hD : 0 ≤ D) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / r)
    (hHs : s ≤ S * (√X + c * A / r)) :
    D * (A ^ 2 * s * ρ) ≤ X / 4 + (D ^ 2 * S ^ 2 * A ^ 4 + D * S * c * A ^ 3) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hir : 1 / r ≤ 1 := by rw [div_le_one hr0]; exact hr
  have hρ1 : ρ ≤ 1 := hρ.trans hir
  have ha := Real.sqrt_nonneg X
  have hsX : √X ^ 2 = X := Real.sq_sqrt hX
  have step1 : D * (A ^ 2 * s * ρ) ≤ D * (A ^ 2 * ρ) * (S * (√X + c * A / r)) := by
    calc D * (A ^ 2 * s * ρ) = D * (A ^ 2 * ρ) * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hHs (by positivity)
  have hb : (D * S * A ^ 2 * ρ) * √X ≤ √X ^ 2 / 4 + (D * S * A ^ 2 * ρ) ^ 2 := by
    nlinarith [sq_nonneg (√X / 2 - D * S * A ^ 2 * ρ)]
  have hρ2 : ρ ^ 2 ≤ 1 / r := by nlinarith
  have hb2 : (D * S * A ^ 2 * ρ) ^ 2 ≤ D ^ 2 * S ^ 2 * A ^ 4 / r := by
    calc (D * S * A ^ 2 * ρ) ^ 2 = D ^ 2 * S ^ 2 * A ^ 4 * ρ ^ 2 := by ring
      _ ≤ D ^ 2 * S ^ 2 * A ^ 4 * (1 / r) := mul_le_mul_of_nonneg_left hρ2 (by positivity)
      _ = D ^ 2 * S ^ 2 * A ^ 4 / r := by ring
  have h3 : D * S * c * A ^ 3 * (ρ / r) ≤ D * S * c * A ^ 3 * (1 / r) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hρ1 hr0.le) (by positivity)
  calc D * (A ^ 2 * s * ρ) ≤ D * (A ^ 2 * ρ) * (S * (√X + c * A / r)) := step1
    _ = (D * S * A ^ 2 * ρ) * √X + D * S * c * A ^ 3 * (ρ / r) := by ring
    _ ≤ √X ^ 2 / 4 + D ^ 2 * S ^ 2 * A ^ 4 / r + D * S * c * A ^ 3 * (1 / r) := by linarith
    _ = _ := by rw [hsX]; ring

/-- For real numbers with `q ≠ 0`, if `-(ν * A) = ν * G + s` then
`-(ν * (q * A)) / q = ν * (q * G) / q + s`. The factor `q` inside each product cancels against the
division by `q`. -/
theorem neg_mul_div_eq_mul_div_add {ν A G s q : ℝ} (hq : q ≠ 0) (h : -(ν * A) = ν * G + s) :
    -(ν * (q * A)) / q = ν * (q * G) / q + s := by
  have e1 : -(ν * (q * A)) / q = -(ν * A) := by
    rw [show -(ν * (q * A)) = q * (-(ν * A)) by ring, mul_div_cancel_left₀ _ hq]
  have e2 : ν * (q * G) / q = ν * G := by
    rw [show ν * (q * G) = q * (ν * G) by ring, mul_div_cancel_left₀ _ hq]
  rw [e1, e2, h]

/-- For real `a ≥ 0`, `0 ≤ x ≤ X` and `0 ≤ y ≤ Y`, `1 + a * x * y ≤ 1 + a * X * Y`. -/
theorem one_add_mul_mul_le_of_le {a x X y Y : ℝ} (ha : 0 ≤ a) (hx0 : 0 ≤ x) (hx : x ≤ X)
    (hy0 : 0 ≤ y) (hy : y ≤ Y) :
    1 + a * x * y ≤ 1 + a * X * Y := by
  have h1 : x * y ≤ X * Y := mul_le_mul hx hy hy0 (hx0.trans hx)
  have h2 := mul_le_mul_of_nonneg_left h1 ha
  linarith [show a * x * y = a * (x * y) by ring, show a * X * Y = a * (X * Y) by ring]

/-- For real `x ∈ Set.Icc (-1) 1` and a natural number `k`, the even power `x ^ (2 * k + 2)`
satisfies `0 ≤ x ^ (2 * k + 2)` and `x ^ (2 * k + 2) ≤ 1`. -/
theorem pow_even_nonneg_and_le_one (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ x ^ (2 * k + 2) ∧ x ^ (2 * k + 2) ≤ 1 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
  exact ⟨pow_nonneg (sq_nonneg x) _, pow_le_one₀ (sq_nonneg x) hx2⟩

/-- If `n₀`, `n₁`, `n₂` are nonnegative reals and each is at most `A + B`, then
`n₀ ^ 2 + n₁ ^ 2 + n₂ ^ 2 ≤ 6 * A ^ 2 + 6 * B ^ 2`. -/
theorem sq_add_sq_add_sq_le {n₀ n₁ n₂ A B : ℝ} (h0 : 0 ≤ n₀) (h1 : 0 ≤ n₁) (h2 : 0 ≤ n₂)
    (k0 : n₀ ≤ A + B) (k1 : n₁ ≤ A + B) (k2 : n₂ ≤ A + B) :
    n₀ ^ 2 + n₁ ^ 2 + n₂ ^ 2 ≤ 6 * A ^ 2 + 6 * B ^ 2 := by
  have q0 := pow_le_pow_left₀ h0 k0 2
  have q1 := pow_le_pow_left₀ h1 k1 2
  have q2 := pow_le_pow_left₀ h2 k2 2
  nlinarith [sq_nonneg (A - B)]

/-- For real `a` and `b`, `((1 / 2) * (a + b)) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2`: the square of the
arithmetic mean is at most the arithmetic mean of the squares. -/
theorem sq_arith_mean_le_arith_mean_sq (a b : ℝ) : ((1 / 2) * (a + b)) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 :=
    by
  nlinarith [sq_nonneg (a - b)]

/-- For real `a ≥ 0` and `b`, `a ^ 2 * b ^ 2 ≤ a ^ 2 + a ^ 6 + b ^ 6`. The proof splits into the
case `b ^ 2 ≤ a`, where the left side is at most `a ^ 3 ≤ a ^ 2 + a ^ 6`, and the case `a ≤ b ^ 2`,
where it is at most `b ^ 6`. -/
theorem sq_mul_sq_le_add_pow_six {a b : ℝ} (ha : 0 ≤ a) :
    a ^ 2 * b ^ 2 ≤ a ^ 2 + a ^ 6 + b ^ 6 := by
  have h6a : 0 ≤ a ^ 6 := by positivity
  have h6b : 0 ≤ b ^ 6 := by positivity
  have h2a : 0 ≤ a ^ 2 := by positivity
  rcases le_total (b ^ 2) a with h | h
  · have h1 : a ^ 2 * b ^ 2 ≤ a ^ 2 * a := mul_le_mul_of_nonneg_left h h2a
    rcases le_total a 1 with h' | h'
    · have : a ^ 2 * a ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left h' h2a
      linarith
    · have : a ^ 2 * a ≤ a ^ 6 := by
        have e : a ^ 2 * a = a ^ 3 := by ring
        rw [e]
        exact pow_le_pow_right₀ h' (by norm_num)
      linarith
  · have h1 : a ^ 2 ≤ (b ^ 2) ^ 2 := pow_le_pow_left₀ ha h 2
    have h2 : a ^ 2 * b ^ 2 ≤ (b ^ 2) ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
    have e : (b ^ 2) ^ 2 * b ^ 2 = b ^ 6 := by ring
    linarith

/-- For real `a < b` and a natural number `k`, `(b - a) / (8 * (k + 1)) ≤ (b - a) / 8`. -/
theorem sub_div_eight_mul_add_one_le (a b : ℝ) (hab : a < b) (k : ℕ) :
    (b - a) / (8 * ((k : ℝ) + 1)) ≤ (b - a) / 8 := by
  apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- For real `a < b` and a natural number `k`, `0 < (b - a) / (8 * (k + 1))`. -/
theorem sub_div_eight_mul_add_one_pos (a b : ℝ) (hab : a < b) (k : ℕ) :
    0 < (b - a) / (8 * ((k : ℝ) + 1)) := by
  apply div_pos (by linarith); positivity

/-- For a real `s` and positive real `r`, `c`, `d`,
`2 * s ≤ d * c ^ 2 * (r ^ (2 * 1) * s ^ 2) + d * (r ^ (2 * 2) * s ^ 2) + 1 / (d * r ^ 2 * (c ^ 2 + r
^ 2))`. With `w = d * r ^ 2 * (c ^ 2 + r ^ 2)` this is `2 * s ≤ w * s ^ 2 + 1 / w`, which is
Mathlib's `two_mul_le_add_mul_sq` for `s` and `1` at the parameter `w`. -/
theorem two_mul_le_weighted_sq_add_one_div (s r c d : ℝ) (hr : 0 < r) (hc : 0 < c) (hd : 0 < d) :
    2 * s ≤ d * c ^ 2 * (r ^ (2 * 1) * s ^ 2) + d * (r ^ (2 * 2) * s ^ 2) +
      1 / (d * r ^ 2 * (c ^ 2 + r ^ 2)) := by
  have hw : 0 < d * r ^ 2 * (c ^ 2 + r ^ 2) := by positivity
  have h := two_mul_le_add_mul_sq (a := s) (b := 1) hw
  rw [mul_one, one_pow, mul_one, inv_eq_one_div] at h
  linarith

/-- For real numbers with `0 < l` and `|y| ≤ U`,
`|x * y * h| ≤ U * (l / 2 * x ^ 2 + h ^ 2 / (2 * l))`. Here the bounded factor is the middle one,
and the square of the first factor appears on the right. -/
theorem abs_mul_mul_le_of_middle_le {x y h U l : ℝ} (hl : 0 < l) (hy : |y| ≤ U) :
    |x * y * h| ≤ U * (l / 2 * x ^ 2 + h ^ 2 / (2 * l)) := by
  have e : x * y * h = y * x * h := by ring
  rw [e]
  exact abs_mul_mul_le_of_left_le hl hy

/-- For real `a`, `b` and `β > 0`, `2 * (a * b) ≤ β * a ^ 2 + b ^ 2 / β`. This is Mathlib's
`two_mul_le_add_mul_sq`, with the product and the inverse written as the lemmas of these modules
write them. -/
theorem two_mul_mul_le_mul_sq_add (a b β : ℝ) (hβ : 0 < β) :
    2 * (a * b) ≤ β * a ^ 2 + b ^ 2 / β := by
  have h := two_mul_le_add_mul_sq (a := a) (b := b) hβ
  rwa [mul_assoc, inv_mul_eq_div] at h

/-- For real `C` and `w` with `0 ≤ w ≤ 1`, `C * w ≤ |C|`. -/
theorem mul_le_abs_of_le_one {C w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : C * w ≤ |C| :=
  (mul_le_mul_of_nonneg_right (le_abs_self C) hw0).trans (mul_le_of_le_one_right (abs_nonneg C) hw1)

/-- For real `t ≥ 0` and `x ≥ 0`, `t ^ 2 * x ≤ t ^ 3 + x ^ 3`. The cases `x ≤ t` and `t ≤ x` are
treated separately. -/
theorem sq_mul_le_cube_add_cube (t x : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x) : t ^ 2 * x ≤ t ^ 3 + x ^ 3 :=
    by
  rcases le_total x t with h | h
  · nlinarith [pow_nonneg hx 3, mul_le_mul_of_nonneg_left h (sq_nonneg t)]
  · nlinarith [pow_nonneg ht 3, mul_le_mul_of_nonneg_left h (sq_nonneg x),
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht h 2) hx]

/-- For real `x`, `y` and `t > 0`, `x * y ≤ (t * x ^ 2 + y ^ 2 / t) / 2`. This is
`two_mul_mul_le_mul_sq_add` divided by `2`. -/
theorem mul_le_mul_sq_add_div_two {x y t : ℝ} (ht : 0 < t) :
    x * y ≤ (t * x ^ 2 + y ^ 2 / t) / 2 := by
  linarith [two_mul_mul_le_mul_sq_add x y t ht]

/-- For real numbers, if `|c| ≤ M`, then `|c * a ^ 2| ≤ M * a ^ 2`. -/
theorem abs_mul_sq_le_of_abs_le {c M a : ℝ} (hc : |c| ≤ M) : |c * a ^ 2| ≤ M * a ^ 2 := by
  rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg a)

/-- For real `s`, `g`, `f` with `0 ≤ f`, if `s ^ 2 + (1 / 4) * g ^ 2 ≤ f ^ 2`, then `g ≤ 2 * f`. -/
theorem le_two_mul_of_sq_add {s g f : ℝ} (hf : 0 ≤ f)
    (h : s ^ 2 + (1 / 4 : ℝ) * g ^ 2 ≤ f ^ 2) : g ≤ 2 * f := by
  nlinarith [sq_nonneg s]

/-- For real `a`, `b`, `c`, `(a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2)`. -/
theorem add_add_sq_le_three_mul (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- For real `a` and `M > 0`, `a ^ 2 ≤ a ^ 6 / M ^ 2 + M`. If `a ^ 2 ≤ M` the term `M` suffices;
otherwise `M ^ 2 ≤ a ^ 4` and the term `a ^ 6 / M ^ 2` suffices. -/
theorem sq_le_pow_six_div_sq_add {a M : ℝ} (hM : 0 < M) : a ^ 2 ≤ a ^ 6 / M ^ 2 + M := by
  rcases le_or_gt (a ^ 2) M with h | h
  · have : 0 ≤ a ^ 6 / M ^ 2 := by positivity
    linarith
  · have h1 : M ^ 2 ≤ (a ^ 2) ^ 2 := pow_le_pow_left₀ hM.le h.le 2
    have h2 : a ^ 2 * M ^ 2 ≤ a ^ 6 := by
      have : a ^ 6 = a ^ 2 * (a ^ 2) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : a ^ 2 ≤ a ^ 6 / M ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      exact h2
    linarith

/-- For real `x`, `y` and `θ > 0`, `(x + y) ^ 2 ≤ (1 + θ) * x ^ 2 + (1 + θ⁻¹) * y ^ 2`. After
expanding the square this is Young's inequality `two_mul_mul_le_mul_sq_add`. -/
theorem add_sq_le_one_add_mul_sq {x y θ : ℝ} (hθ : 0 < θ) :
    (x + y) ^ 2 ≤ (1 + θ) * x ^ 2 + (1 + θ⁻¹) * y ^ 2 := by
  have h := two_mul_mul_le_mul_sq_add x y θ hθ
  rw [div_eq_inv_mul] at h
  rw [add_sq]
  linarith

/-- For real `a`, `b`, `(a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2`. This is Mathlib's `add_sq_le` with the
factor `2` multiplied out. -/
theorem add_sq_le_two_mul_sq_add_two_mul_sq (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  simpa only [mul_add] using add_sq_le (a := a) (b := b)

/-- For real `u ≥ 0` and `a > 0`, `u ≤ a + u ^ 3 / a ^ 2`. If `u ≤ a` the term `a` suffices;
otherwise `a ^ 2 ≤ u ^ 2` and the term `u ^ 3 / a ^ 2` suffices. -/
theorem le_add_cube_div_sq {u a : ℝ} (hu : 0 ≤ u) (ha : 0 < a) : u ≤ a + u ^ 3 / a ^ 2 := by
  rcases le_or_gt u a with h | h
  · have : 0 ≤ u ^ 3 / a ^ 2 := by positivity
    linarith
  · have h2 : u ≤ u ^ 3 / a ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h3 : a ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ ha.le h.le 2
      have h4 := mul_le_mul_of_nonneg_left h3 hu
      nlinarith
    linarith

/-- For real `r ≥ 0` and `a ≥ 0`, `a ^ 6 + 6 * a ^ 5 * (r - a) ≤ r ^ 6`: on the nonnegative reals
the sixth power lies above its tangent line at `a`. The difference of the two sides is
`(r - a) ^ 2` times a polynomial in `r`, `a` with positive coefficients. -/
theorem pow_add_mul_sub_le_pow_six {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) :
    a ^ 6 + 6 * a ^ 5 * (r - a) ≤ r ^ 6 := by
  have h1 : r ^ 6 - (a ^ 6 + 6 * a ^ 5 * (r - a)) =
      (r - a) ^ 2 * (r ^ 4 + 2 * r ^ 3 * a + 3 * r ^ 2 * a ^ 2 + 4 * r * a ^ 3 + 5 * a ^ 4) := by
    ring
  have h2 : 0 ≤ (r - a) ^ 2 *
      (r ^ 4 + 2 * r ^ 3 * a + 3 * r ^ 2 * a ^ 2 + 4 * r * a ^ 3 + 5 * a ^ 4) := by
    positivity
  linarith

/-- For real `a`, `b` and `w₀ > 0`, `a * b ≤ (b ^ 2 + w₀ * a ^ 2) / (2 * √w₀)`. This follows from
`(√w₀ * a - b) ^ 2 ≥ 0`. -/
theorem mul_le_sq_add_mul_sq_div {a b w₀ : ℝ} (hw : 0 < w₀) :
    a * b ≤ (b ^ 2 + w₀ * a ^ 2) / (2 * Real.sqrt w₀) := by
  have hs : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw
  rw [le_div_iff₀ (by positivity)]
  have h2 : Real.sqrt w₀ ^ 2 = w₀ := Real.sq_sqrt hw.le
  nlinarith [sq_nonneg (Real.sqrt w₀ * a - b), h2]

/-- For a real `δ > 0` and every natural number `n`, `0 < δ / (n + 2)`. -/
theorem div_natCast_add_two_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < δ / ((n : ℝ) + 2) := by
    positivity

/-- For a real `δ > 0` and every natural number `n`, `δ / (n + 2) < δ`. -/
theorem div_natCast_add_two_lt_self {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : δ / ((n : ℝ) + 2) < δ := by
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- For real `a`, `b`, `c`, `|a + b - c| ≤ |a| + |b| + |c|`. -/
theorem abs_add_sub_le_abs_add_abs_add_abs (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b,
    le_abs_self c, neg_abs_le c]

/-- For every real `A`, `A ^ 4 ≤ A ^ 2 + A ^ 6`. -/
theorem pow_four_le_sq_add_pow_six (A : ℝ) : A ^ 4 ≤ A ^ 2 + A ^ 6 := by
  nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg (A ^ 2 - 1 / 2)), sq_nonneg A]

/-- For every real `A`, `A ^ 3 ≤ A ^ 2 + A ^ 6`. -/
theorem cube_le_sq_add_pow_six (A : ℝ) : A ^ 3 ≤ A ^ 2 + A ^ 6 := by
  nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg (A ^ 2 - 1 / 2)),
    mul_nonneg (sq_nonneg A) (sq_nonneg (A - 1 / 2)), sq_nonneg A]

/-- For nonnegative reals `M`, `x`, `z`, `M * x ^ 3 * z ≤ x ^ 4 + M ^ 4 * z ^ 4`. With
`y = M * z`, the inequality `(x - y) ^ 2 * (3 * x ^ 2 + 2 * x * y + y ^ 2) ≥ 0` gives
`4 * x ^ 3 * y ≤ 3 * x ^ 4 + y ^ 4`. -/
theorem mul_cube_mul_le_pow_four_add {M x z : ℝ} (hM : 0 ≤ M) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    M * x ^ 3 * z ≤ x ^ 4 + M ^ 4 * z ^ 4 := by
  have hy : 0 ≤ M * z := mul_nonneg hM hz
  have h := mul_nonneg (sq_nonneg (x - M * z))
    (by positivity : (0 : ℝ) ≤ 3 * x ^ 2 + 2 * x * (M * z) + (M * z) ^ 2)
  nlinarith [pow_nonneg hx 4, pow_nonneg hy 4]

/-- For reals with `s ≥ 0`, `t ≥ 0`, `ℓ > 0`, `β > 0`, `2 * (s * p1 * q1 + t * (p2 * q3 + q2 * p3))`
is at most `β * (s * p1 ^ 2 + t * (ℓ * p3 ^ 2 + p2 ^ 2 / ℓ))` plus
`β⁻¹ * (s * q1 ^ 2 + t * (ℓ * q3 ^ 2 + q2 ^ 2 / ℓ))`. The three products are bounded by
`2 * x * y ≤ c * x ^ 2 + c⁻¹ * y ^ 2`, with `c = β`, `β / ℓ` and `β * ℓ`. -/
theorem two_mul_add_le_mul_add_inv (s t ℓ β p1 p2 p3 q1 q2 q3 : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hℓ : 0 < ℓ)
    (hβ : 0 < β) :
    2 * (s * p1 * q1 + t * (p2 * q3 + q2 * p3)) ≤
      β * (s * p1 ^ 2 + t * (ℓ * p3 ^ 2 + p2 ^ 2 / ℓ)) + β⁻¹ *
          (s * q1 ^ 2 + t * (ℓ * q3 ^ 2 + q2 ^ 2 / ℓ)) := by
  have y1 := mul_le_mul_of_nonneg_left (two_mul_le_add_mul_sq (a := p1) (b := q1) hβ) hs
  have y2 := mul_le_mul_of_nonneg_left (two_mul_le_add_mul_sq (a := p2) (b := q3) (ε := β / ℓ) (by
    positivity)) ht
  have y3 := mul_le_mul_of_nonneg_left (two_mul_le_add_mul_sq (a := p3) (b := q2) (ε := β * ℓ) (by
    positivity)) ht
  have e : β * (s * p1 ^ 2 + t * (ℓ * p3 ^ 2 + p2 ^ 2 / ℓ)) + β⁻¹ *
      (s * q1 ^ 2 + t * (ℓ * q3 ^ 2 + q2 ^ 2 / ℓ))
      = s * (β * p1 ^ 2 + β⁻¹ * q1 ^ 2) + t * (β / ℓ * p2 ^ 2 + (β / ℓ)⁻¹ * q3 ^ 2)
        + t * (β * ℓ * p3 ^ 2 + (β * ℓ)⁻¹ * q2 ^ 2) := by
    field_simp
    ring
  rw [e]
  nlinarith

/-- A bound for a sum of `terms` equal terms, with sixteen hypotheses. Let `0 < θ`, `1 ≤ θ⁻¹`,
`j ≤ j₀`, `0 ≤ Z`, `M₁ = CA * Cad * CA`, `M₂ = CA * (Crt * (CTL * CA) + CRR * (CRL * CA))`,
`0 ≤ M₁`, `0 ≤ M₂`, `N = θ⁻¹ ^ j₀ * (terms + 1)`, `0 < N`, `δ = η / (2 * N * (M₁ + 1))`, `0 ≤ δ`,
`r = η / (8 * N * (M₂ + 1))`, `0 ≤ r` and `0 ≤ ε ≤ r ^ 4`. Then
`‖θ⁻¹ ^ j‖ * (terms * (CA * (δ * (Cad * CA * Z)) + 4 * (M₂ * Z) * ε ^ (1 / 4))) ≤ η * Z`, with `M₂`
written out. The proof bounds `ε ^ (1 / 4)` by `r` and `δ * M₁` by `η / (2 * N)`. -/
theorem norm_inv_pow_mul_natCast_mul_le {θ η N M₁ M₂ δ r ε Z CA Cad Crt CTL CRR CRL : ℝ}
    {j j₀ terms : ℕ}
    (hθ0 : 0 < θ) (hθi : 1 ≤ θ⁻¹) (hj : j ≤ j₀) (hZ : 0 ≤ Z) (hM₁ : M₁ = CA * Cad * CA)
    (hM₂ : M₂ = CA * (Crt * (CTL * CA) + CRR * (CRL * CA))) (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂)
    (hN : N = (θ⁻¹) ^ j₀ * ((terms : ℝ) + 1)) (hN0 : 0 < N) (hδ : δ = η / (2 * N * (M₁ + 1)))
    (hδ0 : 0 ≤ δ) (hr : r = η / (8 * N * (M₂ + 1))) (hr0 : 0 ≤ r) (hε0 : 0 ≤ ε) (hεr : ε ≤ r ^ 4) :
    ‖(θ⁻¹) ^ j‖ * ((terms : ℝ) * (CA * (δ * (Cad * CA * Z)) +
      4 * (CA * (Crt * (CTL * CA) + CRR * (CRL * CA)) * Z) * ε ^ (1 / 4 : ℝ))) ≤ η * Z := by
  have hq : ε ^ (1 / 4 : ℝ) ≤ r := rpow_quarter_le hr0 hε0 hεr
  have hB : CA * (δ * (Cad * CA * Z)) + 4 * (CA * (Crt * (CTL * CA) + CRR * (CRL * CA)) * Z) *
      ε ^ (1 / 4 : ℝ) = Z * (δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ)) := by
    rw [hM₁, hM₂]; ring
  rw [hB]
  have hq0 : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε0 _
  have h1 : δ * M₁ ≤ η / (2 * N) := by
    calc δ * M₁ ≤ δ * (M₁ + 1) := by nlinarith
      _ = η / (2 * N) := by rw [hδ]; field_simp
  have h2 : 4 * M₂ * ε ^ (1 / 4 : ℝ) ≤ η / (2 * N) := by
    calc 4 * M₂ * ε ^ (1 / 4 : ℝ) ≤ 4 * (M₂ + 1) * r :=
          mul_le_mul (by linarith) hq hq0 (by linarith)
      _ = η / (2 * N) := by rw [hr]; field_simp; ring
  have hsum : η / (2 * N) + η / (2 * N) = η / N := by field_simp; ring
  have hQ : δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ) ≤ η / N := by linarith
  have hQ0 : 0 ≤ δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ) := by positivity
  have hθp : 0 < θ⁻¹ := inv_pos.2 hθ0
  have hpow : ‖(θ⁻¹) ^ j‖ ≤ (θ⁻¹) ^ j₀ := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_pos hθp]
    exact pow_le_pow_right₀ hθi hj
  have hterms : (θ⁻¹) ^ j₀ * (terms : ℝ) ≤ N := by
    rw [hN]
    have := pow_pos hθp j₀
    nlinarith
  have ht0 : (0 : ℝ) ≤ terms := Nat.cast_nonneg _
  calc ‖(θ⁻¹) ^ j‖ * ((terms : ℝ) * (Z * (δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ)))) ≤
        (θ⁻¹) ^ j₀ * ((terms : ℝ) * (Z * (δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ)))) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = ((θ⁻¹) ^ j₀ * terms) * (δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ)) * Z := by ring
    _ ≤ N * (η / N) * Z := mul_le_mul_of_nonneg_right (mul_le_mul hterms hQ hQ0 hN0.le) hZ
    _ = η * Z := by field_simp

end PDE.Analysis
