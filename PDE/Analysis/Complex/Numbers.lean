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

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import PDE.Analysis.Scalar.Inequalities

set_option linter.style.header false

/-!
# Complex numbers: parts, conjugation, modulus

The lemmas compute real and imaginary parts of products and sums, relate a complex number to its
conjugate and its modulus, and bound the modulus of a sum or a product. The proofs use
`Complex.ext`, the lemmas of Mathlib on `Complex.normSq` and the norm, and `ring`.

## Main results

* `PDE.Analysis.ofReal_sum_re_eq_sum_of_conj`: Let `s` be a finite subset of `ℤ × ℤ` closed under
  negation and `z : ℤ × ℤ → ℂ` with `z (-α) = conj (z α)` for all `α`. Then `∑ α ∈ s, z α` is real:
  `((∑ α ∈ s, (z α).re : ℝ) : ℂ) = ∑ α ∈ s, z α`. Reindexing by `α ↦ -α` shows that the sum equals
  the sum of the conjugates.
* `PDE.Analysis.abs_re_I_mul_le`: For a real `e` and a complex `c`,
  `|(Complex.I * (e : ℂ) * c).re| ≤ |e| * ‖c‖`.
* `PDE.Analysis.I_mul_ofReal_mul_ofReal_mul`: For real `a`, `c` and a complex `z`,
  `Complex.I * (a : ℂ) * ((c : ℂ) * z) = Complex.I * ((a * c : ℝ) : ℂ) * z`.
* `PDE.Analysis.re_sum_real_mul`: For `c : Fin 3 → ℝ` and `z : Fin 3 → ℂ`,
  `(∑ k, (c k : ℂ) * z k).re = ∑ k, c k * (z k).re`.
* `PDE.Analysis.I_div_mul_sum_eq_of_proportional`: Let `a g : Fin 3 → ℂ` and `n : ℂ` with `n ≠ 0`,
  `n ^ 2 = ∑ k, a k ^ 2` and `a k * g j = a j * g k` for all `j`, `k`. Then
  `Complex.I * a j / n * ∑ k, (-(Complex.I * a k / n)) * g k = g j` for every `j`.
* `PDE.Analysis.abs_re_conj_mul_le`: For complex numbers `z` and `w`,
  `|(conj z * w).re| ≤ ‖z‖ * ‖w‖`.
* `PDE.Analysis.add_mul_eq_of_ofReal_mul_eq`: Let `c`, `o`, `r` be real with `c ≠ 0` and
  `c - o ≠ 0`, and let `F`, `dF`, `W`, `dW`, `T` be complex with `r * F = W` and `r * dF = dW - F`.
  Then `(1 / (c - o) * F + (r - o) / (c - o) * dF) * T = 1 / c * ((1 / (c - o) * W + (r - o) / (c -
  o) * dW) * T) + ((c + o - 2 * r) / (c * (c - o)) * F + (r - o) * (c - r) / (c * (c - o)) * dF) *
  T`, where each real coefficient is cast to `ℂ`.
* `PDE.Analysis.eval_real_map_conj`: For real `t`, `x` and `P : MvPolynomial (Fin 2) ℂ`, evaluating
  the polynomial with conjugated coefficients `MvPolynomial.map conj P` at the real point
  `![(t : ℂ), (x : ℂ)]` gives the conjugate of the value of `P` at that point.

There are 68 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Real

namespace PDE.Analysis

/-- Let `a g : Fin 3 → ℂ` and `n : ℂ` with `n ≠ 0`, `n ^ 2 = ∑ k, a k ^ 2` and
`a k * g j = a j * g k` for all `j`, `k`. Then
`Complex.I * a j / n * ∑ k, (-(Complex.I * a k / n)) * g k = g j` for every `j`. The proof uses
`∑ k, a j * a k * g k = n ^ 2 * g j`, which follows from the hypotheses, and `Complex.I ^ 2 = -1`.
-/
theorem I_div_mul_sum_eq_of_proportional (a g : Fin 3 → ℂ) (n : ℂ) (hn : n ≠ 0)
    (hn2 : n ^ 2 = ∑ k, a k ^ 2)
    (hc : ∀ j k, a k * g j = a j * g k) (j : Fin 3) :
    Complex.I * a j / n * ∑ k, (-(Complex.I * a k / n)) * g k = g j := by
  have key : ∑ k, a j * a k * g k = n ^ 2 * g j := by
    rw [hn2, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ ↦ by linear_combination (-(a k)) * hc j k)
  have hterm : ∀ k, Complex.I * a j / n * (-(Complex.I * a k / n) * g k) = a j * a k * g k /
      n ^ 2 := by
    intro k
    field_simp
    linear_combination (-(a j * a k * g k)) * Complex.I_sq
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ ↦ hterm k), ← Finset.sum_div, key,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hn)]

/-- For real `a`, `c` and a complex `z`,
`Complex.I * (a : ℂ) * ((c : ℂ) * z) = Complex.I * ((a * c : ℝ) : ℂ) * z`. -/
theorem I_mul_ofReal_mul_ofReal_mul (a c : ℝ) (z : ℂ) :
    Complex.I * (a : ℂ) * ((c : ℂ) * z) = Complex.I * ((a * c : ℝ) : ℂ) * z := by
  push_cast
  ring

/-- For a real `e` and a complex `c`, `|(Complex.I * (e : ℂ) * c).re| ≤ |e| * ‖c‖`. -/
theorem abs_re_I_mul_le (e : ℝ) (c : ℂ) : |(Complex.I * (e : ℂ) * c).re| ≤ |e| * ‖c‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- For complex numbers `z` and `w`, `|(conj z * w).re| ≤ ‖z‖ * ‖w‖`. -/
theorem abs_re_conj_mul_le (z w : ℂ) : |((starRingEnd ℂ) z * w).re| ≤ ‖z‖ * ‖w‖ := by
  calc |((starRingEnd ℂ) z * w).re| ≤ ‖(starRingEnd ℂ) z * w‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]

/-- Let `c`, `o`, `r` be real with `c ≠ 0` and `c - o ≠ 0`, and let `F`, `dF`, `W`, `dW`, `T` be
complex with `r * F = W` and `r * dF = dW - F`. Then
`(1 / (c - o) * F + (r - o) / (c - o) * dF) * T = 1 / c * ((1 / (c - o) * W + (r - o) / (c - o) *
dW) * T) + ((c + o - 2 * r) / (c * (c - o)) * F + (r - o) * (c - r) / (c * (c - o)) * dF) *
T`, where each real coefficient is cast to `ℂ`. The proof substitutes `W` and `dW` and clears the
denominators. -/
theorem add_mul_eq_of_ofReal_mul_eq (c o r : ℝ) (hc : c ≠ 0) (hco : c - o ≠ 0) (F dF W dW T : ℂ)
    (e1 : (r : ℂ) * F = W) (e2 : (r : ℂ) * dF = dW - F) :
    ((((1 / (c - o) : ℝ)) : ℂ) * F + (((r - o) / (c - o) : ℝ) : ℂ) * dF) * T =
      ((1 / c : ℝ) : ℂ) * (((((1 / (c - o) : ℝ)) : ℂ) * W + (((r - o) / (c - o) : ℝ) : ℂ) * dW) * T)
        + ((((c + o - 2 * r) / (c * (c - o)) : ℝ) : ℂ) * F
          + ((((r - o) * (c - r)) / (c * (c - o)) : ℝ) : ℂ) * dF) * T := by
  have hdW : dW = (r : ℂ) * dF + F := by linear_combination (-1 : ℂ) * e2
  subst e1
  subst hdW
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hco' : (c : ℂ) - (o : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast hco
  push_cast
  field_simp
  ring

/-- For complex `X`, `Y` and a real `s` with `s * s = 1`, if `Y = (s : ℂ) * X` then
`X = (s : ℂ) * Y`. -/
theorem eq_sign_mul_of_eq_sign_mul {X Y : ℂ} {s : ℝ} (hs : s * s = 1) (e : Y = (s : ℂ) * X) :
    X = (s : ℂ) * Y := by
  rw [e, ← mul_assoc, ← Complex.ofReal_mul, hs, Complex.ofReal_one, one_mul]

/-- For real `t`, `x` and `P : MvPolynomial (Fin 2) ℂ`, evaluating the polynomial with conjugated
coefficients `MvPolynomial.map conj P` at the real point `![(t : ℂ), (x : ℂ)]` gives the conjugate
of the value of `P` at that point. -/
theorem eval_real_map_conj (t x : ℝ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.map (starRingEnd ℂ) P) =
      starRingEnd ℂ (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] P) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left]
  congr 1
  funext k
  fin_cases k <;> simp

/-- For `f : ι → ℂ`, conjugating the values of `star f` pointwise gives back `f`:
`(fun i ↦ conj ((star f) i)) = f`. -/
theorem fun_conj_star_apply_eq_self {ι : Type} (f : ι → ℂ) : (fun i ↦ (starRingEnd ℂ) ((star f) i))
    = f := by
  funext i
  simp [Pi.star_apply]

/-- For a complex `x` and integers `a`, `b`,
`(if a = 0 then x * (if b = 0 then 2 * π else 0) else 0) = (if a = 0 ∧ b = 0 then x else 0) * (2 *
π)` in `ℂ`. -/
theorem ite_mul_ite_eq_ite_and_mul (x : ℂ) (a b : ℤ) :
    (if a = 0 then x * (if b = 0 then (2 * Real.pi : ℂ) else 0) else 0) =
      (if a = 0 ∧ b = 0 then x else 0) * (2 * Real.pi : ℂ) := by
  split_ifs <;> simp_all

/-- For a Boolean `odd`, the complex sign `if odd then -1 else 1` multiplied by itself is `1`. -/
theorem ite_neg_one_one_mul_self (odd : Bool) :
    (if odd then -1 else 1 : ℂ) * (if odd then -1 else 1) = 1 := by
  cases odd <;> norm_num

/-- For a Boolean `odd`, the complex sign `if !odd then -1 else 1` is the negative of
`if odd then -1 else 1`. -/
theorem ite_not_neg_one_eq_neg_ite (odd : Bool) : (if !odd then -1 else 1 : ℂ) =
    -(if odd then -1 else 1 : ℂ) := by
  cases odd <;> simp

/-- For real `k` and complex `x`, `w`:
`k ^ 2 * ‖x‖ ^ 2 + ‖w‖ ^ 2 - 2 * |k| * (‖x‖ * ‖w‖) ≤ ‖Complex.I * k * x + w‖ ^ 2`. The left side is
`(|k| * ‖x‖ - ‖w‖) ^ 2`, so the proof squares the reverse triangle inequality for
`Complex.I * k * x` and `w`. -/
theorem le_norm_I_mul_add_sq (k : ℝ) (x w : ℂ) :
    k ^ 2 * ‖x‖ ^ 2 + ‖w‖ ^ 2 - 2 * |k| * (‖x‖ * ‖w‖) ≤ ‖Complex.I * k * x + w‖ ^ 2 := by
  have h1 : ‖Complex.I * k * x‖ = |k| * ‖x‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have h2 : ‖Complex.I * k * x‖ - ‖w‖ ≤ ‖Complex.I * k * x + w‖ := by
    have := norm_sub_norm_le (Complex.I * k * x) (-w)
    simpa [sub_neg_eq_add] using this
  have h3 : ‖w‖ - ‖Complex.I * k * x‖ ≤ ‖Complex.I * k * x + w‖ := by
    have := norm_sub_norm_le w (-(Complex.I * k * x))
    rw [sub_neg_eq_add, add_comm, norm_neg] at this
    exact this
  have h4 : (|k| * ‖x‖ - ‖w‖) ^ 2 ≤ ‖Complex.I * k * x + w‖ ^ 2 := by
    rw [← h1]
    apply sq_le_sq'
    · linarith
    · exact h2
  have hk : |k| ^ 2 = k ^ 2 := sq_abs k
  nlinarith [h4]

/-- For real `k` and complex `w0`, `w1`, `w2`:
`(max (|k| - 1) 0) ^ 2 * (‖w0‖ ^ 2 + ‖w1‖ ^ 2 + ‖w2‖ ^ 2) ≤ ‖Complex.I * k * w0 - w1‖ ^ 2 +
‖Complex.I * k * w1 + w0‖ ^ 2 + ‖Complex.I * k * w2‖ ^
2`. The proof expands the norms in real and imaginary parts, bounds the first two terms below by
`(|k| - 1) ^ 2 * (‖w0‖ ^ 2 + ‖w1‖ ^ 2)` according to the sign of `k`, and uses that the third term
is `k ^ 2 * ‖w2‖ ^ 2`. -/
theorem max_abs_sub_one_sq_mul_le (k : ℝ) (w0 w1 w2 : ℂ) :
    (max (|k| - 1) 0) ^ 2 * (‖w0‖ ^ 2 + ‖w1‖ ^ 2 + ‖w2‖ ^ 2) ≤
      ‖Complex.I * k * w0 - w1‖ ^ 2 + ‖Complex.I * k * w1 + w0‖ ^ 2 + ‖Complex.I * k * w2‖ ^ 2 := by
  have hm1 : (max (|k| - 1) 0) ^ 2 ≤ (|k| - 1) ^ 2 := by
    rcases le_total (|k| - 1) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (|k| - 1)]
    · rw [max_eq_left h]
  have hm2 : (max (|k| - 1) 0) ^ 2 ≤ k ^ 2 := by
    rcases le_total (|k| - 1) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg k]
    · rw [max_eq_left h, ← sq_abs k]
      exact pow_le_pow_left₀ h (by linarith) 2
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  set a := w0.re
  set b := w0.im
  set c := w1.re
  set d := w1.im
  set e := w2.re
  set f := w2.im
  have hS : 0 ≤ a * a + b * b + (c * c + d * d) := by
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hT : 0 ≤ e * e + f * f := by nlinarith [sq_nonneg e, sq_nonneg f]
  have key : (|k| - 1) ^ 2 * (a * a + b * b + (c * c + d * d)) ≤
      (k * b + c) ^ 2 + (k * a - d) ^ 2 + ((a - k * d) ^ 2 + (b + k * c) ^ 2) := by
    rcases le_total 0 k with h | h
    · rw [abs_of_nonneg h]
      nlinarith [mul_nonneg h (sq_nonneg (a - d)), mul_nonneg h (sq_nonneg (b + c))]
    · rw [abs_of_nonpos h]
      nlinarith [mul_nonneg (neg_nonneg.2 h) (sq_nonneg (a + d)),
          mul_nonneg (neg_nonneg.2 h) (sq_nonneg (b - c))]
  have k3 : k ^ 2 * (e * e + f * f) = (k * f) ^ 2 + (k * e) ^ 2 := by ring
  nlinarith [mul_le_mul_of_nonneg_right hm1 hS, mul_le_mul_of_nonneg_right hm2 hT]

/-- For complex numbers `s`, `c`, `Y` with `s * s = 1`, `c * Y = s * (c * (s * Y))`. -/
theorem mul_eq_sign_mul_mul_sign_mul (s c Y : ℂ) (h : s * s = 1) : c * Y = s * (c * (s * Y)) := by
  linear_combination (-(c * Y)) * h

/-- For integers `a`, `b` and complex `K`, `c`,
`(c * if b = 0 then K else 0) * (if a = 0 then 1 else 0) = if a = 0 ∧ b = 0 then K * c else 0`. -/
theorem mul_ite_mul_ite_eq_ite_and (a b : ℤ) (K c : ℂ) :
    (c * if b = 0 then K else 0) * (if a = 0 then 1 else 0) = if a = 0 ∧ b = 0 then K * c else 0 :=
        by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, mul_comm]

/-- For complex numbers with `W * T = s2 * R`,
`a * b * W * c * (T * g) = s2 * (R * a * (b * c * g))`. -/
theorem mul_mul_eq_of_mul_eq_mul {a b c g W T R s2 : ℂ} (h : W * T = s2 * R) :
    a * b * W * c * (T * g) = s2 * (R * a * (b * c * g)) := by
  linear_combination (a * b * c * g) * h

/-- For `P : MvPolynomial (Fin 2) ℂ`, conjugating the coefficients twice gives back `P`:
`MvPolynomial.map conj (MvPolynomial.map conj P) = P`. -/
theorem mvPolynomial_map_conj_map_conj (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have h : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z ↦ by simp
  rw [h, MvPolynomial.map_id]

/-- For complex `a`, `n`: `-(Complex.I * a / n) * (2 * π * Complex.I * a) = 2 * π * a ^ 2 / n`. No
hypothesis `n ≠ 0` is needed, since both sides are `0` when `n = 0`. -/
theorem neg_I_div_mul_two_pi_I (a n : ℂ) :
    -(Complex.I * a / n) * (2 * π * Complex.I * a) = 2 * π * a ^ 2 / n := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- For complex numbers `A` and `B`, `‖A + Complex.I * B‖ ≤ ‖A‖ + ‖B‖`. -/
theorem norm_add_I_mul_le (A B : ℂ) : ‖A + Complex.I * B‖ ≤ ‖A‖ + ‖B‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]

/-- For complex numbers `x` and `y`, `‖x + Complex.I * y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2`. -/
theorem norm_add_I_mul_sq_le (x y : ℂ) : ‖x + Complex.I * y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x (Complex.I * y)
  rw [norm_mul, Complex.norm_I, one_mul] at h
  nlinarith [norm_nonneg (x + Complex.I * y), norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]

/-- For complex numbers `x` and `y`, `‖(x + y) / 2‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2`. -/
theorem norm_add_div_two_sq_le (x y : ℂ) : ‖(x + y) / 2‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  rw [norm_div, Complex.norm_two, div_pow]
  have h1 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- For real numbers `a`, `b`, `s` with `s ^ 2 = 1`,
`‖(a : ℂ) + (s : ℂ) * Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2`. -/
theorem norm_add_sign_mul_I_mul_sq (a b s : ℝ) (hs : s ^ 2 = 1) :
    ‖(a : ℂ) + (s : ℂ) * Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have h : (a : ℂ) + (s : ℂ) * Complex.I * (b : ℂ) = (a : ℂ) + ((s * b : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have h' : (s * b) ^ 2 = s ^ 2 * b ^ 2 := by ring
  rw [h', hs, one_mul]

/-- For complex numbers `a` and `b`, `‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (b * conj a).re`. -/
theorem norm_add_sq_re_mul_conj_left (a b : ℂ) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (b * (starRingEnd ℂ) a).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- For complex numbers `y` and `w`, `‖y + w‖ ^ 2 = ‖y‖ ^ 2 + 2 * (y * conj w).re + ‖w‖ ^ 2`. -/
theorem norm_add_sq_re_mul_conj_right (y w : ℂ) :
    ‖y + w‖ ^ 2 = ‖y‖ ^ 2 + 2 * (y * (starRingEnd ℂ) w).re + ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]; ring

/-- For complex `u`, `A`, `w`: if `‖A‖ ≤ CA`, `‖u‖ ^ 2 ≤ EU` and `‖w‖ ^ 2 ≤ EW`, then
`‖(starRingEnd ℂ) u * A * w‖ ≤ CA * (EU + EW)`. -/
theorem norm_conj_mul_mul_le_mul_add (u w : ℂ) (A : ℂ) (CA : ℝ) (hA : ‖A‖ ≤ CA) (EU EW : ℝ)
    (hu : ‖u‖ ^ 2 ≤ EU) (hw : ‖w‖ ^ 2 ≤ EW) :
    ‖(starRingEnd ℂ) u * A * w‖ ≤ CA * (EU + EW) := by
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have h0 : 0 ≤ CA := le_trans (norm_nonneg _) hA
  have h1 : ‖u‖ * ‖w‖ ≤ EU + EW := by
    nlinarith [sq_nonneg (‖u‖ - ‖w‖), norm_nonneg u, norm_nonneg w]
  calc ‖u‖ * ‖A‖ * ‖w‖ = ‖A‖ * (‖u‖ * ‖w‖) := by ring
    _ ≤ CA * (EU + EW) := mul_le_mul hA h1 (by positivity) h0

/-- For a nonzero complex number `w`, the quotient `w / ‖w‖`, with `‖w‖` coerced to `ℂ`, has norm
`1`. -/
theorem norm_div_norm_eq_one (w : ℂ) (hw : w ≠ 0) : ‖w / (‖w‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact div_self (norm_ne_zero_iff.mpr hw)

/-- For a nonzero complex number `w`, the product `(‖w‖ : ℂ)⁻¹ * w` has norm `1`. -/
theorem norm_inv_norm_mul_eq_one {w : ℂ} (hw : w ≠ 0) : ‖(‖w‖ : ℂ)⁻¹ * w‖ = 1 := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw',
      inv_mul_cancel₀ hw'.ne']

/-- For nonzero complex numbers `w` and `v`,
`‖(‖w‖ : ℂ)⁻¹ * w - (‖v‖ : ℂ)⁻¹ * v‖ ≤ 2 * ‖w - v‖ / ‖w‖`. The proof writes the difference as
`(‖w‖ : ℂ)⁻¹ * (w - v)` plus `((‖v‖ - ‖w‖) / (‖w‖ * ‖v‖)) * v` and uses `|‖v‖ - ‖w‖| ≤ ‖w - v‖`. -/
theorem norm_inv_norm_mul_sub_le {w v : ℂ} (hw : w ≠ 0) (hv : v ≠ 0) :
    ‖(‖w‖ : ℂ)⁻¹ * w - (‖v‖ : ℂ)⁻¹ * v‖ ≤ 2 * ‖w - v‖ / ‖w‖ := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have e : (‖w‖ : ℂ)⁻¹ * w - (‖v‖ : ℂ)⁻¹ * v =
      (‖w‖ : ℂ)⁻¹ * (w - v) + (((‖v‖ - ‖w‖) / (‖w‖ * ‖v‖) : ℝ) : ℂ) * v := by
    have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hw'.ne'
    have hm : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hv'.ne'
    push_cast
    field_simp
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs,
    abs_of_pos hw', abs_div, abs_of_pos (mul_pos hw' hv')]
  have h1 : |‖v‖ - ‖w‖| ≤ ‖w - v‖ := by
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le w v
  have e2 : |‖v‖ - ‖w‖| / (‖w‖ * ‖v‖) * ‖v‖ = |‖v‖ - ‖w‖| / ‖w‖ := by
    field_simp
  rw [e2, inv_mul_eq_div, ← add_div]
  apply div_le_div_of_nonneg_right _ hw'.le
  linarith

/-- For complex numbers with `‖ea‖ = 1`, `‖θw‖ = 1`, `‖φz‖ = 1` and `‖φw‖ = 1`,
`‖ea * (θz * φz) * Φz - ea * (θw * φw) * Φw‖ ≤ ‖θz - θw‖ * ‖Φz‖ + ‖φz - φw‖ * ‖Φz‖ + ‖Φz -
Φw‖`. The difference is `ea * ((θz - θw) * (φz * Φz) + θw * ((φz - φw) * Φz) + θw * φw * (Φz -
Φw))`, and the factors of norm `1` drop out of the triangle inequality. -/
theorem norm_mul_mul_sub_mul_mul_le {ea θz θw φz φw Φz Φw : ℂ} (hea : ‖ea‖ = 1) (hθw : ‖θw‖ = 1)
    (hφz : ‖φz‖ = 1)
    (hφw : ‖φw‖ = 1) :
    ‖ea * (θz * φz) * Φz - ea * (θw * φw) * Φw‖ ≤ ‖θz - θw‖ * ‖Φz‖ + ‖φz - φw‖ * ‖Φz‖ + ‖Φz -
        Φw‖ := by
  have e : ea * (θz * φz) * Φz - ea * (θw * φw) * Φw =
      ea * ((θz - θw) * (φz * Φz) + θw * ((φz - φw) * Φz) + θw * φw * (Φz - Φw)) := by ring
  rw [e, norm_mul, hea, one_mul]
  have n1 : ‖(θz - θw) * (φz * Φz)‖ = ‖θz - θw‖ * ‖Φz‖ := by rw [norm_mul, norm_mul, hφz, one_mul]
  have n2 : ‖θw * ((φz - φw) * Φz)‖ = ‖φz - φw‖ * ‖Φz‖ := by rw [norm_mul, norm_mul, hθw, one_mul]
  have n3 : ‖θw * φw * (Φz - Φw)‖ = ‖Φz - Φw‖ := by
    rw [norm_mul, norm_mul, hθw, hφw, one_mul, one_mul]
  rw [← n1, ← n2, ← n3]
  exact norm_add₃_le

/-- For complex `X`, `Y₂`, `Y₃`, `Y₄`, `Y₅`:
`‖-X + Y₂ + Y₃ + Y₄ + Y₅‖ ≤ ‖X‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖ + ‖Y₅‖`. -/
theorem norm_neg_add_add_add_add_le (X Y₂ Y₃ Y₄ Y₅ : ℂ) :
    ‖-X + Y₂ + Y₃ + Y₄ + Y₅‖ ≤ ‖X‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖ + ‖Y₅‖ := by
  have h1 := norm_add_le (-X + Y₂ + Y₃ + Y₄) Y₅
  have h2 := norm_add_le (-X + Y₂ + Y₃) Y₄
  have h3 := norm_add_le (-X + Y₂) Y₃
  have h4 := norm_add_le (-X) Y₂
  rw [norm_neg] at h4
  linarith

/-- For an integer `k` and a complex `z`,
`‖-((k : ℂ) * Complex.I) * z‖ ^ 2 = (k : ℝ) ^ 2 * ‖z‖ ^ 2`. -/
theorem norm_neg_intCast_mul_I_mul_sq (k : ℤ) (z : ℂ) :
    ‖-((k : ℂ) * Complex.I) * z‖ ^ 2 = (k : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, mul_one, mul_pow, Complex.norm_intCast, sq_abs]

/-- Triangle inequality for four complex numbers: `‖-X - Y + P + Q‖ ≤ ‖X‖ + ‖Y‖ + ‖P‖ + ‖Q‖`. -/
theorem norm_neg_sub_add_add_le (X Y P Q : ℂ) : ‖-X - Y + P + Q‖ ≤ ‖X‖ + ‖Y‖ + ‖P‖ + ‖Q‖ := by
  calc ‖-X - Y + P + Q‖ ≤ ‖-X - Y + P‖ + ‖Q‖ := norm_add_le _ _
    _ ≤ ‖-X - Y‖ + ‖P‖ + ‖Q‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖-X‖ + ‖Y‖ + ‖P‖ + ‖Q‖ := by gcongr; exact norm_sub_le _ _
    _ = ‖X‖ + ‖Y‖ + ‖P‖ + ‖Q‖ := by rw [norm_neg]

/-- For real `t`, `‖(t : ℂ) * Complex.I‖ = |t|`. -/
theorem norm_ofReal_mul_I (t : ℝ) : ‖(t : ℂ) * Complex.I‖ = |t| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Let `t` be real with `|t| ≤ 1` and `x`, `y`, `z` complex. If `‖x‖ * ‖y‖ ≤ T`, `‖z‖ ≤ L` and
`0 ≤ T`, then `‖(t : ℂ) * (x * (y * z))‖ ≤ L * T`. -/
theorem norm_ofReal_mul_mul_le_of_left {t : ℝ} (ht : |t| ≤ 1) {x y z : ℂ} {L T : ℝ}
    (hxy : ‖x‖ * ‖y‖ ≤ T) (hz : ‖z‖ ≤ L)
    (hT : 0 ≤ T) : ‖(t : ℂ) * (x * (y * z))‖ ≤ L * T := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖x‖ * ‖y‖ * ‖z‖ ≤ T * L := mul_le_mul hxy hz (norm_nonneg _) hT
  calc |t| * (‖x‖ * (‖y‖ * ‖z‖)) ≤ 1 * (‖x‖ * (‖y‖ * ‖z‖)) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
    _ = ‖x‖ * ‖y‖ * ‖z‖ := by ring
    _ ≤ T * L := h1
    _ = L * T := mul_comm _ _

/-- Let `t` be real with `|t| ≤ 1` and `x`, `y`, `z` complex. If `‖x‖ ≤ L`, `‖y‖ * ‖z‖ ≤ T` and
`0 ≤ L`, then `‖(t : ℂ) * (x * (y * z))‖ ≤ L * T`. -/
theorem norm_ofReal_mul_mul_le_of_right {t : ℝ} (ht : |t| ≤ 1) {x y z : ℂ} {L T : ℝ} (hx : ‖x‖ ≤ L)
    (hyz : ‖y‖ * ‖z‖ ≤ T)
    (hL : 0 ≤ L) : ‖(t : ℂ) * (x * (y * z))‖ ≤ L * T := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖x‖ * (‖y‖ * ‖z‖) ≤ L * T := mul_le_mul hx hyz (by positivity) hL
  calc |t| * (‖x‖ * (‖y‖ * ‖z‖)) ≤ 1 * (‖x‖ * (‖y‖ * ‖z‖)) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
    _ ≤ L * T := by rw [one_mul]; exact h1

/-- For a real `r` and a complex `z`, `‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2`. -/
theorem norm_ofReal_mul_sq (r : ℝ) (z : ℂ) : ‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- For a real `s` with `0 ≤ s ≤ 1` and natural numbers `a`, `n`, the complex number
`((s ^ a * (1 - s) ^ n : ℝ) : ℂ)` has norm at most `(1 - s) ^ n`, because `0 ≤ s ^ a ≤ 1`. -/
theorem norm_ofReal_pow_mul_pow_le (a n : ℕ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖((s ^ a * (1 - s) ^ n : ℝ) : ℂ)‖ ≤ (1 - s) ^ n := by
  have hu : 0 ≤ 1 - s := by linarith
  have hp : 0 ≤ s ^ a * (1 - s) ^ n := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  have : 0 ≤ (1 - s) ^ n := by positivity
  calc s ^ a * (1 - s) ^ n ≤ 1 * (1 - s) ^ n := mul_le_mul_of_nonneg_right (pow_le_one₀ h0 h1) this
    _ = (1 - s) ^ n := one_mul _

/-- For a real `t ≤ 1` and `z : ℕ`, `‖((t : ℂ) - 1) ^ z‖ = (1 - t) ^ z`. -/
theorem norm_ofReal_sub_one_pow (t : ℝ) (ht : t ≤ 1) (z : ℕ) : ‖((t : ℂ) - 1) ^ z‖ = (1 - t) ^ z :=
    by
  rw [norm_pow, show (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]

/-- For real `t`, `x` with `|t| ≤ 1` and `|x| ≤ 1`, every component of the vector
`![(t : ℂ), (x : ℂ)]` has norm at most `1`. -/
theorem norm_pair_ofReal_apply_le_one {t x : ℝ} (ht : |t| ≤ 1) (hx : |x| ≤ 1) :
    ∀ i, ‖(![(t : ℂ), (x : ℂ)] : Fin 2 → ℂ) i‖ ≤ 1 := by
  intro i
  fin_cases i
  · simpa [Complex.norm_real] using ht
  · simpa [Complex.norm_real] using hx

/-- For real `t`, `x`, `t'`, `x'`, the sum of the norms of the two componentwise differences of
`![(t : ℂ), (x : ℂ)]` and `![(t' : ℂ), (x' : ℂ)]` equals `|t - t'| + |x - x'|`. -/
theorem norm_pair_ofReal_sub_add_eq_abs (t x t' x' : ℝ) :
    ‖(![(t : ℂ), (x : ℂ)] : Fin 2 → ℂ) 0 - (![(t' : ℂ), (x' : ℂ)] : Fin 2 → ℂ) 0‖ +
      ‖(![(t : ℂ), (x : ℂ)] : Fin 2 → ℂ) 1 - (![(t' : ℂ), (x' : ℂ)] : Fin 2 → ℂ) 1‖ = |t -
          t'| + |x - x'| := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

/-- For complex numbers `a`, `b` with `‖a‖ ≤ 1` and `‖b‖ ≤ 1` and every `n : ℕ`,
`‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖`. The proof is by induction, using
`a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + (a ^ n - b ^ n) * b`. -/
theorem norm_pow_sub_pow_le (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ∀ n : ℕ, ‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖
  | 0 => by simp
  | n + 1 => by
    have ih := norm_pow_sub_pow_le a b ha hb n
    have e : a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + (a ^ n - b ^ n) * b := by ring
    have hn : ‖a ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
    rw [e]
    calc ‖a ^ n * (a - b) + (a ^ n - b ^ n) * b‖ ≤ ‖a ^ n‖ * ‖a - b‖ + ‖a ^ n - b ^ n‖ * ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖a - b‖ + (n * ‖a - b‖) * 1 := by
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * ‖a - b‖ := by push_cast; ring

/-- For a real `a`, `‖(a : ℂ) * Complex.I + 1 / 2‖ ^ 2 = a ^ 2 + 1 / 4`. -/
theorem norm_sq_ofReal_mul_I_add_half (a : ℝ) :
    ‖((a : ℝ) : ℂ) * Complex.I + 1 / 2‖ ^ 2 = a ^ 2 + 1 / 4 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

/-- For complex `x`, `y`, `‖(x - y) / 2‖ ^ 2 = ‖x - y‖ ^ 2 / 4`. -/
theorem norm_sub_div_two_sq (x y : ℂ) : ‖(x - y) / 2‖ ^ 2 = ‖x - y‖ ^ 2 / 4 := by
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, h3, div_pow]
  norm_num

/-- For complex numbers `x` and `y`, `‖(x - y) / 2‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2`. -/
theorem norm_sub_div_two_sq_le (x y : ℂ) : ‖(x - y) / 2‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  rw [norm_div, Complex.norm_two, div_pow]
  have h1 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Cauchy-Schwarz inequality for three complex products:
`‖a0 * u0 + a1 * u1 + a2 * u2‖ ≤ √(‖a0‖ ^ 2 + ‖a1‖ ^ 2 + ‖a2‖ ^ 2) * √(‖u0‖ ^ 2 + ‖u1‖ ^ 2 + ‖u2‖ ^
2)`. The proof uses the triangle inequality and then compares squares. -/
theorem norm_sum_three_mul_le_sqrt (a0 a1 a2 u0 u1 u2 : ℂ) :
    ‖a0 * u0 + a1 * u1 + a2 * u2‖ ≤
      Real.sqrt (‖a0‖ ^ 2 + ‖a1‖ ^ 2 + ‖a2‖ ^ 2) * Real.sqrt (‖u0‖ ^ 2 + ‖u1‖ ^ 2 + ‖u2‖ ^ 2) := by
  have h1 : ‖a0 * u0 + a1 * u1 + a2 * u2‖ ≤ ‖a0‖ * ‖u0‖ + ‖a1‖ * ‖u1‖ + ‖a2‖ * ‖u2‖ := by
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (le_of_eq (by
      rw [norm_mul, norm_mul]))) (le_of_eq (norm_mul _ _))
  refine h1.trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (‖a0‖ * ‖u1‖ - ‖a1‖ * ‖u0‖), sq_nonneg (‖a0‖ * ‖u2‖ - ‖a2‖ * ‖u0‖),
    sq_nonneg (‖a1‖ * ‖u2‖ - ‖a2‖ * ‖u1‖), norm_nonneg a0, norm_nonneg a1, norm_nonneg a2,
    norm_nonneg u0, norm_nonneg u1, norm_nonneg u2]

/-- For an integer `n`, `‖2 * π * Complex.I * (n : ℂ)‖ = 2 * π * |(n : ℝ)|`. -/
theorem norm_two_pi_I_mul_intCast (n : ℤ) : ‖(2 * π * Complex.I * (n : ℂ))‖ = 2 * π * |(n : ℝ)| :=
    by
  simp [abs_of_pos pi_pos]

/-- For real `t`, `‖2 * π * Complex.I * (t : ℂ)‖ = 2 * π * |t|`. -/
theorem norm_two_pi_I_mul_ofReal (t : ℝ) : ‖(2 * π * Complex.I * ((t : ℝ) : ℂ))‖ = 2 * π * |t| := by
  simp [abs_of_pos pi_pos]

/-- For real `A`, `B`, `z`, a real `h ≠ 0` and complex `F`, `Fr`, `Fz`, `Frz`,
`A * (1 / (0 - h)) * F + A * ((z - h) / (0 - h)) * Fz + B * (1 / (0 - h)) * Fr + B * ((z - h) / (0 -
h)) * Frz = A * (Fz * (1 - z / h) - F / h) + B * (Frz * (1 - z / h) - Fr /
h)`, where the real factors are cast to `ℂ`. -/
theorem ofReal_div_zero_sub_mul_add_eq (A B h z : ℝ) (hh : h ≠ 0) (F Fr Fz Frz : ℂ) :
    (A : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * F + (A : ℂ) * (((z - h) / (0 - h) : ℝ) : ℂ) * Fz
        + (B : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * Fr + (B : ℂ) * (((z - h) / (0 - h) : ℝ) : ℂ) * Frz
      = (A : ℂ) * (Fz * ((1 - z / h : ℝ) : ℂ) - F / (h : ℂ))
        + (B : ℂ) * (Frz * ((1 - z / h : ℝ) : ℂ) - Fr / (h : ℂ)) := by
  have hc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hc' : (0 : ℂ) - (h : ℂ) ≠ 0 := by rw [zero_sub]; exact neg_ne_zero.mpr hc
  push_cast
  field_simp
  ring

/-- Let `s` be a finite subset of `ℤ × ℤ` closed under negation and `z : ℤ × ℤ → ℂ` with
`z (-α) = conj (z α)` for all `α`. Then `∑ α ∈ s, z α` is real:
`((∑ α ∈ s, (z α).re : ℝ) : ℂ) = ∑ α ∈ s, z α`. Reindexing by `α ↦ -α` shows that the sum equals the
sum of the conjugates. -/
theorem ofReal_sum_re_eq_sum_of_conj (s : Finset (ℤ × ℤ)) (hs : ∀ α ∈ s, -α ∈ s) (z : ℤ × ℤ → ℂ)
    (hz : ∀ α, z (-α) = (starRingEnd ℂ) (z α)) :
    (((∑ α ∈ s, (z α).re : ℝ)) : ℂ) = ∑ α ∈ s, z α := by
  have hc : ∑ α ∈ s, (starRingEnd ℂ) (z α) = ∑ α ∈ s, z α :=
    Finset.sum_nbij' (fun α ↦ -α) (fun α ↦ -α) (fun a ha ↦ hs a ha) (fun a ha ↦ hs a ha)
      (fun a _ ↦ neg_neg a) (fun a _ ↦ neg_neg a) (fun a _ ↦ (hz a).symm)
  push_cast
  simp_rw [Complex.re_eq_add_conj]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hc]
  ring

/-- For complex `s`, `a`, `b`,
`(Complex.I * s * (a + b)).re = (Complex.I * s * a).re + (Complex.I * s * b).re`. -/
theorem re_I_mul_mul_add (s a b : ℂ) :
    (Complex.I * s * (a + b)).re = (Complex.I * s * a).re + (Complex.I * s * b).re := by
  rw [mul_add, Complex.add_re]

/-- For a real `a` and complex `s`, `c`, a real factor comes out of the real part:
`(Complex.I * s * ((a : ℂ) * c)).re = a * (Complex.I * s * c).re`. -/
theorem re_I_mul_mul_ofReal_mul (a : ℝ) (s c : ℂ) :
    (Complex.I * s * ((a : ℂ) * c)).re = a * (Complex.I * s * c).re := by
  rw [show Complex.I * s * ((a : ℂ) * c) = (a : ℂ) * (Complex.I * s * c) by
    ring, Complex.re_ofReal_mul]

/-- For complex numbers `z` and `w`, `(conj ((1 / 2) * z) * w).re = (1 / 2) * (conj w * z).re`. -/
theorem re_conj_half_mul_mul (z w : ℂ) :
    ((starRingEnd ℂ) ((1 / 2 : ℂ) * z) * w).re = (1 / 2) * ((starRingEnd ℂ) w * z).re := by
  simp only [map_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im, map_div₀, map_one,
      map_ofNat,
    Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im]
  norm_num
  ring

/-- For a complex number `w`, `(w / 2).re + (conj w / 2).re = w.re`. -/
theorem re_half_add_conj_half (w : ℂ) : (w / 2).re + (starRingEnd ℂ w / 2).re = w.re := by
  simp

/-- For integer pairs `ξ`, `ζ` and complex `A`, `B`,
`π * (if 2 * π * (ξ.1 - ζ.1) = 0 then 1 * (if ξ.2 = ζ.2 then A * conj B else 0).re else 0) + π * (if
2 * π * (ξ.1 + ζ.1) = 0 then 1 * (if ξ.2 = -ζ.2 then A * B else 0).re else 0) = π * ((if ξ = ζ then
A * conj B else 0) + (if ξ = -ζ then A * B else 0)).re`, where the integers `ξ.1 - ζ.1` and `ξ.1 +
ζ.1` are cast to `ℝ`. The proof turns the two conditions on first components into `ξ.1 = ζ.1` and
`ξ.1 = -ζ.1` and splits equality of pairs into components. -/
theorem re_ite_fst_ite_snd_add_eq (ξ ζ : ℤ × ℤ) (A B : ℂ) :
    Real.pi * (if 2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) = 0 then
        1 * ((if ξ.2 = ζ.2 then A * starRingEnd ℂ B else 0)).re else 0) +
      Real.pi * (if 2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) = 0 then
        1 * ((if ξ.2 = -ζ.2 then A * B else 0)).re else 0) =
      Real.pi * ((if ξ = ζ then A * starRingEnd ℂ B else 0) + (if ξ = -ζ then A * B else 0)).re :=
          by
  have c1 : (2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) = 0) ↔ ξ.1 = ζ.1 := by
    rw [mul_eq_zero, Int.cast_eq_zero, sub_eq_zero]
    simp [Real.pi_ne_zero]
  have c2 : (2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) = 0) ↔ ξ.1 = -ζ.1 := by
    rw [mul_eq_zero, Int.cast_eq_zero, eq_neg_iff_add_eq_zero]
    simp [Real.pi_ne_zero]
  have d1 : ξ = ζ ↔ ξ.1 = ζ.1 ∧ ξ.2 = ζ.2 := Prod.ext_iff
  have d2 : ξ = -ζ ↔ ξ.1 = -ζ.1 ∧ ξ.2 = -ζ.2 := Prod.ext_iff
  simp only [c1, c2, d1, d2, Complex.add_re]
  simp only [ite_and, one_mul, apply_ite Complex.re, Complex.zero_re]
  ring

/-- Polarization identity for complex numbers `a`, `b`:
`(a * conj b).re = (‖a + ((1 : ℝ) : ℂ) * b‖ ^ 2 - ‖a + ((-1 : ℝ) : ℂ) * b‖ ^ 2) / 4`. -/
theorem re_mul_conj_eq_norm_sq_sub (a b : ℂ) :
    (a * (starRingEnd ℂ) b).re = (‖a + ((1 : ℝ) : ℂ) * b‖ ^ 2 - ‖a + ((-1 : ℝ) : ℂ) * b‖ ^ 2) /
        4 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- For complex numbers `z` and `w`, the real part of `z * conj w` equals the real part of
`conj z * w`. -/
theorem re_mul_conj_eq_re_conj_mul (z w : ℂ) :
    (z * (starRingEnd ℂ) w).re = ((starRingEnd ℂ) z * w).re := by
  rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]

/-- For a complex number `z`, `(z * conj z).re = ‖z‖ ^ 2`. This is `sq_norm_eq_re_mul_conj` with the
two sides exchanged. -/
theorem re_mul_conj_self (z : ℂ) : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 :=
  (sq_norm_eq_re_mul_conj z).symm

/-- For complex numbers `u` and `w`, `u.re * w.re = (u * conj w).re / 2 + (u * w).re / 2`. -/
theorem re_mul_re_eq (u w : ℂ) : u.re * w.re = (u * starRingEnd ℂ w).re / 2 + (u * w).re / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- For `0 < τ`, the real part of the real number `1 / (4 * τ)` viewed in `ℂ` is positive. -/
theorem re_ofReal_one_div_four_mul_pos {τ : ℝ} (hτ : 0 < τ) : 0 < (((1 / (4 * τ) : ℝ) : ℂ)).re := by
  rw [Complex.ofReal_re]
  positivity

/-- For a complex number `z`, `(star z * z).re = ‖z‖ ^ 2`. -/
theorem re_star_mul_self {z : ℂ} : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

/-- For a finite set `s`, real coefficients `μ a` and complex numbers `z a`, the real part of
`∑ a ∈ s, (μ a : ℂ) * z a` is `∑ a ∈ s, μ a * (z a).re`. -/
theorem re_sum_ofReal_mul {ι : Type} (s : Finset ι) (μ : ι → ℝ) (z : ι → ℂ) :
    (∑ a ∈ s, ((μ a : ℝ) : ℂ) * z a).re = ∑ a ∈ s, μ a * (z a).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Complex.re_ofReal_mul]

/-- For `c : Fin 3 → ℝ` and `z : Fin 3 → ℂ`, `(∑ k, (c k : ℂ) * z k).re = ∑ k, c k * (z k).re`. -/
theorem re_sum_real_mul (c : Fin 3 → ℝ) (z : Fin 3 → ℂ) :
    (∑ k : Fin 3, ((c k : ℝ) : ℂ) * z k).re = ∑ k : Fin 3, c k * (z k).re := by
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun k _ ↦ Complex.re_ofReal_mul _ _

/-- For a decidable proposition `P` and a complex number `z`,
`star (if P then z else 0) = if P then star z else 0`. -/
theorem star_ite_zero (P : Prop) [Decidable P] (z : ℂ) :
    star (if P then z else 0) = if P then star z else 0 := by
  split_ifs <;> simp

/-- For real coefficients `c : Fin nE → ℝ` and a complex `X`,
`∑ β, (Complex.I * (c β : ℂ) * X).re = (Complex.I * ((∑ β, c β : ℝ) : ℂ) * X).re`. -/
theorem sum_re_I_mul_ofReal_mul {nE : ℕ} (c : Fin nE → ℝ) (X : ℂ) :
    ∑ β : Fin nE, (Complex.I * ((c β : ℝ) : ℂ) * X).re =
        (Complex.I * ((∑ β : Fin nE, c β : ℝ) : ℂ) * X).re := by
  rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.re_sum]

/-- Let `a0`, `a1`, `a2`, `n` be real with `n ^ 2 = a0 ^ 2 + a1 ^ 2 + a2 ^ 2`. Then the sum over
`j = 0, 1, 2` of `-(Complex.I * aj / n) * (2 * π * Complex.I * aj)`, computed in `ℂ`, equals
`2 * π * n`. The proof treats `n = 0` separately and otherwise uses `Complex.I ^ 2 = -1` and the
hypothesis. -/
theorem sum_three_neg_I_div_mul_eq (a0 a1 a2 n : ℝ) (hn : n ^ 2 = a0 ^ 2 + a1 ^ 2 + a2 ^ 2) :
    -(Complex.I * (a0 : ℂ) / (n : ℂ)) * (2 * (π : ℂ) * Complex.I * (a0 : ℂ)) +
      -(Complex.I * (a1 : ℂ) / (n : ℂ)) * (2 * (π : ℂ) * Complex.I * (a1 : ℂ)) +
      -(Complex.I * (a2 : ℂ) / (n : ℂ)) * (2 * (π : ℂ) * Complex.I * (a2 : ℂ)) =
      (((2 * π * n : ℝ)) : ℂ) := by
  rcases eq_or_ne n 0 with h0 | h0
  · subst h0
    simp
  · have hc : (n : ℂ) ≠ 0 := by exact_mod_cast h0
    have hnC : (n : ℂ) ^ 2 = (a0 : ℂ) ^ 2 + (a1 : ℂ) ^ 2 + (a2 : ℂ) ^ 2 := by exact_mod_cast hn
    calc _ = (2 * (π : ℂ) * ((a0 : ℂ) ^ 2 + (a1 : ℂ) ^ 2 + (a2 : ℂ) ^ 2)) * (-(Complex.I ^ 2)) /
             n := by
          ring
      _ = 2 * (π : ℂ) * (n : ℂ) ^ 2 / n := by rw [Complex.I_sq, neg_neg, mul_one, ← hnC]
      _ = (((2 * π * n : ℝ)) : ℂ) := by
          push_cast
          field_simp

/-- The complex number `2 * π`, with `π` cast from `ℝ`, is not zero. -/
theorem two_mul_ofReal_pi_ne_zero : (2 * Real.pi : ℂ) ≠ 0 := by
  have := Real.pi_pos
  exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)

/-- For a complex number `Z`, `2 * ((1 / 2 : ℂ) * Z).re ≤ ‖Z‖`. -/
theorem two_mul_re_half_mul_le_norm (Z : ℂ) : 2 * ((1 / 2 : ℂ) * Z).re ≤ ‖Z‖ := by
  have e : (1 / 2 : ℂ) * Z = ((1 / 2 : ℝ) : ℂ) * Z := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  have := Complex.re_le_norm Z
  linarith

/-- Let `0 < w` and `0 ≤ θ < 1` be real and `σ`, `μ`, `s`, `z` complex, with `s = w * μ` if `θ = 0`.
Then `0 ≤ w * ‖σ‖ ^ 2 + 2 * (conj s * σ).re + 2 * (σ * conj z).re + 2 * (μ * conj z).re +
(1 - θ)⁻¹ * (‖z‖ ^ 2 / w) - (w * ‖μ‖ ^ 2 - 2 * (conj μ * s).re - ‖s - w * μ‖ ^ 2 / (w * θ))`. For
`θ > 0` the right side is a sum of two completed squares in `σ + μ`, with weights `θ * w` and
`(1 - θ) * w`, and for `θ = 0` only the second one is needed. -/
theorem zero_le_norm_sq_add_re_sub {w θ : ℝ} (hw : 0 < w) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (σ μ s z : ℂ)
    (hE : θ = 0 → s = (w : ℂ) * μ) :
    0 ≤ w * ‖σ‖ ^ 2 + 2 * ((starRingEnd ℂ) s * σ).re + 2 * (σ * (starRingEnd ℂ) z).re
      + 2 * (μ * (starRingEnd ℂ) z).re + (1 - θ)⁻¹ * (‖z‖ ^ 2 / w)
      - (w * ‖μ‖ ^ 2 - 2 * ((starRingEnd ℂ) μ * s).re - ‖s - (w : ℂ) * μ‖ ^ 2 / (w * θ)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hB := mul_add_two_mul_add_div_nonneg (mul_pos h1θ hw) (σ.re + μ.re) (σ.im + μ.im) z.re z.im
  rcases hθ.lt_or_eq with hθp | hθ0
  · have hA := mul_add_two_mul_add_div_nonneg (mul_pos hθp hw) (σ.re + μ.re) (σ.im + μ.im)
      (s.re - w * μ.re) (s.im - w * μ.im)
    refine (add_nonneg hA hB).trans_eq ?_
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.conj_re,
      Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  · subst hθ0
    have hs := hE rfl
    subst hs
    refine hB.trans_eq ?_
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.conj_re,
      Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

/-- For real `k` and `x w : Fin 3 → Fin 3 → ℂ`:
`k ^ 2 * (∑ a, ∑ b, ‖x a b‖ ^ 2) + (∑ a, ∑ b, ‖w a b‖ ^ 2) - 2 * |k| * (∑ a, ∑ b, ‖x a b‖ * ‖w a b‖)
≤ ∑ a, ∑ b, ‖Complex.I * k * x a b + w a b‖ ^
2`. It is the sum over the nine index pairs of the same bound for one pair of complex numbers. -/
theorem le_sum_norm_I_mul_add_sq (k : ℝ) (x w : Fin 3 → Fin 3 → ℂ) :
    k ^ 2 * (∑ a : Fin 3, ∑ b : Fin 3, ‖x a b‖ ^ 2) + (∑ a : Fin 3, ∑ b : Fin 3, ‖w a b‖ ^ 2)
      - 2 * |k| * (∑ a : Fin 3, ∑ b : Fin 3, ‖x a b‖ * ‖w a b‖)
      ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖Complex.I * k * x a b + w a b‖ ^ 2 := by
  have h := fun a b ↦ le_norm_I_mul_add_sq k (x a b) (w a b)
  simp only [Fin.sum_univ_three] at *
  linarith [h 0 0, h 0 1, h 0 2, h 1 0, h 1 1, h 1 2, h 2 0, h 2 1, h 2 2]

/-- For real `t`, `‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I + ((t ^ 2 / 2 : ℝ) :
ℂ)‖ ≤ 3 * t ^ 2`. The proof bounds `‖exp (t * I) - 1 - t * I‖` by `2 * t ^
2`, using the quadratic remainder bound for `|t| ≤ 1` and the bound `|t| + |t|` for `|t| >
1`, and then adds `t ^ 2 / 2`. -/
theorem norm_exp_mul_I_taylor_le_sq (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I + ((t ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      3 * t ^ 2 := by
  have h2 : ‖((t ^ 2 / 2 : ℝ) : ℂ)‖ = t ^ 2 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hA : ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I‖ ≤ 2 * t ^ 2 := by
    rcases le_or_gt |t| 1 with ht | ht
    · have := Complex.norm_exp_sub_one_sub_id_le (x := (t : ℂ) * Complex.I)
        (by rw [norm_ofReal_mul_I]; exact ht)
      rw [norm_ofReal_mul_I, sq_abs] at this
      nlinarith [sq_nonneg t]
    · have h1 : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
        have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
        rw [mul_comm] at this
        simpa [Real.norm_eq_abs] using this
      have hsq : |t| ≤ t ^ 2 := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      calc ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I‖
          ≤ ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ + ‖(t : ℂ) * Complex.I‖ := norm_sub_le _ _
        _ ≤ |t| + |t| := by rw [norm_ofReal_mul_I]; linarith
        _ ≤ 2 * t ^ 2 := by linarith
  calc _ ≤ ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I‖ +
        ‖((t ^ 2 / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * t ^ 2 + t ^ 2 / 2 := by rw [h2]; linarith
    _ ≤ 3 * t ^ 2 := by nlinarith [sq_nonneg t]

/-- For complex numbers `a`, `b` of norm `1` and every integer `M`,
`‖a ^ M - b ^ M‖ ≤ |(M : ℝ)| * ‖a - b‖`. A nonnegative exponent reduces to the bound for natural
powers, and for a negative exponent `(a ^ n)⁻¹ - (b ^ n)⁻¹` has the same norm as `b ^ n - a ^ n`
because `a ^ n` and `b ^ n` have norm `1`. -/
theorem norm_zpow_sub_zpow_le (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (M : ℤ) :
    ‖a ^ M - b ^ M‖ ≤ |(M : ℝ)| * ‖a - b‖ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg M
  · rw [zpow_natCast, zpow_natCast, Int.cast_natCast, Nat.abs_cast]
    exact norm_pow_sub_pow_le a b ha.le hb.le n
  · have ha0 : a ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [ha]; exact one_ne_zero))
    have hb0 : b ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [hb]; exact one_ne_zero))
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_sub_inv' ha0 hb0, norm_mul, norm_mul,
      norm_inv, norm_inv, norm_pow, norm_pow, ha, hb, one_pow, inv_one, one_mul, mul_one,
      Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, norm_sub_rev a b]
    exact norm_pow_sub_pow_le b a hb.le ha.le n

/-- For real `t`, `‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I + ((t ^ 2 / 2 : ℝ) :
ℂ)‖ ≤ 3 * |t| ^ 3`. For `|t| ≤
1` the proof uses the Taylor remainder bound of order three for the exponential, and for `|t| > 1`
the bound by `3 * t ^ 2`. -/
theorem norm_exp_mul_I_taylor_le_cube (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I + ((t ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      3 * |t| ^ 3 := by
  rcases le_or_gt |t| 1 with ht | ht
  · have h := Complex.exp_bound (x := (t : ℂ) * Complex.I) (by rw [norm_ofReal_mul_I]; exact ht)
      (n := 3) (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, ((t : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
        1 + (t : ℂ) * Complex.I - ((t ^ 2 / 2 : ℝ) : ℂ) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
        Nat.factorial_one, Nat.factorial_two]
      push_cast
      linear_combination ((t : ℂ) ^ 2 / 2) * Complex.I_sq
    rw [hs, norm_ofReal_mul_I] at h
    have he : Complex.exp ((t : ℂ) * Complex.I) - (1 + (t : ℂ) * Complex.I - ((t ^ 2 / 2 : ℝ) : ℂ))
        =
        Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I + ((t ^ 2 / 2 : ℝ) : ℂ) := by
      ring
    rw [he] at h
    refine h.trans ?_
    rw [mul_comm 3]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    norm_num [Nat.factorial]
  · have := norm_exp_mul_I_taylor_le_sq t
    have h3 : t ^ 2 ≤ |t| ^ 3 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t, sq_nonneg |t|]
    linarith

/-- For every Boolean `odd`, the complex number `if odd then -1 else 1` is fixed by complex
conjugation. -/
theorem conj_ite_neg_one_one (odd : Bool) : starRingEnd ℂ (if odd then -1 else 1 : ℂ) =
    (if odd then -1 else 1 : ℂ) := by
  cases odd <;> simp

/-- For complex `u`, `v` of norm one and every natural number `n`, `‖u ^ n - v ^ n‖ ≤ n * ‖u - v‖`.
A case of `norm_pow_sub_pow_le`, which asks for norms at most one. -/
theorem norm_pow_sub_pow_le_natCast_mul (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (n : ℕ) :
    ‖u ^ n - v ^ n‖ ≤ n * ‖u - v‖ :=
  norm_pow_sub_pow_le u v hu.le hv.le n

/-- For real `r`, `m` and complex `x`, `r * x * m = r * (x / r) * (r * m)` in `ℂ`. This holds also
for `r = 0`, where both sides are zero. -/
theorem ofReal_mul_mul_eq_mul_div_mul (r : ℝ) (x : ℂ) (m : ℝ) :
    (r : ℂ) * x * (m : ℂ) = (r : ℂ) * (x / r) * ((r * m : ℝ) : ℂ) := by
  by_cases hr : r = 0
  · simp [hr]
  · have : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    push_cast
    field_simp

/-- For complex `u`, `v` of norm one and every integer `k`, `‖u ^ k - v ^ k‖ ≤ k.natAbs * ‖u - v‖`,
where `k.natAbs` is the absolute value of `k`. For negative `k` the difference of the inverses
is reduced to the case of a natural power. -/
theorem norm_zpow_sub_zpow_le_natAbs_mul (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (k : ℤ) :
    ‖u ^ k - v ^ k‖ ≤ (k.natAbs : ℝ) * ‖u - v‖ := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simp only [zpow_natCast, Int.natAbs_natCast]
    exact norm_pow_sub_pow_le_natCast_mul u v hu hv n
  · have hu0 : u ^ n ≠ 0 := pow_ne_zero _ (by rw [← norm_ne_zero_iff, hu]; norm_num)
    have hv0 : v ^ n ≠ 0 := pow_ne_zero _ (by rw [← norm_ne_zero_iff, hv]; norm_num)
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_sub_inv' hu0 hv0, Int.natAbs_neg,
        Int.natAbs_natCast]
    rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_pow, norm_pow, hu, hv, one_pow, inv_one,
        one_mul, mul_one,
      norm_sub_rev]
    exact norm_pow_sub_pow_le_natCast_mul u v hu hv n

end PDE.Analysis
