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
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import PDE.Analysis.Scalar.Powers.Basic
public import PDE.Analysis.Scalar.Sums

set_option linter.style.header false

/-!
# Powers, roots, exponentials and logarithms of real numbers

The lemmas rewrite and compare expressions with `Real.rpow`, `Real.sqrt`, `Real.exp` and `Real.log`:
laws of exponents for particular exponents, monotonicity in the base or in the exponent, bounds of
an exponential or of a power by a simpler function. The proofs combine the lemmas of Mathlib on
these functions with `positivity`, `norm_num` and `nlinarith`.

## Main results

* `PDE.Analysis.div_one_add_pow_mul_le`: For real numbers `0 ≤ D`, `0 ≤ a`, `0 ≤ r` and a natural
  number `k ≥ 1`, `D / (1 + r) ^ k * a ≤ D * (a / (1 + r))`.
* `PDE.Analysis.add_rpow_neg_le_rpow_neg`: If `0 < σ ≤ ρ`, `0 ≤ μ` and `0 ≤ e`, then
  `(μ + ρ) ^ (-e) ≤ σ ^ (-e)`.
* `PDE.Analysis.rpow_neg_le_sixteenth_rpow_neg_five`: If `1 / 16 ≤ ρ` and `0 ≤ e ≤ 5`, then
  `ρ ^ (-e) ≤ (1 / 16 : ℝ) ^ (-(5 : ℝ))`.
* `PDE.Analysis.abs_exp_neg_mul_sub_add_le`: For real `τ > 0`, `r` with `|r - τ| ≤ τ / 2` and
  `x ≥ 0`, `|Real.exp (-(r * x)) - Real.exp (-(τ * x)) + (r - τ) * (x * Real.exp (-(τ * x)))| ≤ 16 /
  τ ^ 2 * (r - τ) ^ 2`. This bounds the error of the first order expansion of
  `r ↦ Real.exp (-(r * x))` at `τ`, uniformly in `x`.
* `PDE.Analysis.div_one_add_le_and_sq_le`: Let `D ≥ 0`, `η > 0`, `t ≥ 0` and
  `R = (2 * D / η) ^ 2 + 2 * D / η`. If `R < t`, then `2 * D / (1 + t) ≤ η` and
  `2 * D / (1 + t) ^ 2 ≤ η * (1 + t) ^ (-(3 / 2 : ℝ))`. With `a = 2 * D / η`, the proof uses
  `a ≤ 1 + t` for the first bound and `a ≤ √(1 + t)` for the second.
* `PDE.Analysis.div_one_add_pow_eq_mul_rpow`: For `0 ≤ x` and a natural number `k`,
  `C / (1 + x) ^ k = C * (1 + x) ^ (-(k : ℝ))`, where the power on the right is the real power.
* `PDE.Analysis.div_one_add_pow_le_self`: For real numbers `0 ≤ D`, `0 ≤ r` and a natural number
  `k`, `D / (1 + r) ^ k ≤ D`.
* `PDE.Analysis.div_rpow_le_div_rpow_of_le`: For `0 ≤ a`, `1 ≤ t` and real exponents `q ≤ r`,
  `a / t ^ r ≤ a / t ^ q`.

There are 146 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Real Set Filter Topology
open scoped Nat

namespace PDE.Analysis

/-- If `0 < c ≤ 1`, `0 ≤ m`, `c ≤ ρ` and `0 ≤ e ≤ E`, then `(m + ρ) ^ (-e) ≤ c ^ (-E)`. -/
theorem add_rpow_neg_le_of_le_one {m ρ e E c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hm : 0 ≤ m)
    (hρ : c ≤ ρ)
    (he : 0 ≤ e) (heE : e ≤ E) : (m + ρ) ^ (-e) ≤ c ^ (-E) :=
  (rpow_le_rpow_of_nonpos hc (by linarith) (by linarith)).trans
    (rpow_le_rpow_of_exponent_ge hc hc1 (by linarith))

/-- If `0 < σ ≤ ρ`, `0 ≤ μ` and `0 ≤ e`, then `(μ + ρ) ^ (-e) ≤ σ ^ (-e)`. -/
theorem add_rpow_neg_le_rpow_neg {σ μ ρ e : ℝ} (hσ : 0 < σ) (hμ : 0 ≤ μ) (hρ : σ ≤ ρ) (he : 0 ≤ e) :
    (μ + ρ) ^ (-e) ≤ σ ^ (-e) :=
  Real.rpow_le_rpow_of_nonpos hσ (by linarith) (by linarith)

/-- For `0 < R` and any real `τ`, `R ^ 3 / (R + √τ) ^ 4 ≤ R⁻¹`. -/
theorem div_add_sqrt_pow_four_le_inv {R τ : ℝ} (hR : 0 < R) :
    R ^ 3 / (R + Real.sqrt τ) ^ 4 ≤ R⁻¹ := by
  have hs : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have h4 : R ^ 4 ≤ (R + Real.sqrt τ) ^ 4 := pow_le_pow_left₀ hR.le (by linarith) 4
  rw [div_le_iff₀ (pow_pos (by linarith) 4)]
  calc R ^ 3 = R⁻¹ * R ^ 4 := by field_simp
    _ ≤ R⁻¹ * (R + Real.sqrt τ) ^ 4 := mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hR.le)

/-- For `0 < R` and any real `τ`, `0 ≤ R ^ 3 / (R + √τ) ^ 4`. -/
theorem div_add_sqrt_pow_four_nonneg {R τ : ℝ} (hR : 0 < R) :
    0 ≤ R ^ 3 / (R + Real.sqrt τ) ^ 4 :=
  div_nonneg (pow_nonneg hR.le 3) (pow_nonneg (add_nonneg hR.le (Real.sqrt_nonneg _)) 4)

/-- For `0 < R` and `0 < τ`, `R ^ 3 / (R + √τ) ^ 4 ≤ R ^ 3 / τ ^ 2`, because
`τ ^ 2 = (√τ) ^ 4 ≤ (R + √τ) ^ 4`. -/
theorem div_add_sqrt_pow_le_div_sq {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) :
    R ^ 3 / (R + Real.sqrt τ) ^ 4 ≤ R ^ 3 / τ ^ 2 := by
  have hs : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have hsq : τ ^ 2 = Real.sqrt τ ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hτ.le]
  apply div_le_div_of_nonneg_left (pow_nonneg hR.le 3) (pow_pos hτ 2)
  rw [hsq]
  exact pow_le_pow_left₀ hs (by linarith) 4

/-- Let `D ≥ 0`, `η > 0`, `t ≥ 0` and `R = (2 * D / η) ^ 2 + 2 * D / η`. If `R < t`, then
`2 * D / (1 + t) ≤ η` and `2 * D / (1 + t) ^ 2 ≤ η * (1 + t) ^ (-(3 / 2 : ℝ))`. With
`a = 2 * D / η`, the proof uses `a ≤ 1 + t` for the first bound and `a ≤ √(1 + t)` for the second.
-/
theorem div_one_add_le_and_sq_le {D η t R : ℝ} (hD : 0 ≤ D) (hη : 0 < η) (ht : 0 ≤ t)
    (hR : R = (2 * D / η) ^ 2 + 2 * D / η) (htR : R < t) :
    2 * D / (1 + t) ≤ η ∧ 2 * D / (1 + t) ^ 2 ≤ η * (1 + t) ^ (-(3 / 2 : ℝ)) := by
  set a := 2 * D / η with ha
  have ha0 : 0 ≤ a := by positivity
  have hea : η * a = 2 * D := by rw [ha]; field_simp
  have hpos : 0 < 1 + t := by linarith
  constructor
  · rw [div_le_iff₀ hpos, ← hea]
    refine mul_le_mul_of_nonneg_left ?_ hη.le
    nlinarith
  · have hs : a ≤ Real.sqrt (1 + t) := (Real.le_sqrt ha0 hpos.le).2 (by nlinarith)
    have hw : (1 + t) ^ (-(3 / 2 : ℝ)) * (1 + t) ^ 2 = Real.sqrt (1 + t) := by
      rw [← Real.rpow_two, ← Real.rpow_add hpos, Real.sqrt_eq_rpow]
      norm_num
    rw [div_le_iff₀ (by positivity), mul_assoc, hw, ← hea]
    exact mul_le_mul_of_nonneg_left hs hη.le

/-- For `0 ≤ x` and a natural number `k`, `C / (1 + x) ^ k = C * (1 + x) ^ (-(k : ℝ))`, where the
power on the right is the real power. -/
theorem div_one_add_pow_eq_mul_rpow (C x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    C / (1 + x) ^ k = C * (1 + x) ^ (-(k : ℝ)) := by
  have hp : 0 < 1 + x := by linarith
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, div_eq_mul_inv]

/-- For real numbers `0 ≤ D`, `0 ≤ r` and a natural number `k`, `D / (1 + r) ^ k ≤ D`. -/
theorem div_one_add_pow_le_self {D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (k : ℕ) : D / (1 + r) ^ k ≤ D :=
  div_le_self hD (one_le_pow₀ (by linarith))

/-- For real numbers `0 ≤ D`, `0 ≤ a`, `0 ≤ r` and a natural number `k ≥ 1`,
`D / (1 + r) ^ k * a ≤ D * (a / (1 + r))`. -/
theorem div_one_add_pow_mul_le {D a r : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a) (hr : 0 ≤ r) {k : ℕ}
    (hk : 1 ≤ k) :
    D / (1 + r) ^ k * a ≤ D * (a / (1 + r)) := by
  have h1 : 1 + r ≤ (1 + r) ^ k := le_self_pow₀ (by linarith) (by omega)
  have h0 : 0 < 1 + r := by linarith
  rw [div_mul_eq_mul_div, mul_div_assoc']
  exact div_le_div_of_nonneg_left (mul_nonneg hD ha) h0 h1

/-- For `0 ≤ x` and a real exponent `γ`, `C / (1 + x) ^ γ = C * (1 + x) ^ (-γ)`. -/
theorem div_one_add_rpow_eq_mul_rpow (C x γ : ℝ) (hx : 0 ≤ x) :
    C / (1 + x) ^ γ = C * (1 + x) ^ (-γ) := by
  have hp : 0 < 1 + x := by linarith
  rw [Real.rpow_neg hp.le, div_eq_mul_inv]

/-- For `0 ≤ R ≤ ρ` and any real `B`,
`(B / (1 + ρ) ^ 2) ^ 2 ≤ B ^ 2 * (1 + R) ^ (-(1 / 2 : ℝ)) * (1 + ρ) ^ (-(7 / 2 : ℝ))`. The left side
equals `B ^ 2 * (1 + ρ) ^ (-(7 / 2 : ℝ)) * (1 + ρ) ^ (-(1 / 2 : ℝ))`, and
`(1 + ρ) ^ (-(1 / 2 : ℝ)) ≤ (1 + R) ^ (-(1 / 2 : ℝ))`. -/
theorem div_one_add_sq_sq_le_rpow {B R ρ : ℝ} (hR : 0 ≤ R) (hρ : R ≤ ρ) :
    (B / (1 + ρ) ^ 2) ^ 2 ≤ B ^ 2 * (1 + R) ^ (-(1 / 2 : ℝ)) * (1 + ρ) ^ (-(7 / 2 : ℝ)) := by
  have hp : 0 < 1 + ρ := by linarith
  have hq : 0 < 1 + R := by linarith
  have e : (1 + ρ) ^ (-(7 / 2 : ℝ)) * (1 + ρ) ^ (-(1 / 2 : ℝ)) = ((1 + ρ) ^ 4)⁻¹ := by
    rw [← Real.rpow_add hp, show (-(7 / 2 : ℝ) + -(1 / 2 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hp.le, Real.rpow_natCast]
  have hm : (1 + ρ) ^ (-(1 / 2 : ℝ)) ≤ (1 + R) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hq (by linarith) (by norm_num)
  have h7 : 0 ≤ (1 + ρ) ^ (-(7 / 2 : ℝ)) := Real.rpow_nonneg hp.le _
  have hB : 0 ≤ B ^ 2 := sq_nonneg B
  calc (B / (1 + ρ) ^ 2) ^ 2 = B ^ 2 * ((1 + ρ) ^ (-(7 / 2 : ℝ)) * (1 + ρ) ^ (-(1 / 2 : ℝ))) := by
        rw [e, div_pow, ← pow_mul, div_eq_mul_inv]
    _ ≤ B ^ 2 * ((1 + ρ) ^ (-(7 / 2 : ℝ)) * (1 + R) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm h7) hB
    _ = B ^ 2 * (1 + R) ^ (-(1 / 2 : ℝ)) * (1 + ρ) ^ (-(7 / 2 : ℝ)) := by ring

/-- For `0 ≤ a`, `1 ≤ t` and real exponents `q ≤ r`, `a / t ^ r ≤ a / t ^ q`. -/
theorem div_rpow_le_div_rpow_of_le {a t q r : ℝ} (ha : 0 ≤ a) (ht : 1 ≤ t) (hqr : q ≤ r) :
    a / t ^ r ≤ a / t ^ q :=
  div_le_div_of_nonneg_left ha (Real.rpow_pos_of_pos (by
    linarith) q) (Real.rpow_le_rpow_of_exponent_le ht hqr)

/-- For `0 < t`, reals `a`, `b` and real exponents `q`, `r`:
`a / t ^ q * (b / t ^ r) = a * b / t ^ (q + r)`. -/
theorem div_rpow_mul_div_rpow {a b t q r : ℝ} (ht : 0 < t) :
    a / t ^ q * (b / t ^ r) = a * b / t ^ (q + r) := by
  rw [Real.rpow_add ht]
  have h1 : 0 < t ^ q := Real.rpow_pos_of_pos ht q
  have h2 : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  field_simp

/-- For `0 < w₀` and reals `a`, `z`, `(a / √w₀ * z) ^ 2 * w₀ = a ^ 2 * z ^ 2`. -/
theorem div_sqrt_mul_sq_mul_self {a w₀ z : ℝ} (hw : 0 < w₀) :
    (a / Real.sqrt w₀ * z) ^ 2 * w₀ = a ^ 2 * z ^ 2 := by
  have hs : Real.sqrt w₀ ^ 2 = w₀ := Real.sq_sqrt hw.le
  have hsp : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw
  rw [mul_pow, div_pow, hs]
  field_simp

/-- For every real `r > 0` there is an integer `k` with `1 ≤ 2 ^ (k : ℝ) * r` and
`2 ^ (k : ℝ) * r ≤ 2`, where the power is a real power. The proof takes the integer `n` with
`2 ^ n ≤ r < 2 ^ (n + 1)` and sets `k = -n`. -/
theorem exists_int_two_rpow_mul_mem_Icc (r : ℝ) (hr : 0 < r) :
    ∃ k : ℤ, 1 ≤ (2 : ℝ) ^ (k : ℝ) * r ∧ (2 : ℝ) ^ (k : ℝ) * r ≤ 2 := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hr one_lt_two
  refine ⟨-n, ?_, ?_⟩
  · rw [Real.rpow_intCast, zpow_neg, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
    exact hn1
  · rw [Real.rpow_intCast, zpow_neg, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [zpow_add_one₀ (by norm_num)] at hn2
    linarith

/-- For `0 < κ` and `0 < P` there is a natural number `n` with `2 * Real.exp (-(n * P)) ^ κ < 1`.
Any `n > 1 / (κ * P)` works, since then `Real.exp (-(n * P)) ^ κ < Real.exp (-1)` and
`2 < Real.exp 1`. -/
theorem exists_nat_two_mul_exp_rpow_lt {κ : ℝ} {P : ℝ} (hκ : 0 < κ) (hP : 0 < P) :
    ∃ n : ℕ, 2 * Real.exp (-(n * P)) ^ κ < 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (κ * P))
  refine ⟨n, ?_⟩
  have hnP : 1 < n * P * κ := by
    rw [div_lt_iff₀ (mul_pos hκ hP)] at hn
    linarith
  rw [← Real.exp_mul]
  have h2 : Real.exp (-(n * P) * κ) < Real.exp (-1) :=
    Real.exp_lt_exp.mpr (by linarith)
  have h3 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
    linarith
  have h4 : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-1)]

/-- For `0 < p` and `0 < y` there is `t₀ > 0` such that `T ^ p ≤ y` for every real `T` with
`0 ≤ T ≤ t₀`. One can take `t₀ = y ^ (1 / p)`. -/
theorem exists_pos_forall_rpow_le (p y : ℝ) (hp : 0 < p) (hy : 0 < y) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ T : ℝ, 0 ≤ T → T ≤ t₀ → T ^ p ≤ y :=
  ⟨y ^ (1 / p), Real.rpow_pos_of_pos hy _, fun T hT hTt ↦ by
    calc T ^ p ≤ (y ^ (1 / p)) ^ p := Real.rpow_le_rpow hT hTt hp.le
      _ = y := by rw [← Real.rpow_mul hy.le, one_div_mul_cancel hp.ne', Real.rpow_one]⟩

/-- For real `α > 1` and `τ ≥ 0`,
`Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3 ≤ 1`. The left side
equals `Real.exp (τ * (1 / (2 * α) - 1))`, and this exponent is nonpositive. -/
theorem exp_rpow_mul_inv_cube_le_one (α : ℝ) (hα : 1 < α) {τ : ℝ} (hτ : 0 ≤ τ) :
    Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3 ≤ 1 := by
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add,
    Real.exp_le_one_iff]
  have h3 : τ * (4 * (1 / (2 * α)) - 1) + ((3 : ℕ) : ℝ) * -(τ * (1 / (2 * α))) =
      τ * (1 / (2 * α) - 1) := by push_cast; ring
  rw [h3]
  have : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; linarith
  exact mul_nonpos_of_nonneg_of_nonpos hτ (by linarith)

/-- For `0 < a`, `0 < R` and a real exponent `m ≤ 3`,
`(R / 2) ^ 3 * min 1 ((a / (R / 2)) ^ m) ≤ R ^ 3 * min 1 ((a / R) ^ m)`. Replacing `R` by `R / 2`
multiplies `(a / R) ^ m` by `2 ^ m ≤ 8`, and `(R / 2) ^ 3 = R ^ 3 / 8` absorbs this factor. -/
theorem half_cube_mul_min_rpow_le {a m R : ℝ} (ha : 0 < a) (hm : m ≤ 3)
    (hR : 0 < R) :
    (R / 2) ^ 3 * min 1 ((a / (R / 2)) ^ m) ≤ R ^ 3 * min 1 ((a / R) ^ m) := by
  have e : (a / (R / 2)) ^ m = 2 ^ m * (a / R) ^ m := by
    rw [div_div_eq_mul_div, show a * 2 / R = 2 * (a / R) by ring]
    exact Real.mul_rpow (by norm_num) (by positivity)
  have h8 : (2 : ℝ) ^ m ≤ 8 := by
    calc (2 : ℝ) ^ m ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hm
      _ = 8 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
  have hx : 0 ≤ (a / R) ^ m := Real.rpow_nonneg (by positivity) _
  have hmin : min 1 ((a / (R / 2)) ^ m) ≤ 8 * min 1 ((a / R) ^ m) := by
    rw [e]
    rcases le_total 1 ((a / R) ^ m) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by norm_num)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right h8 hx)
  calc (R / 2) ^ 3 * min 1 ((a / (R / 2)) ^ m)
      ≤ (R / 2) ^ 3 * (8 * min 1 ((a / R) ^ m)) :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = R ^ 3 * min 1 ((a / R) ^ m) := by ring

/-- For real `τ ≥ 0` and `e`, `(τ / 2) ^ (-e) = 2 ^ e * τ ^ (-e)`. -/
theorem half_rpow_neg {τ e : ℝ} (hτ : 0 ≤ τ) : (τ / 2) ^ (-e) = 2 ^ e * τ ^ (-e) := by
  rw [Real.div_rpow hτ zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul, mul_comm]

/-- The identity `√(9 / 2) / 2 = 3 / (2 * √2)` for real square roots. -/
theorem half_sqrt_nine_halves : Real.sqrt (9 / 2) / 2 = 3 / (2 * Real.sqrt 2) := by
  have h : Real.sqrt (9 / 2) * Real.sqrt 2 = 3 := by
    rw [← Real.sqrt_mul (by
      norm_num), show (9 / 2 : ℝ) * 2 = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : 0 < Real.sqrt 2 := by positivity
  rw [eq_div_iff (by positivity)]
  linear_combination h

/-- For real `r > 0`, `r⁻¹ * (1 + r) ^ (-3) = (r * (1 + r) ^ 3)⁻¹`, where the power on the left is a
real power and the power on the right is a natural power. -/
theorem inv_mul_rpow_neg_three_eq_inv {r : ℝ} (hr : 0 < r) :
    r⁻¹ * (1 + r) ^ (-(3 : ℝ)) = (r * (1 + r) ^ 3)⁻¹ := by
  rw [Real.rpow_neg (by
    positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_inv]

/-- For real numbers with `0 ≤ k ≤ 3` and `0 ≤ s ≤ R`, every real `A` satisfies
`A ≤ |A| * (1 + R) ^ 3 * (1 + s) ^ (-k)`, with real powers. The proof inserts
`1 = (1 + R) ^ k * (1 + R) ^ (-k)` and uses `(1 + R) ^ k ≤ (1 + R) ^ 3` and
`(1 + R) ^ (-k) ≤ (1 + s) ^ (-k)`. -/
theorem le_abs_mul_rpow_mul_rpow_neg {k : ℝ} (hk3 : k ≤ 3) (hk0 : 0 ≤ k) {R s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ R) (A : ℝ) : A ≤ |A| * (1 + R) ^ (3 : ℝ) * (1 + s) ^ (-k) := by
  have h1 : 0 < 1 + s := by linarith
  have h2 : 1 ≤ 1 + R := by linarith
  have hR : 0 < 1 + R := by linarith
  have e1 : (1 + R) ^ (-k) ≤ (1 + s) ^ (-k) :=
    Real.rpow_le_rpow_of_nonpos h1 (by linarith) (by linarith)
  have e2 : (1 + R) ^ k ≤ (1 + R) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2 hk3
  have e3 : (1 + R) ^ k * (1 + R) ^ (-k) = 1 := by
    rw [Real.rpow_neg hR.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hR k).ne']
  have e4 : 0 ≤ (1 + R) ^ (-k) := (Real.rpow_pos_of_pos hR _).le
  calc A ≤ |A| := le_abs_self A
    _ = |A| * ((1 + R) ^ k * (1 + R) ^ (-k)) := by rw [e3, mul_one]
    _ ≤ |A| * ((1 + R) ^ (3 : ℝ) * (1 + s) ^ (-k)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
        exact mul_le_mul e2 e1 e4 (Real.rpow_pos_of_pos hR _).le
    _ = |A| * (1 + R) ^ (3 : ℝ) * (1 + s) ^ (-k) := by ring

/-- Let `x`, `D`, `K`, `g`, `p`, `q0`, `q1`, `q2` be nonnegative reals. If
`x ^ 2 ≤ 6 * D ^ 2 * (p + (q0 + q1 + q2)) + K * g ^ 2`, then
`x ≤ 3 * D * (√p + (√q0 + √q1 + √q2)) + √K * g`. The proof writes `p`, `q0`, `q1`, `q2`, `K` as
squares of their square roots and compares the squares of the two sides. -/
theorem le_add_sqrt_of_sq_le_add {x D K g p q0 q1 q2 : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hg : 0 ≤ g)
    (hp : 0 ≤ p) (hq0 : 0 ≤ q0) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (h : x ^ 2 ≤ 6 * D ^ 2 * (p + (q0 + q1 + q2)) + K * g ^ 2) :
    x ≤ 3 * D * (Real.sqrt p + (Real.sqrt q0 + Real.sqrt q1 + Real.sqrt q2)) + Real.sqrt K * g := by
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 ≤ a ∧ p = a ^ 2 := ⟨Real.sqrt p, Real.sqrt_nonneg _,
      (Real.sq_sqrt hp).symm⟩
  obtain ⟨b0, hb0, rfl⟩ : ∃ a, 0 ≤ a ∧ q0 = a ^ 2 :=
    ⟨Real.sqrt q0, Real.sqrt_nonneg _, (Real.sq_sqrt hq0).symm⟩
  obtain ⟨b1, hb1, rfl⟩ : ∃ a, 0 ≤ a ∧ q1 = a ^ 2 :=
    ⟨Real.sqrt q1, Real.sqrt_nonneg _, (Real.sq_sqrt hq1).symm⟩
  obtain ⟨b2, hb2, rfl⟩ : ∃ a, 0 ≤ a ∧ q2 = a ^ 2 :=
    ⟨Real.sqrt q2, Real.sqrt_nonneg _, (Real.sq_sqrt hq2).symm⟩
  obtain ⟨c, hc, rfl⟩ : ∃ a, 0 ≤ a ∧ K = a ^ 2 := ⟨Real.sqrt K, Real.sqrt_nonneg _,
      (Real.sq_sqrt hK).symm⟩
  rw [Real.sqrt_sq ha, Real.sqrt_sq hb0, Real.sqrt_sq hb1, Real.sqrt_sq hb2, Real.sqrt_sq hc]
  have hs : 0 ≤ a + (b0 + b1 + b2) := by positivity
  refine (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 ?_
  have e1 : a ^ 2 + (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) ≤ (a + (b0 + b1 + b2)) ^ 2 := by
    nlinarith [mul_nonneg ha hb0, mul_nonneg ha hb1, mul_nonneg ha hb2, mul_nonneg hb0 hb1,
      mul_nonneg hb0 hb2, mul_nonneg hb1 hb2]
  have e2 : 0 ≤ 3 * D * (a + (b0 + b1 + b2)) * (c * g) := by positivity
  have e3 : 6 * D ^ 2 * (a ^ 2 + (b0 ^ 2 + b1 ^ 2 + b2 ^ 2)) ≤ 9 * D ^ 2 *
      (a + (b0 + b1 + b2)) ^ 2 := by
    have e4 : 0 ≤ D ^ 2 * (a ^ 2 + (b0 ^ 2 + b1 ^ 2 + b2 ^ 2)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e1 (sq_nonneg D)]
  nlinarith

/-- For a real `x ≥ 0`, if `x ^ ((1 : ℝ) / 3) ≤ c` then `x ≤ c ^ 3`. -/
theorem le_cube_of_rpow_third_le {x c : ℝ} (hx : 0 ≤ x) (h : x ^ ((1 : ℝ) / 3) ≤ c) :
    x ≤ c ^ 3 := by
  have h0 : 0 ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hx _
  have h1 : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  calc x = (x ^ ((1 : ℝ) / 3)) ^ 3 := h1.symm
    _ ≤ c ^ 3 := pow_le_pow_left₀ h0 h 3

/-- For `1 < α` and `0 ≤ y`, `y ≤ Real.exp (y ^ (2 * α))`. For `y ≤ 1` the right side is at least
`1`, and for `y ≥ 1` one has `y ≤ y ^ (2 * α) ≤ Real.exp (y ^ (2 * α))`. -/
theorem le_exp_rpow_two_mul {α y : ℝ} (hα : 1 < α) (hy : 0 ≤ y) :
    y ≤ Real.exp (y ^ (2 * α)) := by
  rcases le_total y 1 with h | h
  · exact h.trans (Real.one_le_exp (Real.rpow_nonneg hy _))
  · have h2 : y ≤ y ^ (2 * α) := by
      calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
        _ ≤ y ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    exact h2.trans (by linarith [Real.add_one_le_exp (y ^ (2 * α))])

/-- For real `r > 0` and `x ≥ 0`, `x ≤ r * x ^ 6 + r ^ (-(1 / 5))`, where `r ^ (-(1 / 5))` is a real
power. The proof splits on whether `x ≤ r ^ (-(1 / 5))`; if not, then `r * x ^ 5 > 1` and so
`x ≤ r * x ^ 6`. -/
theorem le_mul_pow_six_add_rpow_neg {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    x ≤ r * x ^ 6 + r ^ (-(1 / 5 : ℝ)) := by
  have hs : 0 < r ^ (-(1 / 5 : ℝ)) := Real.rpow_pos_of_pos hr _
  have hs5 : r * (r ^ (-(1 / 5 : ℝ))) ^ 5 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hr.ne']
  rcases le_or_gt x (r ^ (-(1 / 5 : ℝ))) with h | h
  · linarith [mul_nonneg hr.le (pow_nonneg hx 6)]
  · have h1 : 1 < r * x ^ 5 := by
      calc (1 : ℝ) = r * (r ^ (-(1 / 5 : ℝ))) ^ 5 := hs5.symm
        _ < r * x ^ 5 := mul_lt_mul_of_pos_left (pow_lt_pow_left₀ h hs.le (by norm_num)) hr
    have h2 := mul_le_mul_of_nonneg_left h1.le hx
    have h3 : x * (r * x ^ 5) = r * x ^ 6 := by ring
    linarith

/-- For `1 ≤ α` and `0 ≤ y`, `y ≤ 1 + y ^ α`. -/
theorem le_one_add_rpow {α y : ℝ} (hα : 1 ≤ α) (hy : 0 ≤ y) : y ≤ 1 + y ^ α := by
  rcases le_total y 1 with h | h
  · have := Real.rpow_nonneg hy α
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hα
    rw [Real.rpow_one] at this
    linarith

/-- For real `x ≥ 0`, `x ≤ 1 + x ^ (6 : ℝ)`. -/
theorem le_one_add_rpow_six (x : ℝ) (hx : 0 ≤ x) : x ≤ 1 + x ^ (6 : ℝ) := by
  rcases le_total x 1 with h | h
  · linarith [Real.rpow_nonneg hx (6 : ℝ)]
  · have := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (1 : ℝ) ≤ 6)
    rw [Real.rpow_one] at this
    linarith

/-- For `1 < α` and `0 ≤ r`, `r ≤ 1 + r ^ (2 * α)`. -/
theorem le_one_add_rpow_two_mul (α : ℝ) (hα : 1 < α) (r : ℝ) (hr : 0 ≤ r) : r ≤ 1 + r ^ (2 * α) :=
    by
  rcases le_or_gt r 1 with h | h
  · have : 0 ≤ r ^ (2 * α) := Real.rpow_nonneg hr _
    linarith
  · have h2 : r ^ (1 : ℝ) ≤ r ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
    rw [Real.rpow_one] at h2
    linarith

/-- Let `0 ≤ B`, `0 ≤ e`, `0 ≤ t` and `x ≤ B`, and suppose that `x = 0` whenever `R < t`. Then
`x ≤ B * (1 + |R|) ^ e / (1 + t) ^ e`, with the real exponent `e`. The proof notes that for `t ≤ R`
one has `(1 + t) ^ e ≤ (1 + |R|) ^ e`. -/
theorem le_rpow_div_rpow_of_eq_zero {B R e t x : ℝ} (hB : 0 ≤ B) (he : 0 ≤ e) (ht : 0 ≤ t)
    (hx : x ≤ B)
    (hz : R < t → x = 0) : x ≤ B * (1 + |R|) ^ e / (1 + t) ^ e := by
  have hpos : 0 < (1 + t) ^ e := Real.rpow_pos_of_pos (by linarith) e
  by_cases h : R < t
  · rw [hz h]
    positivity
  · rw [le_div_iff₀ hpos]
    have h1 : (1 + t) ^ e ≤ (1 + |R|) ^ e :=
      Real.rpow_le_rpow (by linarith) (by linarith [le_abs_self R, not_lt.mp h]) he
    calc x * (1 + t) ^ e ≤ B * (1 + t) ^ e := mul_le_mul_of_nonneg_right hx hpos.le
      _ ≤ B * (1 + |R|) ^ e := mul_le_mul_of_nonneg_left h1 hB

/-- For real `r > 0` and `t`, `t ≤ r ^ (-(1 / 5)) + r * t ^ 6`, where `r ^ (-(1 / 5))` is a real
power. The proof splits on whether `t ≤ r ^ (-(1 / 5))`; if not, then `r * t ^ 5 > 1` and so
`t < r * t ^ 6`. -/
theorem le_rpow_neg_add_mul_pow_six (r t : ℝ) (hr : 0 < r) :
    t ≤ r ^ (-(1 / 5 : ℝ)) + r * t ^ 6 := by
  set s := r ^ (-(1 / 5 : ℝ)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hr _
  have h5 : s ^ 5 = r⁻¹ := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hr.le,
      show (-(1 / 5 : ℝ)) * ((5 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have h6 : 0 ≤ r * t ^ 6 := by positivity
  by_cases h : t ≤ s
  · linarith
  · push Not at h
    have h5' : s ^ 5 < t ^ 5 := pow_lt_pow_left₀ h hs0.le (by norm_num)
    have h1 : 1 < r * t ^ 5 := by
      rw [h5] at h5'
      have := mul_lt_mul_of_pos_left h5' hr
      rwa [mul_inv_cancel₀ hr.ne'] at this
    have ht0 : 0 < t := hs0.trans h
    have h2 : t * 1 < t * (r * t ^ 5) := mul_lt_mul_of_pos_left h1 ht0
    have e : t * (r * t ^ 5) = r * t ^ 6 := by ring
    linarith

/-- For nonnegative reals `a`, `b`, `K`, if `a ^ 2 ≤ K * b ^ 2` then `a ≤ √K * b`. -/
theorem le_sqrt_mul_of_sq_le {a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (h : a ^ 2 ≤ K * b ^ 2) : a ≤ Real.sqrt K * b := by
  have h2 : Real.sqrt (a ^ 2) ≤ Real.sqrt (K * b ^ 2) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_mul hK, Real.sqrt_sq hb] at h2

/-- For real numbers `x ≥ 0` and `z`, `x ≤ √(x ^ 2 + z ^ 2)`. -/
theorem le_sqrt_sq_add_sq_of_nonneg (x z : ℝ) (hx : 0 ≤ x) : x ≤ Real.sqrt (x ^ 2 + z ^ 2) := by
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt (x ^ 2 + z ^ 2) := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

/-- For real `s₀` and `σ`, `Real.log (Real.exp (-(σ - s₀) / 2) ^ 2) = -(σ - s₀)`. -/
theorem log_exp_neg_sub_div_two_sq (s₀ σ : ℝ) :
    Real.log (Real.exp (-(σ - s₀) / 2) ^ 2) = -(σ - s₀) := by
  rw [Real.log_pow, Real.log_exp]
  push_cast
  ring

/-- For every real `y`, `y * Real.exp (-y) ≤ 1`. -/
theorem mul_exp_neg_le_one (y : ℝ) : y * Real.exp (-y) ≤ 1 := by
  have h := Real.add_one_le_exp y
  calc y * Real.exp (-y) ≤ Real.exp y * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- For real `a > 0` and `r`, `r * Real.exp (-(a * r ^ 2)) ≤ 1 + a⁻¹`. The proof combines
`1 + a * r ^ 2 ≤ Real.exp (a * r ^ 2)` with `r ≤ (1 + a⁻¹) * (1 + a * r ^ 2)`. -/
theorem mul_exp_neg_mul_sq_le (a r : ℝ) (ha : 0 < a) :
    r * Real.exp (-(a * r ^ 2)) ≤ 1 + a⁻¹ := by
  have he : 1 + a * r ^ 2 ≤ Real.exp (a * r ^ 2) := by
    linarith [Real.add_one_le_exp (a * r ^ 2)]
  have h1 : r ≤ (1 + a⁻¹) * (1 + a * r ^ 2) := by
    have e : (1 + a⁻¹) * (1 + a * r ^ 2) = 1 + a * r ^ 2 + a⁻¹ + r ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith [sq_nonneg (r - 1), inv_pos.2 ha, mul_pos ha ha, sq_nonneg r]
  have hkey : r ≤ (1 + a⁻¹) * Real.exp (a * r ^ 2) :=
    h1.trans (by gcongr)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact hkey

/-- Let `0 ≤ x` and `0 ≤ t`. If `x * t ≤ C` and `x ^ 3 * t ≤ C`, then
`x * t ≤ 4 * C * (1 + x) ^ (-(2 : ℝ))`. The proof uses `(1 + x) ^ 2 ≤ 4` when `x ≤ 1` and
`(1 + x) ^ 2 ≤ 4 * x ^ 2` when `1 ≤ x`. -/
theorem mul_le_four_mul_rpow_neg_two {x t C : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (h1 : x * t ≤ C)
    (h3 : x ^ 3 * t ≤ C) :
    x * t ≤ 4 * C * (1 + x) ^ (-(2 : ℝ)) := by
  have hp : 0 < 1 + x := by linarith
  rw [Real.rpow_neg hp.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by
    norm_num, Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  rcases le_total x 1 with hx1 | hx1
  · have hC : 0 ≤ C := (mul_nonneg hx ht).trans h1
    have : (1 + x) ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_nonneg hx ht]
  · have hxt : 0 ≤ x * t := mul_nonneg hx ht
    have e : (1 + x) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
    have : x * t * (1 + x) ^ 2 ≤ x * t * (4 * x ^ 2) := mul_le_mul_of_nonneg_left e hxt
    nlinarith

/-- For `1 < α`, `0 < x` and `0 < h`,
`x * min h (1 / (2 * π * x) ^ (2 * α)) ≤ (1 + (2 * π) ^ (-(2 * α))) * h ^ (1 - 1 / (2 *
α))`. The proof splits on whether `x * h ^ (1 / (2 * α)) ≤
1`, bounding the minimum by `h` in that case and by `1 / (2 * π * x) ^ (2 * α)` otherwise. -/
theorem mul_min_div_rpow_le_mul_rpow {α x h : ℝ} (hα : 1 < α) (hx : 0 < x) (hh : 0 < h) :
    x * min h (1 / (2 * π * x) ^ (2 * α)) ≤
      (1 + (2 * π) ^ (-(2 * α))) * h ^ (1 - 1 / (2 * α)) := by
  set γ := 1 / (2 * α) with hγ
  have hα2 : 0 < 2 * α := by linarith
  have hhγ : 0 < h ^ γ := Real.rpow_pos_of_pos hh γ
  have hhβ : 0 ≤ h ^ (1 - γ) := Real.rpow_nonneg hh.le _
  have hsplit : h ^ γ * h ^ (1 - γ) = h := by
    rw [← Real.rpow_add hh]
    simp
  have hc0 : 0 ≤ (2 * π) ^ (-(2 * α)) := Real.rpow_nonneg (by positivity) _
  rcases le_or_gt (x * h ^ γ) 1 with hc | hc
  · calc x * min h (1 / (2 * π * x) ^ (2 * α)) ≤ x * h := by
          gcongr
          exact min_le_left _ _
      _ = (x * h ^ γ) * h ^ (1 - γ) := by rw [mul_assoc, hsplit]
      _ ≤ 1 * h ^ (1 - γ) := by gcongr
      _ ≤ (1 + (2 * π) ^ (-(2 * α))) * h ^ (1 - γ) := by nlinarith
  · have hk : (2 * π * x) ^ (2 * α) = (2 * π) ^ (2 * α) * x ^ (2 * α) :=
      Real.mul_rpow (by positivity) hx.le
    have hxk : x * (1 / (2 * π * x) ^ (2 * α)) = (2 * π) ^ (-(2 * α)) * x ^ (1 - 2 * α) := by
      rw [hk, Real.rpow_neg (by positivity), Real.rpow_sub hx, Real.rpow_one]
      ring
    have hpow : 1 ≤ (x * h ^ γ) ^ (2 * α - 1) := Real.one_le_rpow hc.le (by linarith)
    have hexp : (x * h ^ γ) ^ (2 * α - 1) = x ^ (2 * α - 1) * h ^ (1 - γ) := by
      rw [Real.mul_rpow hx.le hhγ.le, ← Real.rpow_mul hh.le]
      congr 2
      rw [hγ]
      field_simp
    have hxpos : 0 < x ^ (2 * α - 1) := Real.rpow_pos_of_pos hx _
    have hinv : x ^ (1 - 2 * α) = (x ^ (2 * α - 1))⁻¹ := by
      rw [← Real.rpow_neg hx.le]
      congr 1
      ring
    have hxb : x ^ (1 - 2 * α) ≤ h ^ (1 - γ) := by
      rw [hinv]
      calc (x ^ (2 * α - 1))⁻¹ ≤ (x ^ (2 * α - 1))⁻¹ * (x ^ (2 * α - 1) * h ^ (1 - γ)) := by
            rw [← hexp]
            exact le_mul_of_one_le_right (inv_nonneg.2 hxpos.le) hpow
        _ = h ^ (1 - γ) := by field_simp
    calc x * min h (1 / (2 * π * x) ^ (2 * α)) ≤ x * (1 / (2 * π * x) ^ (2 * α)) := by
          gcongr
          exact min_le_right _ _
      _ = (2 * π) ^ (-(2 * α)) * x ^ (1 - 2 * α) := hxk
      _ ≤ (2 * π) ^ (-(2 * α)) * h ^ (1 - γ) := by gcongr
      _ ≤ (1 + (2 * π) ^ (-(2 * α))) * h ^ (1 - γ) := by nlinarith

/-- For `0 ≤ x`, `0 ≤ C` and a real exponent `e`,
`x * (C * (1 + x) ^ (-e)) ≤ C * (1 + x) ^ (-(e - 1))`. -/
theorem mul_mul_rpow_neg_le_mul_rpow {x C e : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) :
    x * (C * (1 + x) ^ (-e)) ≤ C * (1 + x) ^ (-(e - 1)) := by
  have hp : 0 < 1 + x := by linarith
  have e1 : (1 + x) ^ (-(e - 1)) = (1 + x) * (1 + x) ^ (-e) := by
    rw [show -(e - 1) = 1 + -e by ring, Real.rpow_add hp, Real.rpow_one]
  rw [e1]
  have : 0 ≤ C * (1 + x) ^ (-e) := mul_nonneg hC (by positivity)
  nlinarith

/-- For real `u` and a natural number `z`, `u * (z * u ^ (z - 1)) = z * u ^ z`, with truncated
subtraction in the exponent; for `z = 0` both sides are `0`. -/
theorem mul_natCast_mul_pow_pred (u : ℝ) (z : ℕ) : u * ((z : ℝ) * u ^ (z - 1)) = z * u ^ z := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp
  · rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel hz]

/-- For real numbers with `0 ≤ k ≤ 3` and `s ≥ 1`, every real `A` satisfies
`A * s ^ (-k) ≤ |A| * 2 ^ 3 * (1 + s) ^ (-k)`, with real powers. The proof uses `(1 + s) / 2 ≤ s`,
which gives `s ^ (-k) ≤ 2 ^ k * (1 + s) ^ (-k)`, and `2 ^ k ≤ 2 ^ 3`. -/
theorem mul_rpow_neg_le_abs_mul_rpow {k : ℝ} (hk3 : k ≤ 3) (hk0 : 0 ≤ k) {s : ℝ} (hs : 1 ≤ s)
    (A : ℝ) :
    A * s ^ (-k) ≤ |A| * (2 : ℝ) ^ (3 : ℝ) * (1 + s) ^ (-k) := by
  have h0 : 0 < s := by linarith
  have h1 : 0 < (1 + s) / 2 := by linarith
  have e1 : s ^ (-k) ≤ ((1 + s) / 2) ^ (-k) :=
    Real.rpow_le_rpow_of_nonpos h1 (by linarith) (by linarith)
  have e2 : ((1 + s) / 2) ^ (-k) = (2 : ℝ) ^ k * (1 + s) ^ (-k) := by
    rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  have e3 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hk3
  have e5 : 0 ≤ (1 + s) ^ (-k) := (Real.rpow_pos_of_pos (by linarith) _).le
  have e6 : 0 ≤ s ^ (-k) := (Real.rpow_pos_of_pos h0 _).le
  calc A * s ^ (-k) ≤ |A| * s ^ (-k) := mul_le_mul_of_nonneg_right (le_abs_self A) e6
    _ ≤ |A| * ((2 : ℝ) ^ k * (1 + s) ^ (-k)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
        rw [← e2]
        exact e1
    _ ≤ |A| * ((2 : ℝ) ^ (3 : ℝ) * (1 + s) ^ (-k)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
        exact mul_le_mul_of_nonneg_right e3 e5
    _ = |A| * (2 : ℝ) ^ (3 : ℝ) * (1 + s) ^ (-k) := by ring

/-- For `0 ≤ x`, `0 ≤ C` and real exponents `e' ≤ e`, `C * (1 + x) ^ (-e) ≤ C * (1 + x) ^ (-e')`. -/
theorem mul_rpow_neg_le_mul_rpow_neg {x C e e' : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (h : e' ≤ e) :
    C * (1 + x) ^ (-e) ≤ C * (1 + x) ^ (-e') :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC

/-- For real numbers with `0 ≤ C` and `0 ≤ δ`, `C * δ * (K * F) ^ 2 = (√(C * δ) * K * F) ^ 2`. -/
theorem mul_sq_eq_sqrt_mul_sq {C δ K F : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) :
    C * δ * (K * F) ^ 2 = (Real.sqrt (C * δ) * K * F) ^ 2 := by
  rw [show (Real.sqrt (C * δ) * K * F) ^ 2 = Real.sqrt (C * δ) ^ 2 * K ^ 2 * F ^ 2 by ring,
    Real.sq_sqrt (mul_nonneg hC hδ)]
  ring

/-- Weighted Cauchy-Schwarz inequality for two terms: for real numbers with `0 < c`, `0 < cμ` and
`0 ≤ E`, `α * √E + β * S ≤ √(α ^ 2 / c + β ^ 2 / cμ) * √(c * E + cμ * S ^ 2)`. -/
theorem mul_sqrt_add_le_sqrt_mul_sqrt {α β c cμ E S : ℝ} (hc : 0 < c) (hcμ : 0 < cμ) (hE : 0 ≤ E) :
    α * Real.sqrt E + β * S ≤ Real.sqrt (α ^ 2 / c + β ^ 2 / cμ) *
        Real.sqrt (c * E + cμ * S ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have he := Real.sq_sqrt hE
  have he0 := Real.sqrt_nonneg E
  set e := Real.sqrt E
  rw [div_add_div _ _ hc.ne' hcμ.ne', div_mul_eq_mul_div, le_div_iff₀ (by positivity), ← he]
  nlinarith [sq_nonneg (α * cμ * S - β * c * e)]

/-- For positive reals `a` and `b`, `a * √(b / a) = √(a * b)`. -/
theorem mul_sqrt_div_eq_sqrt_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * Real.sqrt (b / a) = Real.sqrt (a * b) := by
  have e : a * b = a ^ 2 * (b / a) := by
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

/-- For `0 ≤ x` and a real exponent `γ`, `(1 + x) ^ γ ≤ (1 + x) ^ (γ + 1)`. -/
theorem one_add_rpow_le_rpow_add_one {x γ : ℝ} (hx : 0 ≤ x) : (1 + x) ^ γ ≤ (1 + x) ^ (γ + 1) :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- For `R ≥ 0`, the square of the real power `(1 + R) ^ (-(1 / 2) : ℝ)` equals `1 / (1 + R)`. -/
theorem one_add_rpow_neg_half_sq {R : ℝ} (hR : 0 ≤ R) :
    ((1 + R) ^ (-(1 / 2) : ℝ)) ^ 2 = 1 / (1 + R) := by
  have hpos : 0 < 1 + R := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  norm_num
  rw [Real.rpow_neg_one]

/-- For `1 ≤ τ` and `1 ≤ β`, `(1 + τ) ^ (-β) ≤ τ⁻¹`. -/
theorem one_add_rpow_neg_le_inv {τ β : ℝ} (hτ : 1 ≤ τ) (hβ : 1 ≤ β) : (1 + τ) ^ (-β) ≤ τ⁻¹ := by
  have h0 : 0 < τ := by linarith
  rw [Real.rpow_neg (by linarith)]
  apply inv_anti₀ h0
  calc τ = τ ^ (1 : ℝ) := (Real.rpow_one τ).symm
    _ ≤ τ ^ β := Real.rpow_le_rpow_of_exponent_le hτ hβ
    _ ≤ (1 + τ) ^ β := Real.rpow_le_rpow h0.le (by linarith) (by linarith)

/-- For `0 ≤ τ` and `0 ≤ β`, `(1 + τ) ^ (-β) ≤ 1`. -/
theorem one_add_rpow_neg_le_one {τ β : ℝ} (hτ : 0 ≤ τ) (hβ : 0 ≤ β) : (1 + τ) ^ (-β) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

/-- For `0 < μ` and any real `α`,
`((1 / 8) * μ ^ (-(1 / (2 * α)))) ^ (3 - 2 * (2 * α - 1)) = (1 / 8 : ℝ) ^ (5 - 4 * α) * μ ^ (-((5 -
4 * α) / (2 * α)))`. -/
theorem one_div_eight_mul_rpow_rpow_eq {α μ : ℝ} (hμ : 0 < μ) :
    ((1 / 8) * μ ^ (-(1 / (2 * α)))) ^ (3 - 2 * (2 * α - 1)) =
      (1 / 8 : ℝ) ^ (5 - 4 * α) * μ ^ (-((5 - 4 * α) / (2 * α))) := by
  rw [show (3 - 2 * (2 * α - 1)) = 5 - 4 * α by ring,
    Real.mul_rpow (by norm_num) (Real.rpow_nonneg hμ.le _), ← Real.rpow_mul hμ.le]
  congr 2
  ring

/-- For real numbers with `a ≥ 0` and `0 ≤ r ≤ R`, `1 ≤ (1 + R) ^ a * (1 + r) ^ (-a)`. -/
theorem one_le_rpow_mul_rpow_neg {a r R : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hR : r ≤ R) :
    1 ≤ (1 + R) ^ a * (1 + r) ^ (-a) := by
  have h1 : 0 < 1 + r := by linarith
  rw [Real.rpow_neg h1.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos h1 a)]
  exact Real.rpow_le_rpow h1.le (by linarith) ha

/-- The square root of two is at least one: `1 ≤ √2`. -/
theorem one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
  rwa [Real.sqrt_one] at this

/-- For every real `y`, `1 - Real.exp (-y) ≤ y`. -/
theorem one_sub_exp_neg_le (y : ℝ) : 1 - Real.exp (-y) ≤ y := by
  linarith [Real.add_one_le_exp (-y)]

/-- For reals `a < b`, `0 < 1 - Real.exp (-(b - a))`. -/
theorem one_sub_exp_neg_sub_pos {a b : ℝ} (h : a < b) : 0 < 1 - Real.exp (-(b - a)) := by
  have h1 := Real.exp_lt_exp.2 (show -(b - a) < 0 by linarith)
  rw [Real.exp_zero] at h1
  linarith

/-- Let `a < b < 1`, `0 < r` and `Real.log (r ^ 2) = -(s - s₀)`. If
`s ∈ Ioo (s₀ - Real.log (1 - a)) (s₀ - Real.log (1 - b))`, then `1 - r ^ 2 ∈ Ioo a b`. Comparing
logarithms, the two bounds on `s` give `1 - b < r ^ 2 < 1 - a`. -/
theorem one_sub_sq_mem_Ioo_of_log {s₀ a b s r : ℝ} (hab : a < b) (hb : b < 1) (hr : 0 < r)
    (hlog : Real.log (r ^ 2) = -(s - s₀))
    (hs : s ∈ Ioo (s₀ - Real.log (1 - a)) (s₀ - Real.log (1 - b))) : 1 - r ^ 2 ∈ Ioo a b := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  obtain ⟨h1, h2⟩ := hs
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  constructor
  · have : r ^ 2 < 1 - a := by
      rw [← Real.log_lt_log_iff hr2 h1a, hlog]
      linarith
    linarith
  · have : 1 - b < r ^ 2 := by
      rw [← Real.log_lt_log_iff h1b hr2, hlog]
      linarith
    linarith

/-- For `1 ≤ α` and `0 ≤ x`, `x ^ (2 * 2) ≤ x ^ (2 * 1) + x ^ 2 * (2 * π * x) ^ (2 * α)`, where the
last factor is a real power. For `x ≤ 1` the term `x ^ 2` suffices, and for `x ≥ 1` one has
`x ^ 2 ≤ (2 * π * x) ^ (2 * α)`. -/
theorem pow_four_le_sq_add_mul_rpow {α : ℝ} (hα : 1 ≤ α) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (2 * 2) ≤ x ^ (2 * 1) + x ^ 2 * (2 * π * x) ^ (2 * α) := by
  have hw : 0 ≤ x ^ 2 * (2 * π * x) ^ (2 * α) := by positivity
  have h4 : x ^ (2 * 2) = x ^ 2 * x ^ 2 := by ring
  have h2 : x ^ (2 * 1) = x ^ 2 := by ring
  rw [h4, h2]
  rcases le_total x 1 with h | h
  · have hs : x ^ 2 ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_left hs (sq_nonneg x)
    linarith
  · have hpi := Real.pi_gt_three
    have h1 : 1 ≤ 2 * π * x := by nlinarith
    have hxy : x ^ 2 ≤ (2 * π * x) ^ (2 * α) := by
      calc x ^ 2 ≤ (2 * π * x) ^ 2 := pow_le_pow_left₀ hx (by nlinarith) 2
        _ = (2 * π * x) ^ (2 : ℝ) := (Real.rpow_two _).symm
        _ ≤ (2 * π * x) ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    have := mul_le_mul_of_nonneg_left hxy (sq_nonneg x)
    nlinarith [sq_nonneg x]

/-- For a natural `k ≥ 1` and reals `s > 0`, `t ≥ 0`, `c`, `A`, one has
`t ^ (2 * k) * (|(2 * π * t)⁻¹| * (c * A)) ^ 2 = c ^ 2 * s ^ 2 / s ^ (2 * k) * ((s * t) ^ (2 * k) *
(|(2 * π * (s * t))⁻¹| * A) ^ 2)`. For `t > 0` this is field arithmetic, and for `t =
0` both sides are zero because `2 * k ≠ 0`. -/
theorem pow_mul_abs_inv_mul_sq_eq (k : ℕ) (hk : 1 ≤ k) {s c t A : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    t ^ (2 * k) * (|(2 * π * t)⁻¹| * (c * A)) ^ 2 =
      c ^ 2 * s ^ 2 / s ^ (2 * k) * ((s * t) ^ (2 * k) * (|(2 * π * (s * t))⁻¹| * A) ^ 2) := by
  rcases ht.lt_or_eq with ht | ht
  · rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    field_simp
    ring
  · subst ht
    have h2k : 2 * k ≠ 0 := by omega
    simp [zero_pow h2k]

/-- For a natural number `n` and reals `0 < t`, `0 ≤ r`,
`r ^ n * Real.exp (-(t * r ^ 2)) ≤ n ! * t ^ (-((n : ℝ) / 2))`, where the power of `t` is a real
power. The proof squares both sides and uses `x ^ n / n ! ≤ Real.exp x` with `x = t * r ^ 2`. -/
theorem pow_mul_exp_neg_mul_sq_le (n : ℕ) {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : 0 ≤ r) :
    r ^ n * Real.exp (-(t * r ^ 2)) ≤ (n ! : ℝ) * t ^ (-((n : ℝ) / 2)) := by
  have hf : (1 : ℝ) ≤ n ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
  have hA : 0 ≤ r ^ n * Real.exp (-(t * r ^ 2)) := by positivity
  have hB : 0 ≤ (n ! : ℝ) * t ^ (-((n : ℝ) / 2)) := by positivity
  have htr : 0 ≤ t * r ^ 2 := by positivity
  have hexp := Real.pow_div_factorial_le_exp (t * r ^ 2) htr n
  have hfp : (0 : ℝ) < n ! := by positivity
  rw [div_le_iff₀ hfp] at hexp
  have hsq : (t ^ (-((n : ℝ) / 2))) ^ 2 = (t ^ n)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_natCast, ← Real.rpow_neg ht.le]
    congr 1
    push_cast
    ring
  have htn : 0 < t ^ n := pow_pos ht n
  have key : t ^ n * (r ^ n * Real.exp (-(t * r ^ 2))) ^ 2 ≤ (n ! : ℝ) := by
    have e : t ^ n * (r ^ n * Real.exp (-(t * r ^ 2))) ^ 2 =
        (t * r ^ 2) ^ n * Real.exp (-(t * r ^ 2)) * Real.exp (-(t * r ^ 2)) := by
      rw [mul_pow, ← pow_mul, mul_pow, pow_two (Real.exp _)]
      ring
    rw [e]
    calc (t * r ^ 2) ^ n * Real.exp (-(t * r ^ 2)) * Real.exp (-(t * r ^ 2))
        ≤ (Real.exp (t * r ^ 2) * n !) * Real.exp (-(t * r ^ 2)) * 1 := by
          gcongr
          exact Real.exp_le_one_iff.2 (by linarith)
      _ = n ! := by rw [mul_one, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; simp
  have h2 : (r ^ n * Real.exp (-(t * r ^ 2))) ^ 2 ≤ ((n ! : ℝ) * t ^ (-((n : ℝ) / 2))) ^ 2 := by
    rw [mul_pow (n ! : ℝ), hsq]
    calc (r ^ n * Real.exp (-(t * r ^ 2))) ^ 2 ≤ (n ! : ℝ) / t ^ n := (le_div_iff₀' htn).2 key
      _ = (n ! : ℝ) * (t ^ n)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (n ! : ℝ) ^ 2 * (t ^ n)⁻¹ := by
          gcongr
          nlinarith
  exact (pow_le_pow_iff_left₀ hA hB two_ne_zero).1 h2

/-- For `0 < s`, `0 < ρ`, any real `α` and a natural number `i`,
`s ^ (i + 1) * (s * ρ) ^ (-(2 * α - 1 + i)) = s ^ (2 - 2 * α) * ρ ^ (-(2 * α - 1 +
i))`. The first factor is a natural power and the other powers are real powers. -/
theorem pow_succ_mul_mul_rpow_neg_eq {s ρ α : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (i : ℕ) :
    s ^ (i + 1) * (s * ρ) ^ (-(2 * α - 1 + i)) = s ^ (2 - 2 * α) * ρ ^ (-(2 * α - 1 + i)) := by
  rw [Real.mul_rpow hs.le hρ.le, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hs]
  rw [show ((↑(i + 1) : ℝ) + -(2 * α - 1 + ↑i)) = 2 - 2 * α by push_cast; ring]

/-- For real `A > 0` and `u ≥ 0`, `u ^ 3 * Real.exp (-(A * u)) ≤ 6 / A ^ 3`. This follows from
`(A * u) ^ 3 / 6 ≤ Real.exp (A * u)`. -/
theorem pow_three_mul_exp_neg_mul_le {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    u ^ 3 * Real.exp (-(A * u)) ≤ 6 / A ^ 3 := by
  have h := Real.pow_div_factorial_le_exp (A * u) (mul_nonneg hA.le hu) 3
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  have h' : (A * u) ^ 3 ≤ 6 * Real.exp (A * u) := by linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (pow_pos hA 3)]
  rw [mul_pow] at h'
  linarith

/-- For real numbers with `L > 0`, `r > 1`, `γ ≤ β`, `β ≥ 0`, `j ≥ 0` and `0 < s ≤ L / r`,
`s ^ (β + j) ≤ L ^ (β + j) * r ^ (-(γ + j))`. -/
theorem rpow_add_le_rpow_mul_rpow_neg {L r β γ j s : ℝ} (hL : 0 < L) (hr : 1 < r) (hβγ : γ ≤ β)
    (hβ : 0 ≤ β) (hj : 0 ≤ j)
    (hs : 0 < s) (hsr : s ≤ L / r) : s ^ (β + j) ≤ L ^ (β + j) * r ^ (-(γ + j)) := by
  have hr0 : 0 < r := by linarith
  calc s ^ (β + j) ≤ (L / r) ^ (β + j) := Real.rpow_le_rpow hs.le hsr (by linarith)
    _ = L ^ (β + j) * r ^ (-(β + j)) := by
      rw [Real.div_rpow hL.le hr0.le, Real.rpow_neg hr0.le, div_eq_mul_inv]
    _ ≤ L ^ (β + j) * r ^ (-(γ + j)) := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr.le (by
        linarith)) (by positivity)

/-- For `0 ≤ lam`, real `θ` and `κ`, and a natural number `n`,
`(lam ^ κ / θ) ^ n = (θ⁻¹) ^ n * (lam ^ n) ^ κ`. -/
theorem rpow_div_pow_eq_inv_pow_mul {lam θ κ : ℝ} (hl : 0 ≤ lam) (n : ℕ) :
    (lam ^ κ / θ) ^ n = (θ⁻¹) ^ n * (lam ^ n) ^ κ := by
  rw [div_eq_mul_inv, mul_pow, rpow_pow_comm hl, mul_comm]

/-- For `0 ≤ s` and a real exponent `p` with `0 ≤ p ≤ 1`, `s ^ p ≤ Real.exp s`. The proof uses
`s ^ p ≤ 1 + s ≤ Real.exp s`. -/
theorem rpow_le_exp_of_le_one {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    s ^ p ≤ Real.exp s := by
  have h : s ^ p ≤ 1 + s := by
    rcases le_total s 1 with h | h
    · linarith [Real.rpow_le_one hs h hp0]
    · have h2 := Real.rpow_le_rpow_of_exponent_le h hp1
      rw [Real.rpow_one] at h2
      linarith
  linarith [Real.add_one_le_exp s]

/-- For real `r ≥ 0` and a real exponent `s` with `1 ≤ s ≤ 3`, `r ^ s ≤ r ^ (1 : ℕ) + r ^ (3 : ℕ)`.
The proof compares `r ^ s` with `r` when `r ≤ 1` and with `r ^ 3` when `1 ≤ r`. -/
theorem rpow_le_pow_one_add_pow_three {r : ℝ} (hr : 0 ≤ r) {s : ℝ} (h1 : 1 ≤ s) (h3 : s ≤ 3) :
    r ^ s ≤ r ^ (1 : ℕ) + r ^ (3 : ℕ) := by
  rcases hr.eq_or_lt with h | h
  · subst h; rw [Real.zero_rpow (by linarith)]; simp
  rcases le_total r 1 with hle | hle
  · have := Real.rpow_le_rpow_of_exponent_ge h hle h1
    rw [Real.rpow_one] at this
    have : 0 ≤ r ^ (3 : ℕ) := by positivity
    simp only [pow_one]; linarith
  · have := Real.rpow_le_rpow_of_exponent_le hle h3
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have : 0 ≤ r ^ (1 : ℕ) := by positivity
    linarith

/-- If `c > 0`, `ρ > 0` and `c * ρ ≤ u ≤ C * ρ`, then `u ^ q ≤ (c ^ q + C ^ q) * ρ ^ q` for every
real exponent `q`, of either sign. The proof writes `u = (u / ρ) * ρ` and bounds `(u / ρ) ^ q` by
`C ^ q` when `q ≥ 0` and by `c ^ q` when `q ≤ 0`. -/
theorem rpow_le_rpow_add_rpow_mul_rpow {c C ρ u : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (h1 : c * ρ ≤ u)
    (h2 : u ≤ C * ρ) (q : ℝ) :
    u ^ q ≤ (c ^ q + C ^ q) * ρ ^ q := by
  have hθ0 : c ≤ u / ρ := by rw [le_div_iff₀ hρ]; exact h1
  have hθ1 : u / ρ ≤ C := by rw [div_le_iff₀ hρ]; exact h2
  have hθ : 0 < u / ρ := lt_of_lt_of_le hc hθ0
  have e : u = (u / ρ) * ρ := by field_simp
  rw [e, Real.mul_rpow hθ.le hρ.le]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hρ.le q)
  have hcq := Real.rpow_nonneg hc.le q
  have hCq := Real.rpow_nonneg (hc.le.trans (hθ0.trans hθ1)) q
  rcases le_total 0 q with hq | hq
  · have := Real.rpow_le_rpow hθ.le hθ1 hq
    linarith
  · have := Real.rpow_le_rpow_of_nonpos hc hθ0 hq
    linarith

/-- For reals `0 < lo ≤ μ ≤ hi` and any real exponent `s`, `μ ^ s ≤ lo ^ s + hi ^ s`. For `s ≥ 0`
the left side is at most `hi ^ s`, and for `s ≤ 0` it is at most `lo ^ s`. -/
theorem rpow_le_rpow_add_rpow_of_le {lo hi μ : ℝ} (s : ℝ) (hlo : 0 < lo) (h1 : lo ≤ μ)
    (h2 : μ ≤ hi) :
    μ ^ s ≤ lo ^ s + hi ^ s := by
  have a1 := Real.rpow_nonneg hlo.le s
  have a2 := Real.rpow_nonneg (hlo.le.trans (h1.trans h2)) s
  rcases le_total 0 s with hs | hs
  · have := Real.rpow_le_rpow (hlo.le.trans h1) h2 hs
    linarith
  · have := Real.rpow_le_rpow_of_nonpos hlo h1 hs
    linarith

/-- If `0 < r`, `0 < X`, `r * X ≤ 1` and `0 ≤ p`, then `X ^ p ≤ r ^ (-p)`. -/
theorem rpow_le_rpow_neg_of_mul_le {r X p : ℝ} (hr : 0 < r) (hX : 0 < X) (hrX : r * X ≤ 1)
    (hp : 0 ≤ p) :
    X ^ p ≤ r ^ (-p) := by
  have h1 : (r * X) ^ p ≤ 1 := Real.rpow_le_one (by positivity) hrX hp
  rw [Real.mul_rpow hr.le hX.le] at h1
  rw [Real.rpow_neg hr.le, inv_eq_one_div, le_div_iff₀ (Real.rpow_pos_of_pos hr p)]
  linarith [mul_comm (r ^ p) (X ^ p)]

/-- For `0 ≤ s` and `0 < q`, `s ^ q ≤ q ^ q * Real.exp s`. The proof raises
`s / q ≤ Real.exp (s / q)` to the power `q`. -/
theorem rpow_le_rpow_self_mul_exp {s q : ℝ} (hs : 0 ≤ s) (hq : 0 < q) :
    s ^ q ≤ q ^ q * Real.exp s := by
  have h1 : s / q ≤ Real.exp (s / q) := by
    have := Real.add_one_le_exp (s / q); linarith
  have h2 : (s / q) ^ q ≤ Real.exp (s / q) ^ q :=
    Real.rpow_le_rpow (div_nonneg hs hq.le) h1 hq.le
  rw [← Real.exp_mul, div_mul_cancel₀ s hq.ne', Real.div_rpow hs hq.le] at h2
  have hqq : 0 < q ^ q := Real.rpow_pos_of_pos hq q
  rw [div_le_iff₀ hqq] at h2
  calc s ^ q ≤ Real.exp s * q ^ q := h2
    _ = q ^ q * Real.exp s := mul_comm _ _

/-- For `0 < u`, `0 < w`, `w ≤ 2 * u` and a real exponent `r` with `-1 ≤ r ≤ 0`,
`u ^ r ≤ 2 * w ^ r`. -/
theorem rpow_le_two_mul_rpow {u w r : ℝ} (hu : 0 < u) (hw : 0 < w) (hwu : w ≤ 2 * u) (hr : -1 ≤ r)
    (hr0 : r ≤ 0) : u ^ r ≤ 2 * w ^ r := by
  have h1 : (2 * u) ^ r ≤ w ^ r := rpow_le_rpow_of_nonpos hw hwu hr0
  rw [mul_rpow (by norm_num) hu.le] at h1
  have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ r := rpow_le_rpow_of_exponent_le (by norm_num) hr
  rw [rpow_neg_one] at h2
  have h3 : 0 ≤ u ^ r := rpow_nonneg hu.le r
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

/-- Let `1 ≤ r`, `γt ≤ 1 + γD`, `γt ≤ 4` and `0 ≤ x`, `0 ≤ d`, `0 ≤ y`. If `r ^ (1 : ℝ) * x ≤ A`,
`r ^ γD * d ≤ M` and `r ^ (2 : ℝ) * y ≤ B`, then
`r ^ γt * (2 * (x * d) + 2 * (y * y)) ≤ 2 * (A * M) + 2 * (B * B)`. The proof uses
`r ^ γt ≤ r ^ (1 : ℝ) * r ^ γD` and `r ^ γt ≤ r ^ (2 : ℝ) * r ^ (2 : ℝ)`, which hold because
`1 ≤ r`. -/
theorem rpow_mul_add_mul_le_of_le {r γD γt A B M x d y : ℝ} (hr : 1 ≤ r) (h1 : γt ≤ 1 + γD)
    (h4 : γt ≤ 4)
    (hx0 : 0 ≤ x) (hd0 : 0 ≤ d) (hy0 : 0 ≤ y) (hx : r ^ (1 : ℝ) * x ≤ A)
    (hd : r ^ γD * d ≤ M) (hy : r ^ (2 : ℝ) * y ≤ B) :
    r ^ γt * (2 * (x * d) + 2 * (y * y)) ≤ 2 * (A * M) + 2 * (B * B) := by
  have hr0 : 0 < r := by linarith
  have e1 : r ^ γt ≤ r ^ (1 : ℝ) * r ^ γD := by
    rw [← Real.rpow_add hr0]
    exact Real.rpow_le_rpow_of_exponent_le hr h1
  have e2 : r ^ γt ≤ r ^ (2 : ℝ) * r ^ (2 : ℝ) := by
    rw [← Real.rpow_add hr0]
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have p1 : r ^ γt * (x * d) ≤ A * M :=
    calc r ^ γt * (x * d) ≤ (r ^ (1 : ℝ) * r ^ γD) * (x * d) :=
          mul_le_mul_of_nonneg_right e1 (by positivity)
      _ = (r ^ (1 : ℝ) * x) * (r ^ γD * d) := by ring
      _ ≤ A * M := mul_le_mul hx hd (by positivity) (le_trans (by positivity) hx)
  have p2 : r ^ γt * (y * y) ≤ B * B :=
    calc r ^ γt * (y * y) ≤ (r ^ (2 : ℝ) * r ^ (2 : ℝ)) * (y * y) :=
          mul_le_mul_of_nonneg_right e2 (by positivity)
      _ = (r ^ (2 : ℝ) * y) * (r ^ (2 : ℝ) * y) := by ring
      _ ≤ B * B := mul_le_mul hy hy (by positivity) (le_trans (by positivity) hy)
  calc r ^ γt * (2 * (x * d) + 2 * (y * y)) = 2 * (r ^ γt * (x * d)) + 2 * (r ^ γt * (y * y)) := by
        ring
    _ ≤ 2 * (A * M) + 2 * (B * B) := by linarith

/-- For real numbers with `y ≥ 0`, `s > 0` and `0 ≤ g ≤ 1`,
`y ^ g * Real.exp (-(y * s)) ≤ s ^ (-g)`. This is `rpow_mul_exp_neg_mul_le_rpow` with the product in
the exponent written `y * s`. -/
theorem rpow_mul_exp_le {y s g : ℝ} (hy : 0 ≤ y) (hs : 0 < s) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    y ^ g * Real.exp (-(y * s)) ≤ s ^ (-g) := by
  rw [mul_comm y s]
  exact rpow_mul_exp_neg_mul_le_rpow hy hs hg0 hg1

/-- For `0 < ℓ` and `0 < α`,
`ℓ ^ (-(1 - 1 / α)) * ((ℓ ^ (1 / (2 * α)))⁻¹ * ℓ ^ (1 - 1 / (2 * α))) = 1`, because the three
exponents add up to zero. -/
theorem rpow_mul_inv_mul_rpow_eq_one {α : ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) :
    ℓ ^ (-(1 - 1 / α)) * ((ℓ ^ (1 / (2 * α)))⁻¹ * ℓ ^ (1 - 1 / (2 * α))) = 1 := by
  rw [← Real.rpow_neg hℓ.le, ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
  have e : -(1 - 1 / α) + (-(1 / (2 * α)) + (1 - 1 / (2 * α))) = 0 := by
    field_simp
    ring
  rw [e, Real.rpow_zero]

/-- For `0 < α`, `0 < μ` and `0 ≤ r`,
`μ ^ (1 - 1 / (2 * α)) * (μ ^ (1 / (2 * α)) * (1 + r)) ^ (-(2 * α - 1)) = (1 + r) ^ (-(2 * α -
1))`, because the powers of `μ` cancel. -/
theorem rpow_mul_mul_one_add_rpow_eq {α μ r : ℝ} (hα : 0 < α) (hμ : 0 < μ) (hr : 0 ≤ r) :
    μ ^ (1 - 1 / (2 * α)) * (μ ^ (1 / (2 * α)) * (1 + r)) ^ (-(2 * α - 1)) =
      (1 + r) ^ (-(2 * α - 1)) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hμ.le _) (by linarith), ← Real.rpow_mul hμ.le, ← mul_assoc,
    ← Real.rpow_add hμ]
  have he : 1 - 1 / (2 * α) + 1 / (2 * α) * -(2 * α - 1) = 0 := by field_simp; ring
  rw [he, Real.rpow_zero, one_mul]

/-- For `0 < μ` and any real `α`, `μ ^ (1 / (2 * α)) * μ ^ (-(1 / (2 * α))) = 1`. -/
theorem rpow_mul_rpow_neg_eq_one {α μ : ℝ} (hμ : 0 < μ) :
    μ ^ (1 / (2 * α)) * μ ^ (-(1 / (2 * α))) = 1 := by
  rw [← Real.rpow_add hμ, add_neg_cancel, Real.rpow_zero]

/-- For real `L > 0`, `s > 0`, `b ≥ 0` and a natural number `i`,
`L ^ b * (s + L) ^ (-b - i) ≤ ((s + L) ^ i)⁻¹`, where the powers on the left are real powers. The
proof splits `(s + L) ^ (-b - i)` as `((s + L) ^ b)⁻¹ * ((s + L) ^ i)⁻¹` and uses
`L ^ b ≤ (s + L) ^ b`. -/
theorem rpow_mul_rpow_sub_le_inv_pow {L b s : ℝ} (hL : 0 < L) (hs : 0 < s) (hb0 : 0 ≤ b) (i : ℕ) :
    L ^ b * (s + L) ^ (-b - i) ≤ ((s + L) ^ i)⁻¹ := by
  have hpos : 0 < s + L := by linarith
  rw [Real.rpow_sub hpos, Real.rpow_natCast, Real.rpow_neg hpos.le, div_eq_mul_inv, ← mul_assoc]
  have h1 : L ^ b * ((s + L) ^ b)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hpos b)]
    exact Real.rpow_le_rpow hL.le (by linarith) hb0
  have h2 : 0 ≤ ((s + L) ^ i)⁻¹ := by positivity
  calc L ^ b * ((s + L) ^ b)⁻¹ * ((s + L) ^ i)⁻¹ ≤ 1 * ((s + L) ^ i)⁻¹ := by gcongr
    _ = ((s + L) ^ i)⁻¹ := one_mul _

/-- For `1 < α` and `0 < ℓ ≤ 1`,
`ℓ ^ (1 / α) * ((ℓ ^ (1 - 1 / (2 * α))) ^ 2 * ((ℓ ^ (1 / (2 * α))) ^ 3)⁻¹) ≤ 1`. The left side
equals `ℓ ^ (2 - 3 / (2 * α))`, and this exponent is nonnegative. -/
theorem rpow_mul_sq_mul_inv_cube_le {α : ℝ} (hα : 1 < α) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ℓ ^ (1 / α) * ((ℓ ^ (1 - 1 / (2 * α))) ^ 2 * ((ℓ ^ (1 / (2 * α))) ^ 3)⁻¹) ≤ 1 := by
  have e : ℓ ^ (1 / α) * ((ℓ ^ (1 - 1 / (2 * α))) ^ 2 * ((ℓ ^ (1 / (2 * α))) ^ 3)⁻¹) =
      ℓ ^ (2 - 3 / (2 * α)) := by
    rw [← Real.rpow_natCast (ℓ ^ (1 - 1 / (2 * α))), ← Real.rpow_mul hℓ.le,
      ← Real.rpow_natCast (ℓ ^ (1 / (2 * α))), ← Real.rpow_mul hℓ.le, ← Real.rpow_neg hℓ.le,
      ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
    congr 1
    push_cast
    field_simp
    ring
  rw [e]
  refine Real.rpow_le_one hℓ.le hℓ1 ?_
  rw [sub_nonneg, div_le_iff₀ (by linarith)]
  linarith

/-- For real `μ > 0`, `lam > 0` and `0 ≤ s ≤ 1`,
`(μ * lam) ^ (-(1 / 2 : ℝ)) * (μ * s) ^ (1 / 2 : ℝ) ≤ lam ^ (-(1 / 2 : ℝ))`. The powers of `μ`
cancel and `s ^ (1 / 2 : ℝ) ≤ 1`. -/
theorem rpow_neg_half_mul_rpow_half_le {μ lam s : ℝ} (hμ : 0 < μ) (hl : 0 < lam) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    (μ * lam) ^ (-(1 / 2 : ℝ)) * (μ * s) ^ (1 / 2 : ℝ) ≤ lam ^ (-(1 / 2 : ℝ)) := by
  rw [Real.mul_rpow hμ.le hl.le, Real.mul_rpow hμ.le hs0]
  have e : μ ^ (-(1 / 2 : ℝ)) * μ ^ (1 / 2 : ℝ) = 1 := by
    rw [← rpow_add hμ]; norm_num
  have h1 : s ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hs0 hs1 (by norm_num)
  have h2 : 0 ≤ lam ^ (-(1 / 2 : ℝ)) := rpow_nonneg hl.le _
  calc μ ^ (-(1 / 2 : ℝ)) * lam ^ (-(1 / 2 : ℝ)) * (μ ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ))
      = lam ^ (-(1 / 2 : ℝ)) * s ^ (1 / 2 : ℝ) * (μ ^ (-(1 / 2 : ℝ)) * μ ^ (1 / 2 : ℝ)) := by ring
    _ ≤ lam ^ (-(1 / 2 : ℝ)) * 1 * 1 := by rw [e]; gcongr
    _ = lam ^ (-(1 / 2 : ℝ)) := by ring

/-- For `1 < α` and `0 < r ≤ T`,
`r ^ (-(1 / (2 * α))) ≤ (max T 1) ^ (1 / 2 - 1 / (2 * α)) * r ^ (-(1 / 2 : ℝ))`. The left side
equals `r ^ (1 / 2 - 1 / (2 * α)) * r ^ (-(1 / 2 : ℝ))`, and `r ≤ max T 1` while the exponent
`1 / 2 - 1 / (2 * α)` is nonnegative. -/
theorem rpow_neg_le_max_rpow_mul_rpow (α T r : ℝ) (hα : 1 < α) (hr : 0 < r) (hrT : r ≤ T) :
    r ^ (-(1 / (2 * α))) ≤ max T 1 ^ (1 / 2 - 1 / (2 * α)) * r ^ (-(1 / 2 : ℝ)) := by
  have hβ : 1 / (2 * α) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hsplit : r ^ (-(1 / (2 * α))) = r ^ (1 / 2 - 1 / (2 * α)) * r ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  rw [hsplit]
  gcongr
  exact hrT.trans (le_max_left _ _)

/-- For `1 ≤ x` and `0 ≤ r`, `x ^ (-r) ≤ 2 ^ r * (1 + x) ^ (-r)`, because `1 + x ≤ 2 * x`. -/
theorem rpow_neg_le_mul_one_add_rpow (x r : ℝ) (hx : 1 ≤ x) (hr : 0 ≤ r) :
    x ^ (-r) ≤ 2 ^ r * (1 + x) ^ (-r) := by
  have hle : (2 * x) ^ (-r) ≤ (1 + x) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have heq : x ^ (-r) = 2 ^ r * (2 * x) ^ (-r) := by
    rw [Real.mul_rpow (by norm_num) (by linarith), ← mul_assoc, ← Real.rpow_add (by norm_num),
      add_neg_cancel, Real.rpow_zero, one_mul]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- If `0 < r`, `0 < X`, `1 ≤ 16 * r * X` and `0 ≤ p`, then `X ^ (-p) ≤ 16 ^ p * r ^ p`. -/
theorem rpow_neg_le_of_one_le_mul {r X p : ℝ} (hr : 0 < r) (hX : 0 < X) (hrX : 1 ≤ 16 * r * X)
    (hp : 0 ≤ p) :
    X ^ (-p) ≤ 16 ^ p * r ^ p := by
  have h1 : 1 ≤ (16 * r * X) ^ p := Real.one_le_rpow hrX hp
  rw [Real.mul_rpow (by positivity) hX.le, Real.mul_rpow (by norm_num) hr.le] at h1
  rw [Real.rpow_neg hX.le, inv_eq_one_div, div_le_iff₀ (Real.rpow_pos_of_pos hX p)]
  exact h1

/-- For `1 ≤ t`, a natural number `n` and a real `r` with `(n : ℝ) ≤ r`, `t ^ (-r) ≤ 1 / t ^ n`. -/
theorem rpow_neg_le_one_div_pow {t r : ℝ} (n : ℕ) (ht : 1 ≤ t) (hr : (n : ℝ) ≤ r) :
    t ^ (-r) ≤ 1 / t ^ n := by
  have h := Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg hr)
  have h2 : t ^ (-(n : ℝ)) = 1 / t ^ n := by
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast, one_div]
  exact h.trans h2.le

/-- For real `r ≥ 1` and real exponents `b ≤ a`, `r ^ (-a) ≤ r ^ (-b)`. -/
theorem rpow_neg_le_rpow_neg_of_le {r : ℝ} (hr : 1 ≤ r) {a b : ℝ} (h : b ≤ a) :
    r ^ (-a) ≤ r ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_le hr (by linarith)

/-- If `1 / 16 ≤ ρ` and `0 ≤ e ≤ 5`, then `ρ ^ (-e) ≤ (1 / 16 : ℝ) ^ (-(5 : ℝ))`. -/
theorem rpow_neg_le_sixteenth_rpow_neg_five {ρ e : ℝ} (hρ : 1 / 16 ≤ ρ) (he0 : 0 ≤ e) (he : e ≤ 5) :
    ρ ^ (-e) ≤ (1 / 16 : ℝ) ^ (-(5 : ℝ)) :=
  (Real.rpow_le_rpow_of_nonpos (by norm_num) hρ (by linarith)).trans
    (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith))

/-- For real numbers with `Y > 0`, `Y / 2 ≤ Z` and `b ≥ 0`, `Z ^ (-b) ≤ 2 ^ b * Y ^ (-b)`. -/
theorem rpow_neg_le_two_rpow_mul_rpow {Y Z b : ℝ} (hY : 0 < Y) (hZ : Y / 2 ≤ Z) (hb : 0 ≤ b) :
    Z ^ (-b) ≤ (2 : ℝ) ^ b * Y ^ (-b) := by
  have h1 : Z ^ (-b) ≤ (Y / 2) ^ (-b) := Real.rpow_le_rpow_of_nonpos (by
    positivity) hZ (by linarith)
  have h2 : (Y / 2) ^ (-b) = (2 : ℝ) ^ b * Y ^ (-b) := by
    rw [Real.div_rpow hY.le (by
      norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) b, div_inv_eq_mul]
    ring
  linarith

/-- For real `Y > 0` and real `b`, `Y ^ (-b) * Y⁻¹ = Y ^ (-(b + 1))`. -/
theorem rpow_neg_mul_inv_eq_rpow_neg {Y : ℝ} (hY : 0 < Y) (b : ℝ) :
    Y ^ (-b) * Y⁻¹ = Y ^ (-(b + 1)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hY]
  ring_nf

/-- For `0 < μ`, `0 ≤ r` and real `g`, `β`, `K`,
`μ ^ (-(g * β)) * (K * (1 + μ ^ (-g) * r) ^ (-β)) = K * (μ ^ g + r) ^ (-β)`. The proof factors
`1 + μ ^ (-g) * r = μ ^ (-g) * (μ ^ g + r)`. -/
theorem rpow_neg_mul_one_add_rpow_eq (μ g β K r : ℝ) (hμ : 0 < μ) (hr : 0 ≤ r) :
    μ ^ (-(g * β)) * (K * (1 + μ ^ (-g) * r) ^ (-β)) = K * (μ ^ g + r) ^ (-β) := by
  have h1 : 1 + μ ^ (-g) * r = μ ^ (-g) * (μ ^ g + r) := by
    rw [mul_add, ← rpow_add hμ, neg_add_cancel, rpow_zero]
  have hs : 0 < μ ^ g + r := add_pos_of_pos_of_nonneg (rpow_pos_of_pos hμ _) hr
  have h2 : (μ ^ (-g) * (μ ^ g + r)) ^ (-β) = μ ^ (g * β) * (μ ^ g + r) ^ (-β) := by
    rw [mul_rpow (rpow_nonneg hμ.le _) hs.le, ← rpow_mul hμ.le]
    congr 2
    ring
  have h3 : 0 < μ ^ (g * β) := rpow_pos_of_pos hμ _
  rw [h1, h2, rpow_neg hμ.le]
  field_simp

/-- Let `1 < α < 3 / 2` and let `a ≥ 1`, `b ≥ 1`, `t ≥ 1` be reals with `a ≤ 2 * t * b`. Then
`t ^ (-(3 + 2 * α)) * b ^ (-(10 : ℝ)) ≤ 2 ^ (3 + 2 * α) * (a ^ (-(3 + 2 * α)) * b ^ (-(4 :
ℝ)))`. The proof raises `a ≤ 2 * t * b` to the power `3 + 2 * α`, which is at most `6`, and uses `b
^ (6 : ℝ) * b ^ (4 : ℝ) = b ^ (10 : ℝ)`. -/
theorem rpow_neg_mul_rpow_neg_ten_le (α : ℝ) (hα2 : α < 3 / 2) (hα1 : 1 < α) {a b t : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ht : 1 ≤ t) (h : a ≤ 2 * t * b) :
    t ^ (-(3 + 2 * α)) * b ^ (-(10 : ℝ)) ≤
      2 ^ (3 + 2 * α) * (a ^ (-(3 + 2 * α)) * b ^ (-(4 : ℝ))) := by
  set s := 3 + 2 * α with hs
  have hs0 : 0 ≤ s := by linarith
  have key : a ^ s * b ^ (4 : ℝ) ≤ 2 ^ s * t ^ s * b ^ (10 : ℝ) := by
    calc a ^ s * b ^ (4 : ℝ) ≤ (2 * t * b) ^ s * b ^ (4 : ℝ) := by
          gcongr
      _ = 2 ^ s * t ^ s * (b ^ s * b ^ (4 : ℝ)) := by
          rw [mul_rpow (by positivity) (by linarith), mul_rpow (by norm_num) (by linarith)]; ring
      _ ≤ 2 ^ s * t ^ s * (b ^ (6 : ℝ) * b ^ (4 : ℝ)) := by
          gcongr
          linarith
      _ = 2 ^ s * t ^ s * b ^ (10 : ℝ) := by
          rw [← rpow_add (by linarith)]; norm_num
  have hta : 0 < t ^ s := rpow_pos_of_pos (by linarith) _
  have haa : 0 < a ^ s := rpow_pos_of_pos (by linarith) _
  have hb4 : 0 < b ^ (4 : ℝ) := rpow_pos_of_pos (by linarith) _
  have hb10 : 0 < b ^ (10 : ℝ) := rpow_pos_of_pos (by linarith) _
  rw [rpow_neg (by
    linarith), rpow_neg (by linarith), rpow_neg (by linarith), rpow_neg (by linarith),
    ← mul_inv, ← mul_inv, ← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by
      positivity) (by positivity)]
  linarith

/-- For `0 < μ` and any real `α`, `μ ^ (-(1 / (2 * α))) = (μ ^ (1 / (2 * α)))⁻¹`. This is
`Real.rpow_neg` at the exponent `1 / (2 * α)`. -/
theorem rpow_neg_one_div_eq_inv_rpow {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ ^ (-(1 / (2 * α))) = (μ ^ (1 / (2 * α)))⁻¹ :=
  Real.rpow_neg hμ.le _

/-- For real `r > 0` and real `a`, `q`, `(r ^ (-a)) ^ q = r ^ (-(a * q))`. -/
theorem rpow_neg_rpow_eq_rpow_neg_mul {r : ℝ} (hr : 0 < r) (a q : ℝ) :
    (r ^ (-a)) ^ q = r ^ (-(a * q)) := by
  rw [← Real.rpow_mul hr.le]
  congr 1
  ring

/-- For real `a > 0` and `c` with `a ≤ 2 * c`, one has
`c ^ (-(10 : ℝ)) ≤ 2 ^ (10 : ℝ) * a ^ (-(10 : ℝ))`. The proof applies to `a ≤ 2 * c` the fact that
`x ↦ x ^ (-(10 : ℝ))` is antitone on positive reals. -/
theorem rpow_neg_ten_le_of_le_mul {a c : ℝ} (ha : 0 < a) (h : a ≤ 2 * c) :
    c ^ (-(10 : ℝ)) ≤ 2 ^ (10 : ℝ) * a ^ (-(10 : ℝ)) := by
  have hc : 0 < c := by linarith
  have h1 : (2 * c) ^ (-(10 : ℝ)) ≤ a ^ (-(10 : ℝ)) :=
    rpow_le_rpow_of_nonpos ha h (by norm_num)
  rw [mul_rpow (by norm_num) hc.le] at h1
  have h2 : (2 : ℝ) ^ (10 : ℝ) * (2 : ℝ) ^ (-(10 : ℝ)) = 1 := by
    rw [← rpow_add (by norm_num)]; norm_num
  have h3 : (0 : ℝ) ≤ 2 ^ (10 : ℝ) := by positivity
  calc c ^ (-(10 : ℝ)) = 2 ^ (10 : ℝ) * (2 ^ (-(10 : ℝ)) * c ^ (-(10 : ℝ))) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ 2 ^ (10 : ℝ) * a ^ (-(10 : ℝ)) := mul_le_mul_of_nonneg_left h1 h3

/-- For real `a > 0`, the real power `a ^ (-3)` equals `(a ^ 3)⁻¹`, where `a ^ 3` is the natural
power. -/
theorem rpow_neg_three_eq {a : ℝ} (ha : 0 < a) : a ^ (-(3 : ℝ)) = (a ^ 3)⁻¹ := by
  rw [Real.rpow_neg ha.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- For `0 < μ` and `α ≠ 0`, `(μ ^ (1 / (2 * α))) ^ (2 * α) = μ`. -/
theorem rpow_one_div_rpow_two_mul {μ α : ℝ} (hμ : 0 < μ) (hα : α ≠ 0) :
    (μ ^ (1 / (2 * α))) ^ (2 * α) = μ := by
  rw [← Real.rpow_mul hμ.le]
  have : 1 / (2 * α) * (2 * α) = 1 := by field_simp
  rw [this, Real.rpow_one]

/-- For `0 < μ` and any real `α`, `μ ^ (1 - 1 / (2 * α)) = μ * (μ ^ (1 / (2 * α)))⁻¹`. -/
theorem rpow_one_sub_eq_mul_inv_rpow {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ ^ (1 - 1 / (2 * α)) = μ * (μ ^ (1 / (2 * α)))⁻¹ := by
  rw [Real.rpow_sub hμ, Real.rpow_one, div_eq_mul_inv]

/-- For real `t > 0` and `a`, `(t ^ a) ^ (3 : ℕ) = t ^ (a * 3)`. -/
theorem rpow_pow_three {t : ℝ} (ht : 0 < t) (a : ℝ) : (t ^ a) ^ (3 : ℕ) = t ^ (a * 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

/-- For `α ≠ 0` and `0 < l`, each of the three products
`l ^ (1 - 1 / (2 * α)) * (l ^ (1 / (2 * α))) ^ (2 * α)`,
`l ^ (1 - 1 / (2 * α)) * l ^ (1 / (2 * α)) * l ^ (1 - 1 / (2 * α))` and
`l ^ (2 - 1 / α) * l ^ (1 / (2 * α))` equals `l ^ (1 - 1 / (2 * α)) * l`. Each identity follows from
the rules for adding and multiplying real exponents. -/
theorem rpow_products_eq_rpow_mul_self (α l : ℝ) (hα : α ≠ 0) (hl : 0 < l) :
    l ^ (1 - 1 / (2 * α)) * (l ^ (1 / (2 * α))) ^ (2 * α) = l ^ (1 - 1 / (2 * α)) * l ∧
    l ^ (1 - 1 / (2 * α)) * l ^ (1 / (2 * α)) * l ^ (1 - 1 / (2 * α)) =
      l ^ (1 - 1 / (2 * α)) * l ∧
    l ^ (2 - 1 / α) * l ^ (1 / (2 * α)) = l ^ (1 - 1 / (2 * α)) * l := by
  have e1 : 1 / (2 * α) * (2 * α) = 1 := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.rpow_mul hl.le, e1, Real.rpow_one]
  · rw [← Real.rpow_add hl, sub_add_cancel, Real.rpow_one, mul_comm]
  · rw [← Real.rpow_add hl, ← Real.rpow_add_one hl.ne']
    congr 1
    field_simp
    ring

/-- For `0 ≤ A` and `0 ≤ N`,
`(A * N ^ 2) ^ (1 / 4 : ℝ) * (A ^ 2 * N ^ 2) ^ (1 / 4 : ℝ) = A ^ (3 / 4 : ℝ) * N`. The product of
the two bases is `(A ^ (3 / 4 : ℝ) * N) ^ 4`. -/
theorem rpow_quarter_mul_rpow_quarter_eq {A N : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N) :
    (A * N ^ 2) ^ (1 / 4 : ℝ) * (A ^ 2 * N ^ 2) ^ (1 / 4 : ℝ) = A ^ (3 / 4 : ℝ) * N := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  have e : A * N ^ 2 * (A ^ 2 * N ^ 2) = (A ^ (3 / 4 : ℝ) * N) ^ (4 : ℕ) := by
    rw [mul_pow, ← Real.rpow_natCast (A ^ (3 / 4 : ℝ)), ← Real.rpow_mul hA,
      show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [e, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]

/-- For `0 ≤ r` and any real `x`, `(r ^ x) ^ 2 = r ^ (2 * x)`. -/
theorem rpow_sq_eq_rpow_two_mul (r x : ℝ) (hr : 0 ≤ r) : (r ^ x) ^ 2 = r ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  congr 1
  push_cast
  ring

/-- For `0 < α` and `0 < μ`,
`(μ ^ (1 - 1 / (2 * α))) ^ 2 * (μ ^ (-(1 / (2 * α)))) ^ 3 = μ ^ (-((5 - 4 * α) / (2 * α)))`. -/
theorem rpow_sq_mul_rpow_cube_eq_rpow {α μ : ℝ} (hα : 0 < α) (hμ : 0 < μ) :
    (μ ^ (1 - 1 / (2 * α))) ^ 2 * (μ ^ (-(1 / (2 * α)))) ^ 3 = μ ^ (-((5 - 4 * α) / (2 * α))) := by
  rw [← Real.rpow_natCast (μ ^ (1 - 1 / (2 * α))) 2, ← Real.rpow_natCast (μ ^ (-(1 / (2 * α)))) 3,
    ← Real.rpow_mul hμ.le, ← Real.rpow_mul hμ.le, ← Real.rpow_add hμ]
  congr 1
  push_cast
  field_simp
  ring

/-- For `0 < X` and any real `p`, `(X ^ p) ^ 2 = X ^ (2 * p)`. -/
theorem rpow_sq_of_pos {X p : ℝ} (hX : 0 < X) : (X ^ p) ^ 2 = X ^ (2 * p) := by
  rw [mul_comm, Real.rpow_mul hX.le, Real.rpow_two]

/-- For `1 ≤ p` and `0 ≤ a ≤ b`, `b ^ p - a ^ p ≤ p * b ^ (p - 1) * (b - a)`. For `a < b` the proof
applies Bernoulli's inequality `1 + p * s ≤ (1 + s) ^ p` with `s = a / b - 1` and multiplies by
`b ^ p`. -/
theorem rpow_sub_rpow_le_mul_sub {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hab : a ≤ b) :
    b ^ p - a ^ p ≤ p * b ^ (p - 1) * (b - a) := by
  rcases hab.lt_or_eq with h | h
  · have hb : 0 < b := ha.trans_lt h
    have hs : -1 ≤ a / b - 1 := by
      have : 0 ≤ a / b := div_nonneg ha hb.le
      linarith
    have hB := one_add_mul_self_le_rpow_one_add hs hp
    rw [add_sub_cancel, Real.div_rpow ha hb.le] at hB
    have hbp : 0 < b ^ p := Real.rpow_pos_of_pos hb p
    rw [le_div_iff₀ hbp] at hB
    have e : b ^ (p - 1) = b ^ p / b := Real.rpow_sub_one hb.ne' p
    have e2 : (1 + p * (a / b - 1)) * b ^ p = b ^ p - p * b ^ (p - 1) * (b - a) := by
      rw [e]
      field_simp
      ring
    linarith
  · subst h
    simp

/-- For `0 < μ` and any real `α`, `μ ^ (3 / (2 * α)) = (μ ^ (1 / (2 * α))) ^ 3`. -/
theorem rpow_three_div_eq_rpow_cube {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ ^ (3 / (2 * α)) = (μ ^ (1 / (2 * α))) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hμ.le]
  congr 1
  push_cast
  ring

/-- For `0 ≤ k` and `1 < α < 3 / 2`, `k ^ (2 * α) ≤ 1 + k ^ 3`. For `k ≤ 1` the left side is at most
`1`, and for `k ≥ 1` it is at most `k ^ 3` because `2 * α ≤ 3`. -/
theorem rpow_two_mul_le_one_add_cube {k α : ℝ} (hk : 0 ≤ k) (hα : 1 < α) (hα2 : α < 3 / 2) :
    k ^ (2 * α) ≤ 1 + k ^ 3 := by
  rcases le_total k 1 with h | h
  · have := Real.rpow_le_one hk h (by linarith : (0 : ℝ) ≤ 2 * α)
    have : 0 ≤ k ^ 3 := by positivity
    linarith
  · have h3 : k ^ (2 * α) ≤ k ^ ((3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (by push_cast; linarith)
    rw [Real.rpow_natCast] at h3
    linarith

/-- For real numbers with `r > 0`, `0 ≤ s ≤ 1`, `c ≥ 1` and `s ≤ c / (1 + r)`,
`s ^ 2 / r ≤ c ^ 2 * min r⁻¹ (r ^ (-3))`, where `r ^ (-3)` is a real power. The bound by
`c ^ 2 * r⁻¹` uses `s ≤ 1 ≤ c`, and the bound by `c ^ 2 * r ^ (-3)` uses `s ≤ c / r`. -/
theorem sq_div_le_sq_mul_min_inv {s r c : ℝ} (hr : 0 < r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 1 ≤ c)
    (hsc : s ≤ c / (1 + r)) :
    s ^ 2 / r ≤ c ^ 2 * min (r⁻¹) (r ^ (-(3 : ℝ))) := by
  have e3 : r ^ (-(3 : ℝ)) = (r ^ 3)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_cast
  rw [e3, mul_min_of_nonneg _ _ (sq_nonneg c)]
  have hsr : s ≤ c / r := hsc.trans (by gcongr; linarith)
  refine le_min ?_ ?_
  · rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (inv_nonneg.2 hr.le)
  · have h2 : s ^ 2 ≤ c ^ 2 / r ^ 2 := by
      rw [← div_pow]
      exact pow_le_pow_left₀ hs0 hsr 2
    calc s ^ 2 / r ≤ c ^ 2 / r ^ 2 / r := by gcongr
      _ = c ^ 2 * (r ^ 3)⁻¹ := by
        field_simp

/-- Let `0 ≤ x`, `0 ≤ t` and `t ≤ B * (1 + x) ^ (-a)` with a real exponent `a`. Then
`t ^ 2 ≤ B ^ 2 * (1 + x) ^ (-(2 * a))`. -/
theorem sq_le_of_le_mul_rpow_neg {t B a x : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t)
    (h : t ≤ B * (1 + x) ^ (-a)) :
    t ^ 2 ≤ B ^ 2 * (1 + x) ^ (-(2 * a)) := by
  have hp : 0 < 1 + x := by linarith
  have h1 : t ^ 2 ≤ (B * (1 + x) ^ (-a)) ^ 2 := pow_le_pow_left₀ ht h 2
  have e : (B * (1 + x) ^ (-a)) ^ 2 = B ^ 2 * (1 + x) ^ (-(2 * a)) := by
    rw [mul_pow, ← Real.rpow_natCast ((1 + x) ^ (-a)), ← Real.rpow_mul hp.le]
    congr 2
    push_cast
    ring
  linarith

/-- For `0 ≤ k` and `1 < α`, `k ^ 2 ≤ 1 + k ^ (2 * α)`. -/
theorem sq_le_one_add_rpow {k α : ℝ} (hk : 0 ≤ k) (hα : 1 < α) :
    k ^ 2 ≤ 1 + k ^ (2 * α) := by
  rcases le_total k 1 with h | h
  · have := pow_le_one₀ (n := 2) hk h
    have : 0 ≤ k ^ (2 * α) := Real.rpow_nonneg hk _
    linarith
  · have h3 : k ^ ((2 : ℕ) : ℝ) ≤ k ^ (2 * α) :=
      Real.rpow_le_rpow_of_exponent_le h (by push_cast; linarith)
    rw [Real.rpow_natCast] at h3
    linarith

/-- For `1 ≤ α` and `0 ≤ t`, `t ^ 2 ≤ t ^ (2 * α) + 1`. -/
theorem sq_le_rpow_add_one {α : ℝ} (hα : 1 ≤ α) {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 ≤ t ^ (2 * α) + 1 := by
  rcases le_total t 1 with h | h
  · have h1 : t ^ 2 ≤ 1 := by nlinarith
    have h2 : 0 ≤ t ^ (2 * α) := Real.rpow_nonneg ht _
    linarith
  · have h1 : t ^ (2 : ℝ) ≤ t ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    rw [Real.rpow_two] at h1
    linarith

/-- For a real `y > 0`, `y ^ 2 * (y⁻¹ ^ 2) ^ (6 / 5 : ℝ) = y ^ (-2 / 5 : ℝ)`. -/
theorem sq_mul_inv_sq_rpow_eq_rpow {y : ℝ} (hy : 0 < y) :
    y ^ 2 * (y⁻¹ ^ 2) ^ (6 / 5 : ℝ) = y ^ (-2 / 5 : ℝ) := by
  have h1 : y⁻¹ ^ 2 = y ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hy.le, inv_pow]; norm_cast
  rw [h1, ← Real.rpow_mul hy.le, ← Real.rpow_two, ← Real.rpow_add hy]
  norm_num

/-- For `0 < r`, `0 ≤ p` and any real `A`,
`r ^ 2 * (A * (1 + r) ^ (-p)) ^ 2 ≤ A ^ 2 * r ^ (2 - 2 * p)`. The proof uses
`(1 + r) ^ (-p) ≤ r ^ (-p)` and `r ^ 2 * (r ^ (-p)) ^ 2 = r ^ (2 - 2 * p)`. -/
theorem sq_mul_mul_rpow_neg_sq_le {A p r : ℝ} (hr : 0 < r) (hp : 0 ≤ p) :
    r ^ 2 * (A * (1 + r) ^ (-p)) ^ 2 ≤ A ^ 2 * r ^ (2 - 2 * p) := by
  have hle : (1 + r) ^ (-p) ≤ r ^ (-p) := Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
  have h0 : 0 ≤ (1 + r) ^ (-p) := Real.rpow_nonneg (by linarith) _
  have hsq : ((1 + r) ^ (-p)) ^ 2 ≤ (r ^ (-p)) ^ 2 := pow_le_pow_left₀ h0 hle 2
  have hid : r ^ 2 * (r ^ (-p)) ^ 2 = r ^ (2 - 2 * p) := by
    rw [← Real.rpow_natCast (r ^ (-p)) 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r 2,
      ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  calc r ^ 2 * (A * (1 + r) ^ (-p)) ^ 2 = A ^ 2 * (r ^ 2 * ((1 + r) ^ (-p)) ^ 2) := by ring
    _ ≤ A ^ 2 * (r ^ 2 * (r ^ (-p)) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) (sq_nonneg A)
    _ = _ := by rw [hid]

/-- For `0 < a`, `0 ≤ γ` and `0 < y`, `y ^ 2 * (1 + y / a) ^ (-γ) ≤ a ^ γ * y ^ (2 - γ)`. The proof
bounds `(1 + y / a) ^ (-γ)` by `(y / a) ^ (-γ) = a ^ γ * y ^ (-γ)`. -/
theorem sq_mul_one_add_div_rpow_le {a γ y : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hy0 : 0 < y) :
    y ^ 2 * (1 + y / a) ^ (-γ) ≤ a ^ γ * y ^ (2 - γ) := by
  have h1 : (1 + y / a) ^ (-γ) ≤ (y / a) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hy0 ha) (by linarith) (by linarith)
  have h2 : (y / a) ^ (-γ) = a ^ γ * y ^ (-γ) := by
    rw [Real.div_rpow hy0.le ha.le, Real.rpow_neg ha.le, div_inv_eq_mul, mul_comm]
  have h3 : y ^ (2 - γ) = y ^ 2 * y ^ (-γ) := by
    rw [sub_eq_add_neg, Real.rpow_add hy0, Real.rpow_two]
  calc y ^ 2 * (1 + y / a) ^ (-γ) ≤ y ^ 2 * (a ^ γ * y ^ (-γ)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2.le) (sq_nonneg y)
    _ = a ^ γ * y ^ (2 - γ) := by rw [h3]; ring

/-- For real `y ≥ 0`, `y ^ 2 * (1 + y) ^ (-3) ≤ 1`, where the second factor is a real power. -/
theorem sq_mul_rpow_neg_three_le_one {y : ℝ} (hy : 0 ≤ y) : y ^ 2 * (1 + y) ^ (-(3 : ℝ)) ≤ 1 := by
  have h1 : 0 < 1 + y := by linarith
  rw [Real.rpow_neg h1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith [sq_nonneg y, mul_nonneg hy (sq_nonneg y)]

/-- Let `0 ≤ x`, `0 ≤ t` and `t ≤ C / (1 + x) ^ γ` with a real exponent `γ`. Then
`x ^ 2 * t ^ 2 ≤ C ^ 2 * (1 + x) ^ (-(2 * γ - 2))`. The proof squares the hypothesis, uses
`x ^ 2 ≤ (1 + x) ^ 2` and combines the powers of `1 + x`. -/
theorem sq_mul_sq_le_sq_mul_rpow {x γ C t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (h : t ≤ C / (1 + x) ^ γ) :
    x ^ 2 * t ^ 2 ≤ C ^ 2 * (1 + x) ^ (-(2 * γ - 2)) := by
  have hp : 0 < 1 + x := by linarith
  have h1 : t ^ 2 ≤ (C / (1 + x) ^ γ) ^ 2 := pow_le_pow_left₀ ht h 2
  have h2 : x ^ 2 ≤ (1 + x) ^ 2 := pow_le_pow_left₀ hx (by linarith) 2
  have e : (1 + x) ^ 2 * (C / (1 + x) ^ γ) ^ 2 = C ^ 2 * (1 + x) ^ (-(2 * γ - 2)) := by
    rw [div_pow, ← Real.rpow_natCast ((1 + x) ^ γ), ← Real.rpow_mul hp.le, Real.rpow_neg hp.le,
      Real.rpow_sub hp, ← Real.rpow_natCast (1 + x) 2]
    push_cast
    field_simp
  calc x ^ 2 * t ^ 2 ≤ (1 + x) ^ 2 * (C / (1 + x) ^ γ) ^ 2 :=
        mul_le_mul h2 h1 (sq_nonneg _) (sq_nonneg _)
    _ = _ := e

/-- For real numbers, if `0 ≤ E` and `S ≤ E`, then `A ^ 2 * K ^ 2 * S ≤ (A * √E * K) ^ 2`. The right
side equals `A ^ 2 * K ^ 2 * E`. -/
theorem sq_mul_sq_mul_le_sqrt_sq {A K S E : ℝ} (hE0 : 0 ≤ E) (he : S ≤ E) :
    A ^ 2 * K ^ 2 * S ≤ (A * Real.sqrt E * K) ^ 2 := by
  rw [mul_pow, mul_pow, Real.sq_sqrt hE0]
  have h0 : 0 ≤ A ^ 2 * K ^ 2 := by positivity
  exact (mul_le_mul_of_nonneg_left he h0).trans_eq (by ring)

/-- For real `a`, `(a ^ 2) ^ (3 : ℝ) = a ^ 6`, where the outer power on the left is the real power.
-/
theorem sq_rpow_three (a : ℝ) : (a ^ 2) ^ (3 : ℝ) = a ^ 6 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]

/-- For real `a`, `(a ^ 2) ^ ((3 : ℝ) / 2) = |a| ^ 3`, where the outer power on the left is the real
power. -/
theorem sq_rpow_three_halves (a : ℝ) : (a ^ 2) ^ ((3 : ℝ) / 2) = |a| ^ 3 := by
  have h : a ^ 2 = |a| ^ (2 : ℝ) := by rw [Real.rpow_two, sq_abs]
  rw [h, ← Real.rpow_mul (abs_nonneg a), show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- Let `0 ≤ X` and `0 ≤ Y` be real numbers. If `s ≤ (t * X + Y / t) / 2` for every `t > 0`, then
`s ≤ √X * √Y`. The proof takes `t = √Y / √X` when `X` and `Y` are positive, and argues by
contradiction with `t = (Y + 1) / s` when `X = 0` and with `t = s / X` when `Y = 0`. -/
theorem sq_sqrt_bound {s X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : ∀ t : ℝ, 0 < t → s ≤ (t * X + Y / t) / 2) : s ≤ Real.sqrt X * Real.sqrt Y := by
  rcases eq_or_lt_of_le hX with hX0 | hXp
  · rw [← hX0, Real.sqrt_zero, zero_mul]
    by_contra hs
    push Not at hs
    have h1 := h ((Y + 1) / s) (by positivity)
    rw [← hX0, mul_zero, zero_add, div_div_eq_mul_div] at h1
    have h2 : Y * s / (Y + 1) / 2 < s := by
      rw [div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases eq_or_lt_of_le hY with hY0 | hYp
  · rw [← hY0, Real.sqrt_zero, mul_zero]
    by_contra hs
    push Not at hs
    have h1 := h (s / X) (by positivity)
    rw [← hY0, zero_div, add_zero, div_mul_cancel₀ _ hXp.ne'] at h1
    linarith
  · have ha := Real.sqrt_pos.2 hXp
    have hb := Real.sqrt_pos.2 hYp
    set a := Real.sqrt X with ha_def
    set c := Real.sqrt Y with hc_def
    have hXa : X = a ^ 2 := (Real.sq_sqrt hX).symm
    have hYc : Y = c ^ 2 := (Real.sq_sqrt hY).symm
    have h1 := h (c / a) (div_pos hb ha)
    rw [hXa, hYc] at h1
    have e : (c / a * a ^ 2 + c ^ 2 / (c / a)) / 2 = a * c := by
      field_simp
      ring
    linarith

/-- For `1 ≤ α` and `0 ≤ s`, `s ^ 2 - 1 ≤ s ^ (2 * α)`. -/
theorem sq_sub_one_le_rpow {α : ℝ} (hα : 1 ≤ α) {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 - 1 ≤ s ^ (2 * α) := by
  rcases le_total 1 s with h | h
  · have h1 : s ^ (2 : ℝ) ≤ s ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    rw [Real.rpow_two] at h1
    linarith
  · have h1 : s ^ 2 ≤ 1 := by nlinarith
    have h2 : 0 ≤ s ^ (2 * α) := Real.rpow_nonneg hs _
    linarith

/-- If `μ = 1` and `√(E + μ ^ 2 * S) ≤ a + r + c * x`, then `√(E + S) ≤ (a + r) + c * x`. It is the
hypothesis with `μ` replaced by `1`. -/
theorem sqrt_add_le_of_eq_one (E S a r c x μ : ℝ) (hμ : μ = 1)
    (h : Real.sqrt (E + μ ^ 2 * S) ≤ a + r + c * x) : Real.sqrt (E + S) ≤ (a + r) + c * x := by
  subst hμ
  simpa using h

/-- For real numbers `0 ≤ w` and `0 < c`, `√(w / c) * √c = √w`. -/
theorem sqrt_div_mul_sqrt {w c : ℝ} (hw : 0 ≤ w) (hc : 0 < c) :
    Real.sqrt (w / c) * Real.sqrt c = Real.sqrt w := by
  rw [← Real.sqrt_mul (div_nonneg hw hc.le), div_mul_cancel₀ _ hc.ne']

/-- For `ε > 0` and `T ≥ 0`, `√(T / (1 + (T / ε ^ 2 + 1))) ≤ ε`. Indeed the quotient under the root
is at most `ε ^ 2`. -/
theorem sqrt_div_one_add_div_sq_le {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    Real.sqrt (T / (1 + (T / ε ^ 2 + 1))) ≤ ε := by
  have hpos : 0 < 1 + (T / ε ^ 2 + 1) := by positivity
  have h1 : T / (1 + (T / ε ^ 2 + 1)) ≤ ε ^ 2 := by
    rw [div_le_iff₀ hpos]
    have h3 : ε ^ 2 * (T / ε ^ 2) = T := by field_simp
    nlinarith [sq_nonneg ε]
  exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq hε.le)

/-- For positive reals `a` and `b`, `0 < √(b / a)`. -/
theorem sqrt_div_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < Real.sqrt (b / a) :=
  Real.sqrt_pos.mpr (div_pos hb ha)

/-- For every real `r`, `√(Real.exp (-r)) = Real.exp (-(r / 2))`. -/
theorem sqrt_exp_neg (r : ℝ) : Real.sqrt (Real.exp (-r)) = Real.exp (-(r / 2)) := by
  rw [show Real.exp (-r) = Real.exp (-(r / 2)) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf]
  exact Real.sqrt_sq (Real.exp_pos _).le

/-- For real `α > 0`, `K ≥ 0`, `τ > 0` and `s ≥ 0`,
`√((K * τ ^ (-(1 / (2 * α))) * s) * (K * τ ^ (-(1 / α)) * s)) = K * τ ^ (-(3 / (4 * α))) *
s`. The product under the root is the square of the right side, since `(τ ^ (-(3 / (4 * α)))) ^ 2 =
τ ^ (-(1 / (2 * α))) * τ ^ (-(1 / α))`. -/
theorem sqrt_fracPhi_product {α K τ s : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hτ : 0 < τ) (hs : 0 ≤ s) :
    Real.sqrt ((K * τ ^ (-(1 / (2 * α))) * s) * (K * τ ^ (-(1 / α)) * s)) =
      K * τ ^ (-(3 / (4 * α))) * s := by
  have e : (τ ^ (-(3 / (4 * α)))) ^ 2 = τ ^ (-(1 / (2 * α))) * τ ^ (-(1 / α)) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
    congr 1
    field_simp
    ring
  rw [show (K * τ ^ (-(1 / (2 * α))) * s) * (K * τ ^ (-(1 / α)) * s) =
      (K * τ ^ (-(3 / (4 * α))) * s) ^ 2 by rw [mul_pow, mul_pow, e]; ring]
  exact Real.sqrt_sq (by positivity)

/-- If `0 ≤ A`, `0 ≤ D` and `E ≤ A ^ 2 + D`, then `√E ≤ A + √D`, because `A ^ 2 + D ≤ (A + √D) ^ 2`.
-/
theorem sqrt_le_add_sqrt_of_le {A D E : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hE : E ≤ A ^ 2 + D) :
    Real.sqrt E ≤ A + Real.sqrt D := by
  have hs : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
  calc Real.sqrt E ≤ Real.sqrt ((A + Real.sqrt D) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hA hs])
    _ = A + Real.sqrt D := Real.sqrt_sq (by positivity)

/-- If `b ≤ t ^ 2 * s`, `0 ≤ t` and `√s ≤ cn`, then `√b ≤ t * cn`. -/
theorem sqrt_le_mul_of_le_sq_mul {b t s cn : ℝ} (hb : b ≤ t ^ 2 * s) (ht : 0 ≤ t)
    (hs : Real.sqrt s ≤ cn) : Real.sqrt b ≤ t * cn :=
  calc Real.sqrt b ≤ Real.sqrt (t ^ 2 * s) := Real.sqrt_le_sqrt hb
    _ = t * Real.sqrt s := by rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
    _ ≤ t * cn := mul_le_mul_of_nonneg_left hs ht

/-- For nonnegative real numbers `p`, `q`, `r`, `t`, `√p * √r + √q * √t ≤ √(p + q) * √(r + t)`. The
proof squares both sides and uses `0 ≤ (√p * √t - √q * √r) ^ 2`. -/
theorem sqrt_mul_sqrt_add_le_sqrt_add {p q r t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (ht : 0 ≤ t) :
    Real.sqrt p * Real.sqrt r + Real.sqrt q * Real.sqrt t ≤ Real.sqrt (p + q) *
        Real.sqrt (r + t) := by
  rw [← Real.sqrt_mul (add_nonneg hp hq)]
  apply Real.le_sqrt_of_sq_le
  have h1 := Real.sq_sqrt hp
  have h2 := Real.sq_sqrt hq
  have h3 := Real.sq_sqrt hr
  have h4 := Real.sq_sqrt ht
  nlinarith [sq_nonneg (Real.sqrt p * Real.sqrt t - Real.sqrt q * Real.sqrt r),
    Real.sqrt_nonneg p, Real.sqrt_nonneg q, Real.sqrt_nonneg r, Real.sqrt_nonneg t]

/-- For real numbers `0 ≤ a`, `0 ≤ c` and `t > 0`, `√a * √c ≤ (t * a + c / t) / 2`. This is the
inequality of arithmetic and geometric means with a weight `t`; the proof expands
`0 ≤ (t * √a - √c) ^ 2 / t`. -/
theorem sqrt_mul_sqrt_le_of_pos {a c t : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (ht : 0 < t) :
    Real.sqrt a * Real.sqrt c ≤ (t * a + c / t) / 2 := by
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hc
  set x := Real.sqrt a
  set y := Real.sqrt c
  have key : 0 ≤ (t * x - y) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have eq : (t * x - y) ^ 2 / t = t * x ^ 2 + y ^ 2 / t - 2 * (x * y) := by
    field_simp
    ring
  rw [← hx, ← hy]
  linarith

/-- For `0 < ℓ` and any real `α`, `√(ℓ ^ (1 / α)) = ℓ ^ (1 / (2 * α))`. -/
theorem sqrt_rpow_one_div_eq_rpow {α : ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Real.sqrt (ℓ ^ (1 / α)) = ℓ ^ (1 / (2 * α)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hℓ.le]
  congr 1
  ring

/-- For nonnegative reals `a b c a₁ b₁ c₁ a₂ b₂ c₂` with `a ≤ a₁ + a₂`, `b ≤ b₁ + b₂` and
`c ≤ c₁ + c₂`, `√(a ^ 2 + b ^ 2 + c ^ 2) ≤ √(a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) + √(a₂ ^ 2 + b₂ ^ 2 + c₂ ^
2)`. It is the triangle inequality for the Euclidean norm on three coordinates. -/
theorem sqrt_sum_three_sq_le_of_le {a b c a₁ b₁ c₁ a₂ b₂ c₂ : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hc0 : 0 ≤ c)
    (ha10 : 0 ≤ a₁) (hb10 : 0 ≤ b₁) (hc10 : 0 ≤ c₁) (ha20 : 0 ≤ a₂) (hb20 : 0 ≤ b₂) (hc20 : 0 ≤ c₂)
    (ha : a ≤ a₁ + a₂) (hb : b ≤ b₁ + b₂) (hc : c ≤ c₁ + c₂) :
    Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) ≤
      Real.sqrt (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) + Real.sqrt (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) := by
  have ha' : |a| ≤ |a₁| + |a₂| := by
    rw [abs_of_nonneg ha0, abs_of_nonneg ha10, abs_of_nonneg ha20]; exact ha
  have hb' : |b| ≤ |b₁| + |b₂| := by
    rw [abs_of_nonneg hb0, abs_of_nonneg hb10, abs_of_nonneg hb20]; exact hb
  have hc' : |c| ≤ |c₁| + |c₂| := by
    rw [abs_of_nonneg hc0, abs_of_nonneg hc10, abs_of_nonneg hc20]; exact hc
  have h := sqrt_sum_sq_le ![a₁, b₁, c₁] ![a₂, b₂, c₂] ![a, b, c] (fun i ↦ by
    fin_cases i
    exacts [ha', hb', hc'])
  simpa [Fin.sum_univ_three, add_assoc] using h

/-- For `0 < w₀` and real `z`, `(2 / √3 / w₀ * z) ^ 2 * w₀ * w₀ = 4 / 3 * z ^ 2`. -/
theorem two_div_sqrt_three_div_mul_sq {w₀ z : ℝ} (hw : 0 < w₀) :
    (2 / Real.sqrt 3 / w₀ * z) ^ 2 * w₀ * w₀ = 4 / 3 * z ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [mul_pow, div_pow, div_pow, h3]
  field_simp
  ring

/-- For `0 < w₀` and real `n`, `(2 / √3 / √w₀ * n) ^ 2 * w₀ = 4 / 3 * n ^ 2`. -/
theorem two_div_sqrt_three_div_sqrt_sq {w₀ : ℝ} (hw : 0 < w₀) (n : ℝ) :
    (2 / Real.sqrt 3 / Real.sqrt w₀ * n) ^ 2 * w₀ = 4 / 3 * n ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt w₀ ^ 2 = w₀ := Real.sq_sqrt hw.le
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsp : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw
  rw [mul_pow, div_pow, div_pow, h3, hs]
  field_simp
  ring

/-- For a real `l > 0`, `2 * π ^ 2 / √((l * (4 * π ^ 2)) * (l⁻¹ * (16 * π ^ 4))) = 1 / (4 * π)`. The
product under the root equals `(8 * π ^ 3) ^ 2`. -/
theorem two_mul_pi_sq_div_sqrt_eq (l : ℝ) (hl : 0 < l) :
    2 * π ^ 2 / Real.sqrt ((l * (4 * π ^ 2)) * (l⁻¹ * (16 * π ^ 4))) = 1 / (4 * π) := by
  have hpi : 0 < π := Real.pi_pos
  have e : (l * (4 * π ^ 2)) * (l⁻¹ * (16 * π ^ 4)) = (8 * π ^ 3) ^ 2 := by
    field_simp
    ring
  rw [e, Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-- For `0 < α` and `0 < τ`, `(2 * τ ^ (-α⁻¹)) ^ (3 / 4 : ℝ) ≤ 2 * τ ^ (-(3 / (4 * α)))`. The left
side equals `2 ^ (3 / 4 : ℝ) * τ ^ (-(3 / (4 * α)))`, and `2 ^ (3 / 4 : ℝ) ≤ 2`. -/
theorem two_mul_rpow_neg_inv_rpow_le {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) :
    (2 * τ ^ (-α⁻¹)) ^ (3 / 4 : ℝ) ≤ 2 * τ ^ (-(3 / (4 * α))) := by
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hτ.le _), ← Real.rpow_mul hτ.le,
    show -α⁻¹ * (3 / 4 : ℝ) = -(3 / (4 * α)) by field_simp]
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (3 / 4 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hτ.le _)

/-- For real `a`, `N ≥ 0`, `ρ > 0` and an integer `l` with `2 ^ (l : ℝ) * ρ ≤ 1`, one has
`2 ^ (a * l) ≤ 2 ^ N * (2 ^ (a * l) * (1 + 2 ^ (l : ℝ) * ρ) ^ (-N))`, all powers being real powers.
The proof uses `(1 + 2 ^ (l : ℝ) * ρ) ^ N ≤ 2 ^ N`. -/
theorem two_rpow_le_of_mul_le_one (a N ρ : ℝ) (l : ℤ) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (h : (2 : ℝ) ^ (l : ℝ) * ρ ≤ 1) :
    (2:ℝ) ^ (a * l) ≤ 2 ^ N * ((2:ℝ) ^ (a * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-N)) := by
  have ht : 0 < (2:ℝ) ^ (l:ℝ) := by positivity
  have h1 : 0 < 1 + (2:ℝ) ^ (l:ℝ) * ρ := by positivity
  have hpos : 0 < (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ N := Real.rpow_pos_of_pos h1 N
  have hle : (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ N ≤ 2 ^ N :=
    Real.rpow_le_rpow h1.le (by linarith) hN
  rw [Real.rpow_neg h1.le]
  have h2e : 0 < (2:ℝ) ^ (a * l) := by positivity
  have heq : 2 ^ N * (2 ^ (a * (l:ℝ)) * ((1 + 2 ^ (l:ℝ) * ρ) ^ N)⁻¹)
      = 2 ^ (a * (l:ℝ)) * (2 ^ N / (1 + 2 ^ (l:ℝ) * ρ) ^ N) := by ring
  rw [heq]
  have hq : 1 ≤ (2:ℝ) ^ N / (1 + 2 ^ (l:ℝ) * ρ) ^ N := by
    rw [le_div_iff₀ hpos]; linarith
  nlinarith

/-- For real `e`, `N ≥ 0`, `ρ > 0` and an integer `l` with `1 < 2 ^ (l : ℝ) * ρ`, one has
`2 ^ (e * l) ≤ 2 ^ N * ρ ^ N * (2 ^ ((e + N) * l) * (1 + 2 ^ (l : ℝ) * ρ) ^ (-N))`, all powers being
real powers. The proof writes `2 ^ ((e + N) * l)` as `2 ^ (e * l) * (2 ^ (l : ℝ)) ^ N` and uses
`1 + 2 ^ (l : ℝ) * ρ ≤ 2 * (2 ^ (l : ℝ) * ρ)`. -/
theorem two_rpow_le_of_one_lt_mul (e N ρ : ℝ) (l : ℤ) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (h : 1 < (2 : ℝ) ^ (l : ℝ) * ρ) :
    (2:ℝ) ^ (e * l) ≤
      2 ^ N * ρ ^ N * ((2:ℝ) ^ ((e + N) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-N)) := by
  have ht : 0 < (2:ℝ) ^ (l:ℝ) := by positivity
  have h1 : 0 < 1 + (2:ℝ) ^ (l:ℝ) * ρ := by positivity
  have hsplit : (2:ℝ) ^ ((e + N) * l) = 2 ^ (e * l) * ((2:ℝ) ^ (l:ℝ)) ^ N := by
    rw [add_mul, Real.rpow_add (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm N]
  rw [hsplit, Real.rpow_neg h1.le]
  have hle : (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ N ≤ (2 * ((2:ℝ) ^ (l:ℝ) * ρ)) ^ N :=
    Real.rpow_le_rpow h1.le (by linarith) hN
  have hpos : 0 < (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ N := Real.rpow_pos_of_pos h1 N
  rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow ht.le hρ.le] at hle
  have h2e : 0 < (2:ℝ) ^ (e * l) := by positivity
  have heq : 2 ^ N * ρ ^ N * (2 ^ (e * (l:ℝ)) * ((2:ℝ) ^ (l:ℝ)) ^ N * ((1 + 2 ^ (l:ℝ) * ρ) ^ N)⁻¹)
      = 2 ^ (e * (l:ℝ)) * ((2 ^ N * (((2:ℝ) ^ (l:ℝ)) ^ N * ρ ^ N)) / (1 + 2 ^ (l:ℝ) * ρ) ^ N) := by
    ring
  rw [heq]
  have hq : 1 ≤ (2 ^ N * (((2:ℝ) ^ (l:ℝ)) ^ N * ρ ^ N)) / (1 + 2 ^ (l:ℝ) * ρ) ^ N := by
    rw [le_div_iff₀ hpos]; linarith
  nlinarith

/-- For an integer `l`, the real power `(2 : ℝ) ^ (-(l : ℝ))` equals `((2 : ℝ) ^ l)⁻¹`, the inverse
of the integer power. -/
theorem two_rpow_neg_intCast_eq_inv_zpow (l : ℤ) : (2 : ℝ) ^ (-(l : ℝ)) = ((2 : ℝ) ^ l)⁻¹ := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_intCast]

/-- For real `τ > 0`, `r` with `|r - τ| ≤ τ / 2` and `x ≥ 0`,
`|Real.exp (-(r * x)) - Real.exp (-(τ * x)) + (r - τ) * (x * Real.exp (-(τ * x)))| ≤ 16 / τ ^ 2 *
(r - τ) ^ 2`. This bounds the error of the first order expansion of `r ↦ Real.exp (-(r *
x))` at `τ`, uniformly in `x`. The proof factors out `Real.exp (-(τ * x))`, applies
`|Real.exp y - 1 - y| ≤ y ^ 2 * Real.exp |y|` with `y = -((r - τ) * x)`, and uses
`x ^ 2 * Real.exp (-(τ / 2 * x)) ≤ 16 / τ ^ 2`. -/
theorem abs_exp_neg_mul_sub_add_le {τ r x : ℝ} (hτ : 0 < τ) (hr : |r - τ| ≤ τ / 2) (hx : 0 ≤ x) :
    |Real.exp (-(r * x)) - Real.exp (-(τ * x)) + (r - τ) * (x * Real.exp (-(τ * x)))| ≤
      16 / τ ^ 2 * (r - τ) ^ 2 := by
  set k := r - τ with hk
  have e : Real.exp (-(r * x)) - Real.exp (-(τ * x)) + k * (x * Real.exp (-(τ * x))) =
      Real.exp (-(τ * x)) * (Real.exp (-(k * x)) - 1 - (-(k * x))) := by
    rw [show -(r * x) = -(τ * x) + -(k * x) by rw [hk]; ring, Real.exp_add]
    ring
  rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_exp_sub_one_sub_le_mul (-(k * x))
  rw [abs_neg, abs_mul, abs_of_nonneg hx] at h1
  have h2 : Real.exp (-(τ * x)) * Real.exp (|k| * x) ≤ Real.exp (-(τ / 2 * x)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have h3 : x ^ 2 * Real.exp (-(τ / 2 * x)) ≤ 16 / τ ^ 2 := by
    have hm := mul_exp_neg_le_one (τ / 4 * x)
    have hn : 0 ≤ τ / 4 * x * Real.exp (-(τ / 4 * x)) := by positivity
    have e2 : x ^ 2 * Real.exp (-(τ / 2 * x)) =
        (4 / τ) ^ 2 * (τ / 4 * x * Real.exp (-(τ / 4 * x))) ^ 2 := by
      rw [show -(τ / 2 * x) = -(τ / 4 * x) + -(τ / 4 * x) by ring, Real.exp_add]
      field_simp
    rw [e2]
    calc (4 / τ) ^ 2 * (τ / 4 * x * Real.exp (-(τ / 4 * x))) ^ 2 ≤ (4 / τ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hn hm) (by positivity)
      _ = 16 / τ ^ 2 := by rw [div_pow]; norm_num
  calc Real.exp (-(τ * x)) * |Real.exp (-(k * x)) - 1 - -(k * x)| ≤
        Real.exp (-(τ * x)) * ((-(k * x)) ^ 2 * Real.exp (|k| * x)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = (k ^ 2 * x ^ 2) * (Real.exp (-(τ * x)) * Real.exp (|k| * x)) := by ring
    _ ≤ (k ^ 2 * x ^ 2) * Real.exp (-(τ / 2 * x)) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = k ^ 2 * (x ^ 2 * Real.exp (-(τ / 2 * x))) := by ring
    _ ≤ k ^ 2 * (16 / τ ^ 2) := mul_le_mul_of_nonneg_left h3 (sq_nonneg k)
    _ = 16 / τ ^ 2 * k ^ 2 := by ring

/-- Let `|a| ≤ A`, `0 ≤ A'`, `0 ≤ Nθ`, `0 ≤ NΔ`, `0 ≤ NC` be real numbers with `S ^ 2 ≤ Nθ * Nb`,
`Nb = a ^ 2 * NΔ + 2 * a * M + NC`, `M ^ 2 ≤ NΔ * NC` and `NC ≤ A' ^ 2 * Nω`. Then
`|S| ≤ (A * √NΔ + A' * √Nω) * √Nθ`. The proof shows `Nb ≤ (|a| * √NΔ + √NC) ^ 2` from
`|M| ≤ √NΔ * √NC`, takes square roots, and uses `√NC ≤ A' * √Nω`. -/
theorem abs_le_mul_sqrt_add_mul_sqrt {a A A' Nθ NΔ Nω NC M S Nb : ℝ} (ha : |a| ≤ A) (hA' : 0 ≤ A')
    (hθ0 : 0 ≤ Nθ) (hΔ0 : 0 ≤ NΔ) (hC0 : 0 ≤ NC)
    (h1 : S ^ 2 ≤ Nθ * Nb) (hNb : Nb = a ^ 2 * NΔ + 2 * a * M + NC) (h2 : M ^ 2 ≤ NΔ * NC)
    (hNC : NC ≤ A' ^ 2 * Nω) :
    |S| ≤ (A * Real.sqrt NΔ + A' * Real.sqrt Nω) * Real.sqrt Nθ := by
  have hsC : Real.sqrt NC ≤ A' * Real.sqrt Nω := by
    calc Real.sqrt NC ≤ Real.sqrt (A' ^ 2 * Nω) := Real.sqrt_le_sqrt hNC
      _ = A' * Real.sqrt Nω := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA']
  have hMabs : |M| ≤ Real.sqrt NΔ * Real.sqrt NC := abs_le_sqrt_mul_sqrt h2 hΔ0
  have hsΔ := Real.sq_sqrt hΔ0
  have hsCsq := Real.sq_sqrt hC0
  have hsΔ0 := Real.sqrt_nonneg NΔ
  have hsC0 := Real.sqrt_nonneg NC
  have hsθ0 := Real.sqrt_nonneg Nθ
  have haM : a * M ≤ |a| * (Real.sqrt NΔ * Real.sqrt NC) := by
    calc a * M ≤ |a * M| := le_abs_self _
      _ = |a| * |M| := abs_mul _ _
      _ ≤ |a| * (Real.sqrt NΔ * Real.sqrt NC) := mul_le_mul_of_nonneg_left hMabs (abs_nonneg _)
  have hb : Nb ≤ (|a| * Real.sqrt NΔ + Real.sqrt NC) ^ 2 := by
    have e : (|a| * Real.sqrt NΔ + Real.sqrt NC) ^ 2
        = |a| ^ 2 * Real.sqrt NΔ ^ 2 + 2 * (|a| * (Real.sqrt NΔ * Real.sqrt NC)) +
            Real.sqrt NC ^ 2 := by ring
    rw [e, sq_abs, hsΔ, hsCsq, hNb]
    linarith
  have h3 : S ^ 2 ≤ Nθ * (|a| * Real.sqrt NΔ + Real.sqrt NC) ^ 2 :=
    h1.trans (mul_le_mul_of_nonneg_left hb hθ0)
  have h4 := abs_le_sqrt_mul_sqrt h3 hθ0
  rw [Real.sqrt_sq (by positivity)] at h4
  refine h4.trans ?_
  rw [mul_comm (Real.sqrt Nθ)]
  refine mul_le_mul_of_nonneg_right ?_ hsθ0
  have : |a| * Real.sqrt NΔ ≤ A * Real.sqrt NΔ := mul_le_mul_of_nonneg_right ha hsΔ0
  linarith

/-- For `1 ≤ p` and real numbers `a`, `b` with `0 ≤ a ≤ M` and `0 ≤ b ≤ M`,
`|a ^ p - b ^ p| ≤ p * M ^ (p - 1) * |a - b|`. The proof orders `a` and `b` and uses
`b ^ p - a ^ p ≤ p * b ^ (p - 1) * (b - a)` for `a ≤ b`. -/
theorem abs_rpow_sub_rpow_le {p a b M : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M)
    (hbM : b ≤ M) : |a ^ p - b ^ p| ≤ p * M ^ (p - 1) * |a - b| := by
  have hp0 : 0 ≤ p := by linarith
  rcases le_total a b with h | h
  · have h1 : a ^ p ≤ b ^ p := Real.rpow_le_rpow ha h hp0
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have h2 := rpow_sub_rpow_le_mul_sub hp ha h
    have h3 : b ^ (p - 1) ≤ M ^ (p - 1) := Real.rpow_le_rpow hb hbM (by linarith)
    have h4 : p * b ^ (p - 1) * (b - a) ≤ p * M ^ (p - 1) * (b - a) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left h3 hp0
    linarith
  · have h1 : b ^ p ≤ a ^ p := Real.rpow_le_rpow hb h hp0
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    have h2 := rpow_sub_rpow_le_mul_sub hp hb h
    have h3 : a ^ (p - 1) ≤ M ^ (p - 1) := Real.rpow_le_rpow ha haM (by linarith)
    have h4 : p * a ^ (p - 1) * (a - b) ≤ p * M ^ (p - 1) * (a - b) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left h3 hp0
    linarith

/-- For reals `0 ≤ a` and `0 < s` and a natural number `m ≤ 10`,
`(a + s) ^ m * Real.exp (-(a ^ 2) / (4 * s ^ 2)) ≤ 40 ^ 5 * s ^ m`. The proof multiplies by
`s ^ (10 - m)`, uses `s ≤ a + s` to reduce to the exponent `10`, and applies the bound
`(a + s) ^ 10 * Real.exp (-(a ^ 2) / (4 * s ^ 2)) ≤ 40 ^ 5 * s ^ 10`. -/
theorem add_pow_mul_gaussian_le (a s : ℝ) (ha : 0 ≤ a) (hs : 0 < s) (m : ℕ) (hm : m ≤ 10) :
    (a + s) ^ m * Real.exp (-(a ^ 2) / (4 * s ^ 2)) ≤ 40 ^ 5 * s ^ m := by
  have hle : (a + s) ^ m * s ^ (10 - m) ≤ (a + s) ^ 10 := by
    calc (a + s) ^ m * s ^ (10 - m) ≤ (a + s) ^ m * (a + s) ^ (10 - m) := by
          gcongr; linarith
      _ = (a + s) ^ 10 := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hE := (Real.exp_pos (-(a ^ 2) / (4 * s ^ 2))).le
  have key : (a + s) ^ m * Real.exp (-(a ^ 2) / (4 * s ^ 2)) * s ^ (10 - m) ≤
      40 ^ 5 * s ^ m * s ^ (10 - m) := by
    calc (a + s) ^ m * Real.exp (-(a ^ 2) / (4 * s ^ 2)) * s ^ (10 - m)
        = (a + s) ^ m * s ^ (10 - m) * Real.exp (-(a ^ 2) / (4 * s ^ 2)) := by ring
      _ ≤ (a + s) ^ 10 * Real.exp (-(a ^ 2) / (4 * s ^ 2)) := mul_le_mul_of_nonneg_right hle hE
      _ ≤ 40 ^ 5 * s ^ 10 := add_pow_ten_mul_gaussian_le a s hs
      _ = 40 ^ 5 * s ^ m * s ^ (10 - m) := by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  exact le_of_mul_le_mul_right key (pow_pos hs _)

/-- Let `0 < q`, `2 * α * q = 3`, `0 < τ` and `0 ≤ a`. Then
`a ^ 3 * Real.exp (-(τ * a ^ (2 * α))) ≤ q ^ q * τ ^ (-q)`. The proof applies
`s ^ q ≤ q ^ q * Real.exp s` to `s = τ * a ^ (2 * α)`, for which `s ^ q = τ ^ q * a ^ 3`. -/
theorem cube_mul_exp_neg_mul_rpow_le {α q τ a : ℝ} (hq : 0 < q) (h3 : 2 * α * q = 3) (hτ : 0 < τ)
    (ha : 0 ≤ a) :
    a ^ 3 * Real.exp (-(τ * a ^ (2 * α))) ≤ q ^ q * τ ^ (-q) := by
  have hs : 0 ≤ τ * a ^ (2 * α) := mul_nonneg hτ.le (Real.rpow_nonneg ha _)
  have key := rpow_le_rpow_self_mul_exp hs hq
  have hpow : (τ * a ^ (2 * α)) ^ q = τ ^ q * a ^ 3 := by
    rw [Real.mul_rpow hτ.le (Real.rpow_nonneg ha _), ← Real.rpow_mul ha, h3]
    congr 1
    exact_mod_cast Real.rpow_natCast a 3
  rw [hpow] at key
  have hτq : 0 < τ ^ q := Real.rpow_pos_of_pos hτ q
  have he : 0 < Real.exp (-(τ * a ^ (2 * α))) := Real.exp_pos _
  have hexp : Real.exp (τ * a ^ (2 * α)) * Real.exp (-(τ * a ^ (2 * α))) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.rpow_neg hτ.le, le_mul_inv_iff₀ hτq]
  calc a ^ 3 * Real.exp (-(τ * a ^ (2 * α))) * τ ^ q
      = (τ ^ q * a ^ 3) * Real.exp (-(τ * a ^ (2 * α))) := by ring
    _ ≤ (q ^ q * Real.exp (τ * a ^ (2 * α))) * Real.exp (-(τ * a ^ (2 * α))) :=
        mul_le_mul_of_nonneg_right key he.le
    _ = q ^ q := by rw [mul_assoc, hexp, mul_one]

/-- For `0 ≤ x`, `0 ≤ C` and a real exponent `γ`, `C / (1 + x) ^ (γ + 1) ≤ C / (1 + x) ^ γ`. -/
theorem div_one_add_rpow_add_one_le {x γ C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) :
    C / (1 + x) ^ (γ + 1) ≤ C / (1 + x) ^ γ :=
  div_le_div_of_nonneg_left hC (by positivity) (one_add_rpow_le_rpow_add_one hx)

/-- For `0 < μ` and any real `α`, `μ⁻¹ ^ (-(1 / (2 * α))) = μ ^ (1 / (2 * α))`. -/
theorem inv_rpow_neg_one_div_eq_rpow {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ⁻¹ ^ (-(1 / (2 * α))) = μ ^ (1 / (2 * α)) := by
  rw [Real.inv_rpow hμ.le, rpow_neg_one_div_eq_inv_rpow hμ, inv_inv]

/-- Let `a > 0`, `e1 < 0`, `e2 < 0`, `ρ > 0`, let `p1`, `p2` be real and `l` an integer, and put
`u = 2 ^ (l : ℝ) * ρ`. The quantity that equals `2 ^ (a * l)` if `u ≤ 1` and
`2 ^ (e1 * l) * ρ ^ p1 + 2 ^ (e2 * l) * ρ ^ p2` otherwise is at most
`2 ^ (a + 1) * (2 ^ (a * l) * (1 + u) ^ (-(a + 1))) + (2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1) * (2 ^
(1 * l) * (1 + u) ^ (-(1 - e1))) + (2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2) * (2 ^ (1 * l) * (1 + u) ^
(-(1 - e2)))`, all powers being real powers. The proof treats `u ≤ 1` and `1 <
u` separately, bounds each power of `2` on the left by one of the three terms, and drops the other
terms, which are nonnegative. -/
theorem ite_two_rpow_le_add_rpow_neg (a e1 e2 p1 p2 ρ : ℝ) (l : ℤ) (ha : 0 < a) (he1 : e1 < 0)
    (he2 : e2 < 0)
    (hρ : 0 < ρ) :
    (if (2:ℝ) ^ (l:ℝ) * ρ ≤ 1 then (2:ℝ) ^ (a * l)
        else (2:ℝ) ^ (e1 * l) * ρ ^ p1 + (2:ℝ) ^ (e2 * l) * ρ ^ p2)
      ≤ 2 ^ (a + 1) * ((2:ℝ) ^ (a * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(a + 1)))
        + (2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e1)))
        + (2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e2))) := by
  have ht : 0 < (2:ℝ) ^ (l:ℝ) := by positivity
  have h1 : 0 < 1 + (2:ℝ) ^ (l:ℝ) * ρ := by positivity
  have n1 : 0 ≤ 2 ^ (a + 1) * ((2:ℝ) ^ (a * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(a + 1))) := by
    positivity
  have n2 : 0 ≤ (2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e1))) := by positivity
  have n3 : 0 ≤ (2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e2))) := by positivity
  split_ifs with hl
  · have := two_rpow_le_of_mul_le_one a (a + 1) ρ l (by linarith) hρ hl
    linarith
  · push Not at hl
    have k2 := two_rpow_le_of_one_lt_mul e1 (1 - e1) ρ l (by linarith) hρ hl
    have k3 := two_rpow_le_of_one_lt_mul e2 (1 - e2) ρ l (by linarith) hρ hl
    rw [show e1 + (1 - e1) = 1 by ring] at k2
    rw [show e2 + (1 - e2) = 1 by ring] at k3
    have q2 := mul_le_mul_of_nonneg_right k2 (by positivity : (0:ℝ) ≤ ρ ^ p1)
    have q3 := mul_le_mul_of_nonneg_right k3 (by positivity : (0:ℝ) ≤ ρ ^ p2)
    have r2 : 2 ^ (1 - e1) * ρ ^ (1 - e1) *
        ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e1))) * ρ ^ p1
        = (2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e1))) := by ring
    have r3 : 2 ^ (1 - e2) * ρ ^ (1 - e2) *
        ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e2))) * ρ ^ p2
        = (2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e2))) := by ring
    rw [r2] at q2
    rw [r3] at q3
    linarith

/-- For real numbers with `0 ≤ k ≤ 3` and `0 ≤ s ≤ R`, all real `A` and `D` satisfy
`A ≤ (|A| * (1 + R) ^ 3 + |D| * 2 ^ 3) * (1 + s) ^ (-k)`, with real powers. -/
theorem le_abs_add_abs_mul_rpow_neg {k : ℝ} (hk3 : k ≤ 3) (hk0 : 0 ≤ k) {R s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ R) (A D : ℝ) :
    A ≤ (|A| * (1 + R) ^ (3 : ℝ) + |D| * (2 : ℝ) ^ (3 : ℝ)) * (1 + s) ^ (-k) := by
  have h := le_abs_mul_rpow_mul_rpow_neg hk3 hk0 hs0 hs A
  have h' : 0 ≤ |D| * (2 : ℝ) ^ (3 : ℝ) * (1 + s) ^ (-k) := by positivity
  rw [add_mul]
  linarith

/-- For real numbers with `0 ≤ k ≤ 3` and `1 ≤ R ≤ s`, all real `A` and `D` satisfy
`D * s ^ (-k) ≤ (|A| * (1 + R) ^ 3 + |D| * 2 ^ 3) * (1 + s) ^ (-k)`, with real powers. -/
theorem mul_rpow_neg_le_add_mul_rpow {k : ℝ} (hk3 : k ≤ 3) (hk0 : 0 ≤ k) {R s : ℝ} (hR : 1 ≤ R)
    (hs : R ≤ s) (A D : ℝ) :
    D * s ^ (-k) ≤ (|A| * (1 + R) ^ (3 : ℝ) + |D| * (2 : ℝ) ^ (3 : ℝ)) * (1 + s) ^ (-k) := by
  have h := mul_rpow_neg_le_abs_mul_rpow hk3 hk0 (hR.trans hs) D
  have h1 : 0 < 1 + s := by linarith
  have h2 : 0 < 1 + R := by linarith
  have h' : 0 ≤ |A| * (1 + R) ^ (3 : ℝ) * (1 + s) ^ (-k) := by positivity
  rw [add_mul]
  linarith

/-- If `1 < α`, `0 < r`, `0 < X` and `r * X ≤ 1`, then
`r ^ (4 * α) ≤ r ^ (2 * α - 3 / 2) * X ^ (-(2 * α + 3 / 2))`. -/
theorem rpow_four_mul_le_rpow_mul_rpow {α r X : ℝ} (hα : 1 < α) (hr : 0 < r) (hX : 0 < X)
    (hrX : r * X ≤ 1) :
    r ^ (4 * α) ≤ r ^ (2 * α - 3 / 2) * X ^ (-(2 * α + 3 / 2)) := by
  rw [show 4 * α = (2 * α - 3 / 2) + (2 * α + 3 / 2) by ring, Real.rpow_add hr]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr.le _)
  have h1 := rpow_le_rpow_neg_of_mul_le hX hr (by
    linarith [mul_comm r X]) (p := 2 * α + 3 / 2) (by linarith)
  exact h1

/-- If `1 < α`, `0 < r`, `0 < X` and `1 ≤ 16 * r * X`, then
`(X ^ (-(2 * α))) ^ 2 ≤ 16 ^ (2 * α - 3 / 2) * r ^ (2 * α - 3 / 2) * X ^ (-(2 * α + 3 / 2))`. -/
theorem rpow_neg_two_mul_sq_le {α r X : ℝ} (hα : 1 < α) (hr : 0 < r) (hX : 0 < X)
    (hrX : 1 ≤ 16 * r * X) :
    (X ^ (-(2 * α))) ^ 2 ≤ 16 ^ (2 * α - 3 / 2) * r ^ (2 * α - 3 / 2) * X ^ (-(2 * α + 3 / 2)) := by
  rw [rpow_sq_of_pos hX, show 2 * -(2 * α) = -(2 * α - 3 / 2) + -(2 * α + 3 / 2) by ring,
    Real.rpow_add hX]
  exact mul_le_mul_of_nonneg_right (rpow_neg_le_of_one_le_mul hr hX hrX (by linarith))
    (Real.rpow_nonneg hX.le _)

/-- For `0 < μ` and any real `α`, `μ ^ (1 - 3 / (2 * α)) = μ * ((μ ^ (1 / (2 * α))) ^ 3)⁻¹`. -/
theorem rpow_one_sub_eq_mul_inv_cube {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ ^ (1 - 3 / (2 * α)) = μ * ((μ ^ (1 / (2 * α))) ^ 3)⁻¹ := by
  rw [Real.rpow_sub hμ, Real.rpow_one, rpow_three_div_eq_rpow_cube hμ, div_eq_mul_inv]

/-- For `1 ≤ α`, `0 ≤ τ` and `0 ≤ s`, `s ^ 2 * τ ^ α⁻¹ ≤ 1 + s ^ (2 * α) * τ`. The proof applies
`y ≤ 1 + y ^ α` to `y = s ^ 2 * τ ^ α⁻¹`, whose power `y ^ α` is `s ^ (2 * α) * τ`. -/
theorem sq_mul_rpow_inv_le_one_add {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 ≤ τ) (s : ℝ) (hs : 0 ≤ s) :
    s ^ 2 * τ ^ α⁻¹ ≤ 1 + s ^ (2 * α) * τ := by
  have hα0 : 0 < α := by linarith
  have h1 := le_one_add_rpow hα (mul_nonneg (sq_nonneg s) (Real.rpow_nonneg hτ α⁻¹))
  have e : (s ^ 2 * τ ^ α⁻¹) ^ α = s ^ (2 * α) * τ := by
    rw [Real.mul_rpow (sq_nonneg s) (Real.rpow_nonneg hτ _), Real.rpow_inv_rpow hτ hα0.ne',
      Real.rpow_mul hs, Real.rpow_two]
  rw [e] at h1
  exact h1

/-- For real `α < 5 / 4`, `r > 0` and `X > 0` with `r * X ≤ 1`,
`r ^ 2 * (X ^ (-(2 * α - 1))) ^ 2 ≤ r ^ (2 * α - 3 / 2) * X ^ (-(2 * α + 3 / 2))`. The proof splits
off the factor `X ^ (7 / 2 - 2 * α)` and bounds it by `r ^ (-(7 / 2 - 2 * α))`, which holds because
`r * X ≤ 1` and `7 / 2 - 2 * α > 0`. -/
theorem sq_mul_sq_rpow_le_mul_rpow {α r X : ℝ} (hα2 : α < 5 / 4) (hr : 0 < r) (hX : 0 < X)
    (hrX : r * X ≤ 1) :
    r ^ 2 * (X ^ (-(2 * α - 1))) ^ 2 ≤ r ^ (2 * α - 3 / 2) * X ^ (-(2 * α + 3 / 2)) := by
  rw [rpow_sq_of_pos hX, show 2 * -(2 * α - 1) = (7 / 2 - 2 * α) + -(2 * α + 3 / 2) by ring,
    Real.rpow_add hX, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hX.le _)
  have h1 := rpow_le_rpow_neg_of_mul_le hr hX hrX (p := 7 / 2 - 2 * α) (by linarith)
  have e : r ^ (2 * α - 3 / 2) = r ^ (2 : ℝ) * r ^ (-(7 / 2 - 2 * α)) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [e, Real.rpow_two]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- Let `0 < c`, `0 < cμ`, `0 < w₀`, `0 ≤ ε`, `0 ≤ ε'`, `0 ≤ r`, `0 ≤ n`, `0 ≤ T`, `0 ≤ Gr`, `T ≤ E`
and `w₀ * Gr ≤ E` be real numbers. Then
`√T + (ε * √T + ε' * √Gr + √(r * n)) ≤ √((1 + ε + ε' / √w₀) ^ 2 / c + r / cμ) * √(c * E + cμ *
n)`. The proof uses `√T ≤ √E` and `√Gr ≤ √E /
√w₀` and applies the Cauchy-Schwarz inequality for two terms with the weights `c` and `cμ`. -/
theorem sqrt_add_le_sqrt_mul_sqrt {ε ε' r c cμ w₀ T Gr E n : ℝ} (hc : 0 < c) (hcμ : 0 < cμ)
    (hw₀ : 0 < w₀)
    (hε : 0 ≤ ε) (hε' : 0 ≤ ε') (hr : 0 ≤ r) (hn : 0 ≤ n) (hT0 : 0 ≤ T) (hG0 : 0 ≤ Gr)
    (hT : T ≤ E) (hG : w₀ * Gr ≤ E) :
    Real.sqrt T + (ε * Real.sqrt T + ε' * Real.sqrt Gr + Real.sqrt (r * n))
      ≤ Real.sqrt ((1 + ε + ε' / Real.sqrt w₀) ^ 2 / c + r / cμ) * Real.sqrt (c * E + cμ * n) := by
  have hE : 0 ≤ E := hT0.trans hT
  have hsw := Real.sqrt_pos.2 hw₀
  have h1 : Real.sqrt T ≤ Real.sqrt E := Real.sqrt_le_sqrt hT
  have h2 : Real.sqrt Gr ≤ Real.sqrt E / Real.sqrt w₀ := by
    rw [le_div_iff₀ hsw, ← Real.sqrt_mul hG0, mul_comm]
    exact Real.sqrt_le_sqrt hG
  have key := mul_sqrt_add_le_sqrt_mul_sqrt (α := 1 + ε + ε' / Real.sqrt w₀) (β := Real.sqrt r)
      (S := Real.sqrt n) hc hcμ hE
  rw [Real.sq_sqrt hr, Real.sq_sqrt hn] at key
  refine le_trans ?_ key
  rw [Real.sqrt_mul hr]
  have h3 : ε' * Real.sqrt Gr ≤ ε' / Real.sqrt w₀ * Real.sqrt E := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h2 hε'
  nlinarith [mul_le_mul_of_nonneg_left h1 hε]

/-- For real numbers `a < s < t`,
`(t - s) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ)) ≤ 2 * (t - a) ^ (-(1 / 2 : ℝ)) * (t - s) ^ (-(3
/ 4 : ℝ)) + 2 * (t - a) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ))`. One of `s - a` and `t -
s` is at least half of `t - a`, and its negative power is then at most twice the same power of `t -
a`. -/
theorem sub_rpow_mul_sub_rpow_le_add {a s t : ℝ} (has : a < s) (hst : s < t) :
    (t - s) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ)) ≤
      2 * (t - a) ^ (-(1 / 2 : ℝ)) * (t - s) ^ (-(3 / 4 : ℝ)) +
        2 * (t - a) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ)) := by
  have hu : 0 < s - a := sub_pos.2 has
  have hv : 0 < t - s := sub_pos.2 hst
  have hw : 0 < t - a := by linarith
  have p1 : 0 ≤ (t - s) ^ (-(3 / 4 : ℝ)) := rpow_nonneg hv.le _
  have p2 : 0 ≤ (s - a) ^ (-(1 / 2 : ℝ)) := rpow_nonneg hu.le _
  have p3 : 0 ≤ (t - a) ^ (-(1 / 2 : ℝ)) := rpow_nonneg hw.le _
  have p4 : 0 ≤ (t - a) ^ (-(3 / 4 : ℝ)) := rpow_nonneg hw.le _
  rcases le_total (t - a) (2 * (s - a)) with h | h
  · have e := rpow_le_two_mul_rpow (r := -(1 / 2 : ℝ)) hu hw h (by norm_num) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left e p1, mul_nonneg p4 p2]
  · have h' : t - a ≤ 2 * (t - s) := by linarith
    have e := rpow_le_two_mul_rpow (r := -(3 / 4 : ℝ)) hv hw h' (by norm_num) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right e p2, mul_nonneg p3 p1]

/-- For `0 < μ` and any real `α`, `μ⁻¹ ^ (1 - 3 / (2 * α)) = μ⁻¹ * (μ ^ (1 / (2 * α))) ^ 3`. -/
theorem inv_rpow_one_sub_eq_inv_mul {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ⁻¹ ^ (1 - 3 / (2 * α)) = μ⁻¹ * (μ ^ (1 / (2 * α))) ^ 3 := by
  rw [Real.inv_rpow hμ.le, rpow_one_sub_eq_mul_inv_cube hμ, mul_inv, inv_inv]

end PDE.Analysis
