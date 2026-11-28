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
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Linarith.NNRealPreprocessor

set_option linter.style.header false

/-!
# Powers, roots, exponentials and logarithms of real numbers: first lemmas

The lemmas rewrite and compare expressions with `Real.rpow`, `Real.sqrt`, `Real.exp` and `Real.log`:
laws of exponents for particular exponents, monotonicity in the base or in the exponent, bounds of
an exponential or of a power by a simpler function. The proofs combine the lemmas of Mathlib on
these functions with `positivity`, `norm_num` and `nlinarith`.

## Main results

* `PDE.Analysis.exists_pow_eq_mul_self_and_le`: For reals `0 < q < 1`, `δ > 0` and `K ≥ 0` there are
  reals `r`, `c` and a natural `N` with `0 < r < 1`, `0 < c`, `q ^ j = r ^ j * r ^ j` for all
  natural `j`, `2 * K * r ^ (N + 1) ≤ c` and `c * (1 / (1 - r)) = δ / 2`.
* `PDE.Analysis.inv_pow_three_mul_self`: For every real `t`, `t⁻¹ ^ 3 * t = t⁻¹ ^ 2`. This also
  holds for `t = 0`, because `0⁻¹ = 0`.
* `PDE.Analysis.inv_sqrt_pow_three_rpow`: For real `c > 0` and `q`,
  `((√c ^ 3)⁻¹) ^ q = c ^ (-(3 / 2 * q))`.
* `PDE.Analysis.mul_pow_le_of_pow_lt_div`: Let `K ≥ 0`, `η > 0` and `0 ≤ q < 1` be reals and `N ≤ n`
  natural numbers. If `q ^ N < η / (K + 1)`, then `K * q ^ n ≤ η`.
* `PDE.Analysis.rpow_quarter_mul_rpow_quarter_mul`: For real `μ > 0`,
  `μ ^ (1 / 4 : ℝ) * μ ^ (1 / 4 : ℝ) * μ = √μ ^ 3`.
* `PDE.Analysis.rpow_three_halves_eq_sqrt_pow`: For real `μ > 0`, `μ ^ (3 / 2 : ℝ) = √μ ^ 3`. A case
  of `rpow_three_halves_eq_sqrt_pow_of_nonneg`, which asks for `0 ≤ μ` only.
* `PDE.Analysis.rpow_three_quarters_eq_mul_sqrt`: For real `μ > 0`,
  `μ ^ (3 / 4 : ℝ) = μ ^ (1 / 4 : ℝ) * √μ`.
* `PDE.Analysis.two_pi_mul_exp_neg_sq_le`: For real `τ > 0` and `t`, `2 * π * t * Real.exp (-((4 * π
  ^ 2 * τ) * t ^ 2)) ≤ (1 + 2 / τ) * Real.exp (-((2 * π ^ 2 * τ) * t ^ 2))`.

There are 55 further lemmas of the same kind.

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

/-- For `0 ≤ y`, `|Real.exp (-y) - 1 + y| ≤ y ^ 2`. For `y ≤ 1` this is the second order bound
`Real.abs_exp_sub_one_sub_id_le` at `-y`, and for `y > 1` it follows from `0 < Real.exp (-y) ≤ 1`.
-/
theorem abs_exp_neg_sub_one_add_le {y : ℝ} (hy : 0 ≤ y) : |Real.exp (-y) - 1 + y| ≤ y ^ 2 := by
  rcases le_or_gt y 1 with h | h
  · have := Real.abs_exp_sub_one_sub_id_le (x := -y) (by rw [abs_neg, abs_of_nonneg hy]; exact h)
    rwa [neg_sq, sub_neg_eq_add] at this
  · have h1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : 0 < Real.exp (-y) := Real.exp_pos _
    rw [abs_le]
    constructor <;> nlinarith

/-- For real `A ≤ 0` and `B ≤ 0`, `|Real.exp A - Real.exp B| ≤ |A - B|`: the real exponential is
1-Lipschitz on the nonpositive reals. The proof assumes `B ≤ A`, writes
`exp A - exp B = exp A * (1 - exp (B - A))` and uses `x + 1 ≤ exp x`. -/
theorem abs_exp_sub_exp_le_of_nonpos {A B : ℝ} (hA : A ≤ 0) (hB : B ≤ 0) :
    |Real.exp A - Real.exp B| ≤ |A - B| := by
  wlog h : B ≤ A generalizing A B
  · rw [abs_sub_comm, abs_sub_comm A]; exact this hB hA (le_of_not_ge h)
  have h1 : Real.exp A - Real.exp B = Real.exp A * (1 - Real.exp (B - A)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  have h2 : 1 - Real.exp (B - A) ≤ A - B := by linarith [Real.add_one_le_exp (B - A)]
  have h3 : 0 ≤ 1 - Real.exp (B - A) := by
    have : Real.exp (B - A) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have h4 : Real.exp A ≤ 1 := Real.exp_le_one_iff.2 hA
  rw [h1, abs_of_nonneg (mul_nonneg (Real.exp_pos A).le h3), abs_of_nonneg (by linarith)]
  calc Real.exp A * (1 - Real.exp (B - A)) ≤ 1 * (A - B) := mul_le_mul h4 h2 h3 zero_le_one
    _ = A - B := one_mul _

/-- For every real `y`, `|Real.exp y - 1 - y| ≤ y ^ 2 * Real.exp |y|`. For `|y| ≤ 1` this follows
from `|Real.exp y - 1 - y| ≤ y ^ 2`, and for `1 < |y|` from `1 ≤ y ^ 2` and
`|y| + 1 ≤ Real.exp |y|`. -/
theorem abs_exp_sub_one_sub_le_mul (y : ℝ) : |Real.exp y - 1 - y| ≤ y ^ 2 * Real.exp |y| := by
  by_cases hy : |y| ≤ 1
  · exact (Real.abs_exp_sub_one_sub_id_le hy).trans
      (le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (abs_nonneg y)))
  · rw [not_le] at hy
    have h0 : 0 ≤ Real.exp y - 1 - y := by linarith [Real.add_one_le_exp y]
    rw [abs_of_nonneg h0]
    have hsq : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have ha : |y| + 1 ≤ Real.exp |y| := Real.add_one_le_exp _
    have hb : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.2 (le_abs_self y)
    have hc : 0 < Real.exp |y| := Real.exp_pos _
    have hd : Real.exp |y| ≤ y ^ 2 * Real.exp |y| := le_mul_of_one_le_left hc.le hsq
    rcases le_or_gt 0 y with h | h
    · linarith
    · have h1 : Real.exp y ≤ 1 := Real.exp_le_one_iff.2 h.le
      have h2 : |y| = -y := abs_of_neg h
      linarith

/-- For real numbers, if `S ^ 2 ≤ X * Y` and `0 ≤ X` then `|S| ≤ √X * √Y`. -/
theorem abs_le_sqrt_mul_sqrt {S X Y : ℝ} (h : S ^ 2 ≤ X * Y) (hX : 0 ≤ X) :
    |S| ≤ Real.sqrt X * Real.sqrt Y := by
  rw [← Real.sqrt_mul hX, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- Let `0 < c`, `0 < cμ`, `0 < w₀`, `0 ≤ eS`, `0 ≤ eG`, `0 ≤ r`, `0 ≤ t`, `0 ≤ E`, `A ≤ √E` and
`Gn ≤ √E / √w₀` be real numbers. Then
`A + (eS * A + eG * Gn + √r * √t) ≤ √((1 + eS + eG / √w₀) ^ 2 / c + r / cμ) * √(c * E + cμ *
t)`. The proof bounds the left side by `(1 + eS + eG / √w₀) * √E + √r *
√t` and applies the Cauchy-Schwarz inequality for two terms with the weights `c` and `cμ`. -/
theorem add_le_sqrt_mul_sqrt_of_le {c cμ E A Gn w₀ eS eG r t : ℝ} (hc : 0 < c) (hcμ : 0 < cμ)
    (hw₀ : 0 < w₀)
    (heS : 0 ≤ eS) (heG : 0 ≤ eG) (hr : 0 ≤ r) (ht : 0 ≤ t) (hE : 0 ≤ E)
    (hA : A ≤ Real.sqrt E) (hG : Gn ≤ Real.sqrt E / Real.sqrt w₀) :
    A + (eS * A + eG * Gn + Real.sqrt r * Real.sqrt t) ≤
      Real.sqrt ((1 + eS + eG / Real.sqrt w₀) ^ 2 / c + r / cμ) * Real.sqrt (c * E + cμ * t) := by
  obtain ⟨q, hq0, rfl⟩ : ∃ q, 0 ≤ q ∧ r = q ^ 2 := ⟨Real.sqrt r, Real.sqrt_nonneg _,
      (Real.sq_sqrt hr).symm⟩
  rw [Real.sqrt_sq hq0]
  have hsw : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw₀
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 ≤ s ∧ E = s ^ 2 := ⟨Real.sqrt E, Real.sqrt_nonneg _,
      (Real.sq_sqrt hE).symm⟩
  obtain ⟨n, hn0, rfl⟩ : ∃ n, 0 ≤ n ∧ t = n ^ 2 := ⟨Real.sqrt t, Real.sqrt_nonneg _,
      (Real.sq_sqrt ht).symm⟩
  rw [Real.sqrt_sq hs0] at hA hG
  rw [Real.sqrt_sq hn0]
  set a := 1 + eS + eG / Real.sqrt w₀ with ha
  have ha0 : 0 ≤ a := by positivity
  have step1 : A + (eS * A + eG * Gn + q * n) ≤ a * s + q * n := by
    have h1 : eG * Gn ≤ eG * (s / Real.sqrt w₀) := mul_le_mul_of_nonneg_left hG heG
    have h2 : eS * A ≤ eS * s := mul_le_mul_of_nonneg_left hA heS
    have h3 : a * s = s + eS * s + eG * (s / Real.sqrt w₀) := by rw [ha]; ring
    linarith
  refine step1.trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  rw [div_add_div _ _ hc.ne' hcμ.ne', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (a * cμ * n - q * c * s)]

/-- For reals `a` and `s > 0`, `(a + s) ^ 10 * Real.exp (-(a ^ 2) / (4 * s ^ 2)) ≤ 40 ^ 5 * s ^ 10`.
With `u = a ^ 2 / (4 * s ^ 2)`, the proof uses `(a + s) ^ 2 ≤ 40 * s ^ 2 * (1 + u / 5)` and
`1 + u / 5 ≤ Real.exp (u / 5)`, and raises to the fifth power. -/
theorem add_pow_ten_mul_gaussian_le (a s : ℝ) (hs : 0 < s) :
    (a + s) ^ 10 * Real.exp (-(a ^ 2) / (4 * s ^ 2)) ≤ 40 ^ 5 * s ^ 10 := by
  set u := a ^ 2 / (4 * s ^ 2) with hu
  have hs2 : 0 < s ^ 2 := by positivity
  have hau : a ^ 2 = 4 * s ^ 2 * u := by rw [hu]; field_simp
  have h1 : (a + s) ^ 2 ≤ 40 * s ^ 2 * (1 + u / 5) := by
    nlinarith [sq_nonneg (a - s)]
  have h2 : 1 + u / 5 ≤ Real.exp (u / 5) := by linarith [Real.add_one_le_exp (u / 5)]
  have he : Real.exp (u / 5) ^ 5 = Real.exp u := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : (a + s) ^ 10 ≤ 40 ^ 5 * s ^ 10 * Real.exp u := by
    calc (a + s) ^ 10 = ((a + s) ^ 2) ^ 5 := by ring
      _ ≤ (40 * s ^ 2 * Real.exp (u / 5)) ^ 5 := by
        apply pow_le_pow_left₀ (sq_nonneg _)
        calc (a + s) ^ 2 ≤ 40 * s ^ 2 * (1 + u / 5) := h1
          _ ≤ 40 * s ^ 2 * Real.exp (u / 5) := by gcongr
      _ = 40 ^ 5 * s ^ 10 * Real.exp u := by rw [mul_pow, he]; ring
  have hneg : -(a ^ 2) / (4 * s ^ 2) = -u := by rw [hu]; ring
  rw [hneg]
  calc (a + s) ^ 10 * Real.exp (-u) ≤ 40 ^ 5 * s ^ 10 * Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = 40 ^ 5 * s ^ 10 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- For real `r > 0` and `ρ ≥ 0` with `1 / (16 * r) ≤ ρ`, and any real `C`,
`6 * (C / (1 + ρ) ^ 2) ^ 2 ≤ 24 * C ^ 2 * √r * (1 + ρ) ^ (-(7 / 2 : ℝ))`. The proof writes
`(1 + ρ) ^ (-(7 / 2 : ℝ))` as `((1 + ρ) ^ 4)⁻¹ * √(1 + ρ)` and uses `1 ≤ 4 * (√r * √(1 + ρ))`. -/
theorem div_sq_sq_le_sqrt_mul_rpow {r ρ C : ℝ} (hr : 0 < r) (hρ : 1 / (16 * r) ≤ ρ) (hρ0 : 0 ≤ ρ) :
    6 * (C / (1 + ρ) ^ 2) ^ 2 ≤ 24 * C ^ 2 * Real.sqrt r * (1 + ρ) ^ (-(7 / 2 : ℝ)) := by
  have ha : 0 < 1 + ρ := by linarith
  have e1 : (1 + ρ) ^ (-(7 / 2 : ℝ)) = ((1 + ρ) ^ 4)⁻¹ * Real.sqrt (1 + ρ) := by
    rw [show (-(7 / 2 : ℝ)) = -((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add ha,
      Real.rpow_neg ha.le, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have e2 : (C / (1 + ρ) ^ 2) ^ 2 = C ^ 2 * ((1 + ρ) ^ 4)⁻¹ := by
    field_simp
  have h16 : 1 ≤ 16 * r * ρ := by
    rw [div_le_iff₀ (by positivity)] at hρ
    linarith
  have key : 1 ≤ 4 * (Real.sqrt r * Real.sqrt (1 + ρ)) := by
    rw [← Real.sqrt_mul hr.le]
    have : 1 / 4 ≤ Real.sqrt (r * (1 + ρ)) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith
    linarith
  rw [e1, e2]
  have hX : 0 ≤ C ^ 2 * ((1 + ρ) ^ 4)⁻¹ := by positivity
  calc 6 * (C ^ 2 * ((1 + ρ) ^ 4)⁻¹) = 6 * (C ^ 2 * ((1 + ρ) ^ 4)⁻¹) * 1 := (mul_one _).symm
    _ ≤ 6 * (C ^ 2 * ((1 + ρ) ^ 4)⁻¹) * (4 * (Real.sqrt r * Real.sqrt (1 + ρ))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

/-- For reals `0 < q < 1`, `δ > 0` and `K ≥ 0` there are reals `r`, `c` and a natural `N` with
`0 < r < 1`, `0 < c`, `q ^ j = r ^ j * r ^ j` for all natural `j`, `2 * K * r ^ (N + 1) ≤ c` and
`c * (1 / (1 - r)) = δ / 2`. The proof takes `r = √q` and `c = δ * (1 - √q) / 2`, and `N` so large
that `√q ^ N < c / (2 * K + 1)`. -/
theorem exists_pow_eq_mul_self_and_le (q δ K : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ)
    (hK0 : 0 ≤ K) :
    ∃ (r c : ℝ) (N : ℕ), 0 < r ∧ r < 1 ∧ 0 < c ∧ (∀ j : ℕ, q ^ j = r ^ j * r ^ j) ∧
      2 * K * r ^ (N + 1) ≤ c ∧ c * (1 / (1 - r)) = δ / 2 := by
  have hr0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hr1 : Real.sqrt q < 1 := (Real.sqrt_lt_sqrt hq0.le hq1).trans_eq Real.sqrt_one
  have hr1' : 0 < 1 - Real.sqrt q := by linarith
  have hc : 0 < δ * (1 - Real.sqrt q) / 2 := div_pos (mul_pos hδ hr1') two_pos
  have hK1 : (0 : ℝ) < 2 * K + 1 := by linarith
  obtain ⟨N, hNr⟩ := exists_pow_lt_of_lt_one (div_pos hc hK1) hr1
  refine ⟨Real.sqrt q, δ * (1 - Real.sqrt q) / 2, N, hr0, hr1, hc, fun j ↦ ?_, ?_, ?_⟩
  · rw [← mul_pow, Real.mul_self_sqrt hq0.le]
  · have h1 : Real.sqrt q ^ (N + 1) ≤ Real.sqrt q ^ N :=
      pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ N)
    have h2 : Real.sqrt q ^ N * (2 * K + 1) < δ * (1 - Real.sqrt q) / 2 := (lt_div_iff₀ hK1).1 hNr
    have h3 : 0 ≤ Real.sqrt q ^ (N + 1) := pow_nonneg hr0.le _
    nlinarith
  · field_simp

/-- For real `κ`, `P`, `CK`, `M` and `0 < t₀` there is a natural number `k > 0` such that
`1 - Real.exp (-(P / k)) < t₀` and
`2 * (4 * CK * (1 - Real.exp (-(P / k))) ^ (1 / 4 : ℝ) * (Real.exp (κ * (P / k)) * M)) < 1 /
4`. Both left sides are continuous functions of `x = P / k` that vanish at `x = 0`, and `P /
k` tends to `0` as `k` tends to infinity. -/
theorem exists_scaled_step_count (κ P CK M t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ k : ℕ, 0 < k ∧ 1 - Real.exp (-(P / k)) < t₀ ∧
      2 * (4 * CK * (1 - Real.exp (-(P / k))) ^ (1 / 4 : ℝ) * (Real.exp (κ * (P / k)) * M)) <
        1 / 4 := by
  set g : ℝ → ℝ := fun x ↦
    2 * (4 * CK * (1 - Real.exp (-x)) ^ (1 / 4 : ℝ) * (Real.exp (κ * x) * M)) with hg
  set h : ℝ → ℝ := fun x ↦ 1 - Real.exp (-x) with hh
  have hgc : Continuous g := by
    have h1 : Continuous fun x : ℝ ↦ (1 - Real.exp (-x)) ^ (1 / 4 : ℝ) :=
      (Real.continuous_rpow_const (by norm_num)).comp
        (continuous_const.sub (Real.continuous_exp.comp continuous_neg))
    rw [hg]
    exact continuous_const.mul ((continuous_const.mul h1).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_const))
  have hhc : Continuous h := continuous_const.sub (Real.continuous_exp.comp continuous_neg)
  have hg0 : g 0 = 0 := by
    simp [hg]
  have hh0 : h 0 = 0 := by simp [hh]
  have ht : Tendsto (fun k : ℕ ↦ P / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat P
  have tg : Tendsto (fun k : ℕ ↦ g (P / k)) atTop (𝓝 0) := by
    have := (hgc.tendsto 0).comp ht
    rw [hg0] at this
    exact this
  have th : Tendsto (fun k : ℕ ↦ h (P / k)) atTop (𝓝 0) := by
    have := (hhc.tendsto 0).comp ht
    rw [hh0] at this
    exact this
  have e1 := tg.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)
  have e2 := th.eventually_lt_const ht₀
  obtain ⟨k, hk1, hk2, hk3⟩ := ((eventually_ge_atTop 1).and (e2.and e1)).exists
  exact ⟨k, hk1, hk2, hk3⟩

/-- For all real `P`, `CK`, `M` and every `t₀ > 0` there is a natural number `k > 0` with
`1 - Real.exp (-(P / k)) < t₀` and
`2 * (4 * CK * (1 - Real.exp (-(P / k))) ^ (1 / 4 : ℝ) * (Real.exp (P / k / 4) * M)) < 1 /
4`. This is `exists_scaled_step_count` with `κ = 1 / 4`. -/
theorem exists_step_count (P CK M t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ k : ℕ, 0 < k ∧ 1 - Real.exp (-(P / k)) < t₀ ∧
      2 * (4 * CK * (1 - Real.exp (-(P / k))) ^ (1 / 4 : ℝ) * (Real.exp (P / k / 4) * M)) < 1 /
          4 := by
  obtain ⟨k, hk, h1, h2⟩ := exists_scaled_step_count (1 / 4) P CK M t₀ ht₀
  exact ⟨k, hk, h1, by rwa [show (1 / 4 : ℝ) * (P / k) = P / k / 4 by ring] at h2⟩

/-- For every real `P > 0` there is a natural number `n` with
`2 * Real.exp (-(n * P)) ^ (1 / 4 : ℝ) < 1`. Any `n > 4 / P` works, because then the left side is
less than `2 * Real.exp (-1)`, which is less than `1`. -/
theorem exists_two_mul_exp_rpow_lt_one {P : ℝ} (hP : 0 < P) :
    ∃ n : ℕ, 2 * Real.exp (-(n * P)) ^ (1 / 4 : ℝ) < 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / P)
  refine ⟨n, ?_⟩
  have hnP : 4 < n * P := by
    rwa [div_lt_iff₀ hP] at hn
  rw [← Real.exp_mul]
  have h2 : Real.exp (-(n * P) * (1 / 4 : ℝ)) < Real.exp (-1) :=
    Real.exp_lt_exp.mpr (by linarith)
  have h3 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
    linarith
  have h4 : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-1)]

/-- For real `s₀` and `t` with `t < 1`, `Real.exp (-((s₀ - Real.log (1 - t)) - s₀)) = 1 - t`. -/
theorem exp_neg_sub_log_one_sub (s₀ t : ℝ) (ht : t < 1) :
    exp (-((s₀ - Real.log (1 - t)) - s₀)) = 1 - t := by
  rw [show -((s₀ - Real.log (1 - t)) - s₀) = Real.log (1 - t) by ring, Real.exp_log (by linarith)]

/-- For real `τ > 0` and `N ≥ 0`,
`(τ⁻¹ * N ^ 2) ^ (1 / 4 : ℝ) * ((τ ^ 2)⁻¹ * N ^ 2) ^ (1 / 4 : ℝ) = τ ^ (-(3 / 4 : ℝ)) *
N`. The product of the two bases is the fourth power of the right side. -/
theorem inv_mul_sq_rpow_quarter_mul {τ N : ℝ} (hτ : 0 < τ) (hN : 0 ≤ N) :
    (τ⁻¹ * N ^ 2) ^ (1 / 4 : ℝ) * ((τ ^ 2)⁻¹ * N ^ 2) ^ (1 / 4 : ℝ) = τ ^ (-(3 / 4 : ℝ)) * N := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  have e : τ⁻¹ * N ^ 2 * ((τ ^ 2)⁻¹ * N ^ 2) = (τ ^ (-(3 / 4 : ℝ)) * N) ^ (4 : ℕ) := by
    rw [mul_pow, ← Real.rpow_natCast (τ ^ (-(3 / 4 : ℝ))), ← Real.rpow_mul hτ.le,
      show (-(3 / 4 : ℝ)) * ((4 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hτ.le,
      Real.rpow_natCast]
    field_simp
  rw [e, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]

/-- For every real `t`, `t⁻¹ ^ 3 * t = t⁻¹ ^ 2`. This also holds for `t = 0`, because `0⁻¹ = 0`. -/
theorem inv_pow_three_mul_self (t : ℝ) : t⁻¹ ^ 3 * t = t⁻¹ ^ 2 := by
  rcases eq_or_ne t 0 with h | h
  · simp [h]
  · field_simp

/-- For real `μ > 0`, `(√μ)⁻¹ * √μ ^ 3 = μ`. -/
theorem inv_sqrt_mul_sqrt_pow_three {μ : ℝ} (hμ : 0 < μ) :
    (Real.sqrt μ)⁻¹ * (Real.sqrt μ) ^ 3 = μ := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul, Real.sq_sqrt hμ.le]

/-- For real `c > 0` and `q`, `((√c ^ 3)⁻¹) ^ q = c ^ (-(3 / 2 * q))`. -/
theorem inv_sqrt_pow_three_rpow {c : ℝ} (hc : 0 < c) (q : ℝ) :
    ((Real.sqrt c ^ 3)⁻¹) ^ q = c ^ (-(3 / 2 * q)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_neg hc.le,
    ← Real.rpow_mul hc.le]
  congr 1
  push_cast
  ring

/-- Let `a`, `b`, `A`, `c`, `G`, `X` be nonnegative real numbers and `r > 0`, with `b ≤ A ^ 2`,
`G ≤ (c / r) ^ 2 * b` and `X ≤ a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)`. If
`L ≤ 4 * (X ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ))`, then
`L ≤ 4 * c * (a ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r`. The proof shows
`X ^ (1 / 2 : ℝ) ≤ a ^ (1 / 4 : ℝ) * A ^ (1 / 2 : ℝ)` and `G ^ (1 / 2 : ℝ) ≤ c / r * A`. -/
theorem le_mul_rpow_three_halves_of_le {a b G X A c r L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbA : b ≤ A ^ 2)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hr : 0 < r) (hG0 : 0 ≤ G) (hG : G ≤ (c / r) ^ 2 * b)
    (hX0 : 0 ≤ X) (hX : X ≤ a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ))
    (hL : L ≤ 4 * (X ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ))) :
    L ≤ 4 * c * (a ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by
  have h1 : X ^ (1 / 2 : ℝ) ≤ a ^ (1 / 4 : ℝ) * A ^ (1 / 2 : ℝ) := by
    calc X ^ (1 / 2 : ℝ) ≤ (a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hX0 hX (by norm_num)
      _ = a ^ (1 / 4 : ℝ) * b ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha,
            ← Real.rpow_mul hb]
          norm_num
      _ ≤ a ^ (1 / 4 : ℝ) * A ^ (1 / 2 : ℝ) := by
          gcongr
          calc b ^ (1 / 4 : ℝ) ≤ (A ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hb hbA (by norm_num)
            _ = A ^ (1 / 2 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
                norm_num
  have h2 : G ^ (1 / 2 : ℝ) ≤ c / r * A := by
    have hcr : 0 ≤ c / r * A := by positivity
    calc G ^ (1 / 2 : ℝ) ≤ ((c / r * A) ^ 2) ^ (1 / 2 : ℝ) := by
          apply Real.rpow_le_rpow hG0 _ (by norm_num)
          calc G ≤ (c / r) ^ 2 * b := hG
            _ ≤ (c / r) ^ 2 * A ^ 2 := by gcongr
            _ = (c / r * A) ^ 2 := by ring
      _ = c / r * A := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hcr]
          norm_num
  have h3 : (a ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) = a ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_mul ha]
    norm_num
  have h4 : A ^ (3 / 2 : ℝ) = A ^ (1 / 2 : ℝ) * A := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add' hA (by norm_num), Real.rpow_one]
  have hX' : 0 ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX0 _
  have hG' : 0 ≤ G ^ (1 / 2 : ℝ) := Real.rpow_nonneg hG0 _
  calc L ≤ 4 * (X ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ)) := hL
    _ ≤ 4 * ((a ^ (1 / 4 : ℝ) * A ^ (1 / 2 : ℝ)) * (c / r * A)) := by gcongr
    _ = 4 * c * (a ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by
        rw [h3, h4]
        field_simp

/-- Let `l > 0`, `ρ ≥ 0`, `C ≥ 0` and `D` be reals and `n` a natural number. If
`D ≤ l ^ n * (C / (1 + l * ρ) ^ n)`, then `D * ρ ^ n ≤ C`. This holds because
`(l * ρ) ^ n ≤ (1 + l * ρ) ^ n`. -/
theorem mul_pow_le_of_le_mul_div {l ρ C D : ℝ} (hl : 0 < l) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (n : ℕ)
    (hD : D ≤ l ^ n * (C / (1 + l * ρ) ^ n)) : D * ρ ^ n ≤ C := by
  have hA : 0 < (1 + l * ρ) ^ n := by positivity
  have hle : (l * ρ) ^ n ≤ (1 + l * ρ) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) _
  calc D * ρ ^ n ≤ l ^ n * (C / (1 + l * ρ) ^ n) * ρ ^ n := by gcongr
    _ = C * ((l * ρ) ^ n / (1 + l * ρ) ^ n) := by ring
    _ ≤ C * 1 := by gcongr; exact div_le_one_of_le₀ hle hA.le
    _ = C := mul_one C

/-- Let `K ≥ 0`, `η > 0` and `0 ≤ q < 1` be reals and `N ≤ n` natural numbers. If
`q ^ N < η / (K + 1)`, then `K * q ^ n ≤ η`. -/
theorem mul_pow_le_of_pow_lt_div {K q η : ℝ} {n N : ℕ} (hK0 : 0 ≤ K) (hη : 0 < η) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hn : N ≤ n)
    (hN : q ^ N < η / (K + 1)) : K * q ^ n ≤ η := by
  have hqN : q ^ n ≤ q ^ N := pow_le_pow_of_le_one hq0 hq1.le hn
  calc K * q ^ n ≤ K * (η / (K + 1)) := mul_le_mul_of_nonneg_left (hqN.trans hN.le) hK0
    _ ≤ (K + 1) * (η / (K + 1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = η := by field_simp

/-- Let `0 < ℓ < 1`, `a ≥ 0`, `b ≥ 0` and `ε > 0` be reals. If `ℓ < (ε / (a + b + 1)) ^ 4`, then
`a * √(√ℓ) + b * √ℓ ≤ ε`. The proof shows `√ℓ ≤ √(√ℓ)` and `√(√ℓ) < ε / (a + b + 1)`. -/
theorem mul_sqrt_sqrt_add_mul_sqrt_le {ℓ a b ε : ℝ} (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 < ε) (h1 : ℓ < 1)
    (h2 : ℓ < (ε / (a + b + 1)) ^ 4) : a * Real.sqrt (Real.sqrt ℓ) + b * Real.sqrt ℓ ≤ ε := by
  have hu0 : 0 ≤ Real.sqrt (Real.sqrt ℓ) := Real.sqrt_nonneg _
  have e1 : Real.sqrt (Real.sqrt ℓ) ^ 2 = Real.sqrt ℓ := Real.sq_sqrt (Real.sqrt_nonneg _)
  have e2 : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  have e4 : Real.sqrt (Real.sqrt ℓ) ^ 4 = ℓ := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, e1, e2]
  have hδ : 0 < ε / (a + b + 1) := by positivity
  have hu1 : Real.sqrt (Real.sqrt ℓ) < 1 := by
    rw [← pow_lt_pow_iff_left₀ hu0 zero_le_one (by norm_num : (4 : ℕ) ≠ 0), e4, one_pow]
    exact h1
  have huδ : Real.sqrt (Real.sqrt ℓ) < ε / (a + b + 1) := by
    rw [← pow_lt_pow_iff_left₀ hu0 hδ.le (by norm_num : (4 : ℕ) ≠ 0), e4]
    exact h2
  have hsq : Real.sqrt ℓ ≤ Real.sqrt (Real.sqrt ℓ) := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu1.le)]
  have k : (a + b) * (ε / (a + b + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hb, mul_le_mul_of_nonneg_left huδ.le (add_nonneg ha hb)]

/-- For real `s > 0` and `y ≥ 0`, `(1 + y) * Real.exp (-(y * s)) ≤ 1 + 1 / s`. The proof uses
`Real.exp (-(y * s)) ≤ 1` and `y * s * Real.exp (-(y * s)) ≤ 1`. -/
theorem one_add_mul_exp_neg_mul_le {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) :
    (1 + y) * Real.exp (-(y * s)) ≤ 1 + 1 / s := by
  have h1 : Real.exp (-(y * s)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have h2 : y * s * Real.exp (-(y * s)) ≤ 1 := by
    have h3 : y * s + 1 ≤ Real.exp (y * s) := Real.add_one_le_exp _
    have h4 : Real.exp (y * s) * Real.exp (-(y * s)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-(y * s))]
  have h5 : y * Real.exp (-(y * s)) ≤ 1 / s := by
    rw [le_div_iff₀ hs]
    nlinarith
  nlinarith

/-- For real `τ > 0` and `x ≥ 0`,
`(1 + 4 * π ^ 2 * x) * Real.exp (-(4 * π ^ 2 * x * τ)) ^ 2 ≤ (1 + 1 / τ) *
Real.exp (-(4 * π ^ 2 * x * τ))`. The proof uses `1 + 4 * π ^ 2 * x ≤ (1 + 1 / τ) *
(1 + 4 * π ^ 2 * x * τ)` and `y + 1 ≤ Real.exp y`, so that one of the two exponential factors on the
left is absorbed. -/
theorem one_add_mul_exp_neg_sq_le {τ x : ℝ} (hτ : 0 < τ) (hx : 0 ≤ x) :
    (1 + 4 * π ^ 2 * x) * Real.exp (-(4 * π ^ 2 * x * τ)) ^ 2 ≤
      (1 + 1 / τ) * Real.exp (-(4 * π ^ 2 * x * τ)) := by
  have hy : 0 ≤ 4 * π ^ 2 * x * τ := by positivity
  have h1 : 1 + 4 * π ^ 2 * x ≤ (1 + 1 / τ) * (1 + 4 * π ^ 2 * x * τ) := by
    have e : (1 + 1 / τ) * (1 + 4 * π ^ 2 * x * τ) = 1 + 4 * π ^ 2 * x * τ + 1 / τ + 4 * π ^ 2 *
        x := by
      field_simp
      ring
    rw [e]
    have : 0 < 1 / τ := by positivity
    linarith
  have h2 := Real.add_one_le_exp (4 * π ^ 2 * x * τ)
  have h3 : Real.exp (4 * π ^ 2 * x * τ) * Real.exp (-(4 * π ^ 2 * x * τ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hE := Real.exp_pos (-(4 * π ^ 2 * x * τ))
  calc (1 + 4 * π ^ 2 * x) * Real.exp (-(4 * π ^ 2 * x * τ)) ^ 2
      ≤ ((1 + 1 / τ) * Real.exp (4 * π ^ 2 * x * τ)) * Real.exp (-(4 * π ^ 2 * x * τ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left (by
          linarith) (by positivity)))
          (by positivity)
    _ = (1 + 1 / τ) * (Real.exp (4 * π ^ 2 * x * τ) * Real.exp (-(4 * π ^ 2 * x * τ))) *
          Real.exp (-(4 * π ^ 2 * x * τ)) := by ring
    _ = (1 + 1 / τ) * Real.exp (-(4 * π ^ 2 * x * τ)) := by rw [h3, mul_one]

/-- For real `s₀` and `t` with `t < 1`, `1 - Real.exp (-((s₀ - Real.log (1 - t)) - s₀)) = t`. So
`σ ↦ 1 - Real.exp (-(σ - s₀))` undoes `t ↦ s₀ - Real.log (1 - t)` for `t < 1`. -/
theorem one_sub_exp_neg_log_one_sub (s₀ t : ℝ) (ht : t < 1) :
    1 - Real.exp (-((s₀ - Real.log (1 - t)) - s₀)) = t := by
  have h : 0 < 1 - t := by linarith
  rw [show -((s₀ - Real.log (1 - t)) - s₀) = Real.log (1 - t) by ring, Real.exp_log h]
  ring

/-- For all real `s₀` and `σ`, `1 - Real.exp (-(σ - s₀)) < 1`. -/
theorem one_sub_exp_neg_sub_lt_one (s₀ σ : ℝ) : 1 - Real.exp (-(σ - s₀)) < 1 := by
  linarith [Real.exp_pos (-(σ - s₀))]

/-- For a real `v ≥ 0` and a natural number `n`, `v ^ n * Real.exp (-v) ≤ n.factorial`. -/
theorem pow_mul_exp_neg_le_factorial {v : ℝ} (hv : 0 ≤ v) (n : ℕ) :
    v ^ n * Real.exp (-v) ≤ (n.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (x := v) hv n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- For real `W ≥ 0` and a real exponent `e` with `0 ≤ e ≤ 1`, `W ^ e ≤ max 1 W`. -/
theorem rpow_le_max_one_self {W e : ℝ} (hW : 0 ≤ W) (he : 0 ≤ e) (he1 : e ≤ 1) : W ^ e ≤ max 1 W :=
    by
  rcases le_total W 1 with h | h
  · exact (Real.rpow_le_one hW h he).trans (le_max_left _ _)
  · calc W ^ e ≤ W ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h he1
      _ = W := Real.rpow_one W
      _ ≤ max 1 W := le_max_right _ _

/-- For real `x ≥ 1` and `y ≥ 1` and real exponents with `0 ≤ m` and `m < r`,
`x ^ m ≤ y ^ m * x ^ (3 : ℝ) + y ^ (m - r) * x ^ r`. If `x ≤ y` the first term on the right bounds
`x ^ m`, and if `y ≤ x` the second term does, because `m - r < 0`. -/
theorem rpow_le_rpow_mul_add_rpow_sub {x y m r : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hmr : m < r)
    (hm : 0 ≤ m) :
    x ^ m ≤ y ^ m * x ^ (3 : ℝ) + y ^ (m - r) * x ^ r := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rcases le_total x y with hxy | hxy
  · have h1 : x ^ m ≤ y ^ m := Real.rpow_le_rpow hx0.le hxy hm
    have h2 : 1 ≤ x ^ (3 : ℝ) := Real.one_le_rpow hx (by norm_num)
    have h3 : 0 ≤ y ^ (m - r) * x ^ r := by positivity
    nlinarith [Real.rpow_nonneg hy0.le m]
  · have h1 : x ^ (m - r) ≤ y ^ (m - r) := Real.rpow_le_rpow_of_nonpos hy0 hxy (by linarith)
    have e : x ^ m = x ^ (m - r) * x ^ r := by
      rw [← Real.rpow_add hx0]; ring_nf
    have h4 : 0 ≤ y ^ m * x ^ (3 : ℝ) := by positivity
    rw [e]
    nlinarith [Real.rpow_nonneg hx0.le r]

/-- For real `μ > 0`, `μ ^ (1 / 4 : ℝ) * μ ^ (-(1 / 4 : ℝ)) = 1`. -/
theorem rpow_quarter_mul_rpow_neg_quarter {μ : ℝ} (hμ : 0 < μ) :
    μ ^ (1 / 4 : ℝ) * μ ^ (-(1 / 4 : ℝ)) = 1 := by
  rw [← Real.rpow_add hμ]
  norm_num

/-- For a real `y ≥ 0`, `y ^ (3 / 2) = √y ^ 3`, where `3 / 2` is a real exponent. -/
theorem rpow_three_halves_eq_sqrt_pow_of_nonneg {y : ℝ} (hy : 0 ≤ y) : y ^ (3 / 2 : ℝ) = √y ^ 3 :=
    by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

/-- For real `μ > 0`, `μ ^ (3 / 2 : ℝ) = √μ ^ 3`. A case of
`rpow_three_halves_eq_sqrt_pow_of_nonneg`, which asks for `0 ≤ μ` only. -/
theorem rpow_three_halves_eq_sqrt_pow {μ : ℝ} (hμ : 0 < μ) : μ ^ (3 / 2 : ℝ) = Real.sqrt μ ^ 3 :=
    rpow_three_halves_eq_sqrt_pow_of_nonneg hμ.le

/-- For real `μ > 0`, `μ ^ (3 / 4 : ℝ) = μ ^ (1 / 4 : ℝ) * √μ`. -/
theorem rpow_three_quarters_eq_mul_sqrt {μ : ℝ} (hμ : 0 < μ) :
    μ ^ (3 / 4 : ℝ) = μ ^ (1 / 4 : ℝ) * Real.sqrt μ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hμ]
  norm_num

/-- For real `μ > 0`, `μ ^ (3 / 4 : ℝ) * μ⁻¹ = μ ^ (-(1 / 4 : ℝ))`. -/
theorem rpow_three_quarters_mul_inv {μ : ℝ} (hμ : 0 < μ) :
    μ ^ (3 / 4 : ℝ) * μ⁻¹ = μ ^ (-(1 / 4 : ℝ)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hμ]
  norm_num

/-- For a real `y > 0`, `y ^ 2 * (y⁻¹ ^ 3) ^ (2 : ℝ) = y ^ (-4 : ℝ)`. -/
theorem sq_mul_inv_pow_three_rpow_two {y : ℝ} (hy : 0 < y) :
    y ^ 2 * (y⁻¹ ^ 3) ^ (2 : ℝ) = y ^ (-4 : ℝ) := by
  have h1 : y⁻¹ ^ 3 = y ^ (-3 : ℝ) := by
    rw [Real.rpow_neg hy.le, inv_pow]; norm_cast
  rw [h1, ← Real.rpow_mul hy.le, ← Real.rpow_two, ← Real.rpow_add hy]
  norm_num

/-- For real `x ≥ 0`, `(x ^ 2) ^ (1 / 2 : ℝ) = x`. -/
theorem sq_rpow_half {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx]
  norm_num

/-- For real `K ≥ 0`, `τ > 0` and `s ≥ 0`,
`√((K * τ ^ (-(1 / 2 : ℝ)) * s) * (K * τ ^ (-(1 : ℝ)) * s)) = K * τ ^ (-(3 / 4 : ℝ)) *
s`. The product under the root is the square of the right side. -/
theorem sqrt_phi_product {K τ s : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hs : 0 ≤ s) :
    Real.sqrt ((K * τ ^ (-(1 / 2 : ℝ)) * s) * (K * τ ^ (-(1 : ℝ)) * s)) = K * τ ^ (-(3 / 4 : ℝ)) *
        s := by
  have e : (τ ^ (-(3 / 4 : ℝ))) ^ 2 = τ ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
    norm_num
  rw [show (K * τ ^ (-(1 / 2 : ℝ)) * s) * (K * τ ^ (-(1 : ℝ)) * s) =
      (K * τ ^ (-(3 / 4 : ℝ)) * s) ^ 2 by
    rw [mul_pow, mul_pow, e]; ring]
  exact Real.sqrt_sq (by positivity)

/-- For real `μ > 0`, `√μ ^ 3 = μ ^ (3 / 2 : ℝ)`. This is `rpow_three_halves_eq_sqrt_pow` with the
two sides exchanged. -/
theorem sqrt_pow_three_eq_rpow {μ : ℝ} (hμ : 0 < μ) : (Real.sqrt μ) ^ 3 = μ ^ (3 / 2 : ℝ) :=
  (rpow_three_halves_eq_sqrt_pow hμ).symm

/-- For all real `s₀` and `σ`, `s₀ - Real.log (1 - (1 - Real.exp (-(σ - s₀)))) = σ`. So
`t ↦ s₀ - Real.log (1 - t)` undoes `σ ↦ 1 - Real.exp (-(σ - s₀))`. -/
theorem sub_log_one_sub_one_sub_exp (s₀ σ : ℝ) :
    s₀ - Real.log (1 - (1 - Real.exp (-(σ - s₀)))) = σ := by
  rw [show 1 - (1 - Real.exp (-(σ - s₀))) = Real.exp (-(σ - s₀)) by ring, Real.log_exp]
  ring

/-- For real `t < T`, `(T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) = (T - t)⁻¹`. -/
theorem sub_rpow_neg_half_mul_self (T t : ℝ) (ht : t < T) :
    (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) = (T - t)⁻¹ := by
  rw [← rpow_add (sub_pos.2 ht), show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num, rpow_neg_one]

/-- For real `τ > 0` and `t`,
`2 * π * t * Real.exp (-((4 * π ^ 2 * τ) * t ^ 2)) ≤ (1 + 2 / τ) * Real.exp (-((2 * π ^ 2 * τ) * t ^
2))`. The proof splits the exponential on the left into two equal factors and shows
`2 * π * t * Real.exp (-((2 * π ^ 2 * τ) * t ^ 2)) ≤ 1 + 2 / τ` from `x + 1 ≤ Real.exp x`. -/
theorem two_pi_mul_exp_neg_sq_le {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    2 * π * t * Real.exp (-((4 * π ^ 2 * τ) * t ^ 2)) ≤
      (1 + 2 / τ) * Real.exp (-((2 * π ^ 2 * τ) * t ^ 2)) := by
  have hsplit : Real.exp (-((4 * π ^ 2 * τ) * t ^ 2)) =
      Real.exp (-((2 * π ^ 2 * τ) * t ^ 2)) * Real.exp (-((2 * π ^ 2 * τ) * t ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hx := Real.add_one_le_exp ((2 * π ^ 2 * τ) * t ^ 2)
  have key : 2 * π * t ≤ (1 + 2 / τ) * ((2 * π ^ 2 * τ) * t ^ 2 + 1) := by
    have h1 : (1 + 2 / τ) * ((2 * π ^ 2 * τ) * t ^ 2 + 1) =
        (2 * π ^ 2 * τ) * t ^ 2 + 1 + (2 * π * t) ^ 2 + 2 / τ := by
      field_simp; ring
    rw [h1]
    have : 0 ≤ 2 / τ := by positivity
    have : 0 ≤ (2 * π ^ 2 * τ) * t ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * π * t - 1)]
  have hb : 2 * π * t * Real.exp (-((2 * π ^ 2 * τ) * t ^ 2)) ≤ 1 + 2 / τ := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    exact key.trans (mul_le_mul_of_nonneg_left hx (by positivity))
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

/-- For real `μ > 0`, `μ ^ (1 / 4 : ℝ) * μ ^ (1 / 4 : ℝ) * μ = √μ ^ 3`. -/
theorem rpow_quarter_mul_rpow_quarter_mul {μ : ℝ} (hμ : 0 < μ) :
    μ ^ (1 / 4 : ℝ) * μ ^ (1 / 4 : ℝ) * μ = Real.sqrt μ ^ 3 := by
  rw [← rpow_three_halves_eq_sqrt_pow hμ, ← Real.rpow_add hμ, ← Real.rpow_add_one hμ.ne']
  norm_num

/-- For real numbers with `0 < τ`, `τ ≤ T` and `0 ≤ x`,
`x ^ 2 * (1 + x) * Real.exp (-(16 * π ^ 2 * τ * x)) * τ ^ 3 ≤ 2 * |T| + 7`. With
`e = Real.exp (-(16 * π ^ 2 * τ * x))` the left side equals
`τ * ((τ * x) ^ 2 * e) + (τ * x) ^ 3 * e`, and the bound `v ^ n * Real.exp (-v) ≤ n.factorial` gives
at most `2 * τ + 6`. -/
theorem sq_mul_exp_neg_mul_pow_le {T τ x : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T) (hx : 0 ≤ x) :
    x ^ 2 * (1 + x) * Real.exp (-(16 * π ^ 2 * τ * x)) * τ ^ 3 ≤ 2 * |T| + 7 := by
  have hK : 1 ≤ 16 * π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hy : 0 ≤ τ * x := mul_nonneg hτ.le hx
  have hyv : τ * x ≤ 16 * π ^ 2 * τ * x := by nlinarith
  have hv : 0 ≤ 16 * π ^ 2 * τ * x := le_trans hy hyv
  have hE : 0 < Real.exp (-(16 * π ^ 2 * τ * x)) := Real.exp_pos _
  have e2 := pow_mul_exp_neg_le_factorial hv 2
  have e3 := pow_mul_exp_neg_le_factorial hv 3
  norm_num [Nat.factorial] at e2 e3
  have h2 : (τ * x) ^ 2 ≤ (16 * π ^ 2 * τ * x) ^ 2 := pow_le_pow_left₀ hy hyv 2
  have h3 : (τ * x) ^ 3 ≤ (16 * π ^ 2 * τ * x) ^ 3 := pow_le_pow_left₀ hy hyv 3
  have hA : (τ * x) ^ 2 * Real.exp (-(16 * π ^ 2 * τ * x)) ≤ 2 :=
    le_trans (mul_le_mul_of_nonneg_right h2 hE.le) e2
  have hB : (τ * x) ^ 3 * Real.exp (-(16 * π ^ 2 * τ * x)) ≤ 6 :=
    le_trans (mul_le_mul_of_nonneg_right h3 hE.le) e3
  have heq : x ^ 2 * (1 + x) * Real.exp (-(16 * π ^ 2 * τ * x)) * τ ^ 3 =
      τ * ((τ * x) ^ 2 * Real.exp (-(16 * π ^ 2 * τ * x))) +
        (τ * x) ^ 3 * Real.exp (-(16 * π ^ 2 * τ * x)) := by ring
  rw [heq]
  have hTa : τ ≤ |T| := hτT.trans (le_abs_self T)
  have hτA := mul_le_mul_of_nonneg_left hA hτ.le
  nlinarith

/-- For real `τ > 0`, `(√τ)⁻¹ = τ ^ (-(1 / 2))`, with the real power. -/
theorem inv_sqrt_eq_rpow_neg_half {τ : ℝ} (hτ : 0 < τ) : (Real.sqrt τ)⁻¹ = τ ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hτ.le]

/-- For `0 < τ`, `τ⁻¹ * (√τ)⁻¹ = τ ^ (-(3 / 2 : ℝ))`. -/
theorem inv_mul_inv_sqrt_eq_rpow {τ : ℝ} (hτ : 0 < τ) :
    τ⁻¹ * (Real.sqrt τ)⁻¹ = τ ^ (-(3 / 2 : ℝ)) := by
  rw [inv_sqrt_eq_rpow_neg_half hτ, ← Real.rpow_neg_one, ← Real.rpow_add hτ]
  norm_num

/-- For real `α > 1` and `0 < τ ≤ 1`, `τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4))`. The exponent
`-(3 / (4 * α))` is at least `-(3 / 4)`, and powers of `τ ≤ 1` decrease in the exponent. -/
theorem rpow_neg_three_div_le_rpow_neg {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ)) := by
  have h : 3 / (4 * α) ≤ 3 / 4 := div_le_div_of_nonneg_left (by
    norm_num) (by norm_num) (by linarith)
  exact Real.rpow_le_rpow_of_exponent_ge hτ hτ1 (by linarith)

/-- For `1 < α`, `0 < τ ≤ 1` and nonnegative reals `C`, `e`, `z`,
`C * τ ^ (-(3 / (4 * α))) * e * z ≤ C * τ ^ (-(3 / 4 : ℝ)) * e * z`. It is the inequality
`τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ))` multiplied by the nonnegative factors `C`, `e` and `z`.
-/
theorem mul_rpow_neg_three_div_mul_le {α C e z τ : ℝ} (hα : 1 < α) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hz : 0 ≤ z)
    (h0 : 0 < τ) (h1 : τ ≤ 1) :
    C * τ ^ (-(3 / (4 * α))) * e * z ≤ C * τ ^ (-(3 / 4 : ℝ)) * e * z :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rpow_neg_three_div_le_rpow_neg hα h0 h1) hC) he) hz

/-- For real `x ≥ 0` and `0 ≤ q ≤ 1`, `x ^ q ≤ 1 + x`, with the real power. If `x ≤ 1` then
`x ^ q ≤ 1`, and if `1 ≤ x` then `x ^ q ≤ x`. -/
theorem rpow_le_one_add {x q : ℝ} (hx : 0 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : x ^ q ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · linarith [Real.rpow_le_one hx h hq0]
  · have := Real.rpow_le_rpow_of_exponent_le h hq1
    rw [Real.rpow_one] at this
    linarith

/-- For `0 ≤ s` and a real exponent `g` with `0 ≤ g ≤ 1`, `s ^ g * Real.exp (-s) ≤ 1`. -/
theorem rpow_mul_exp_neg_le_one {s g : ℝ} (hs : 0 ≤ s) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    s ^ g * Real.exp (-s) ≤ 1 := by
  have h1 := rpow_le_one_add hs hg0 hg1
  have h2 := Real.add_one_le_exp s
  calc s ^ g * Real.exp (-s) ≤ Real.exp s * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- For `0 ≤ y` and a real exponent `p` with `0 ≤ p ≤ 1`, `y ^ p * Real.exp (-(2 * y)) ≤ 1`. The
proof uses `y ^ p ≤ 1 + y ≤ Real.exp (2 * y)`. -/
theorem rpow_mul_exp_neg_two_mul_le {y p : ℝ} (hy : 0 ≤ y) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    y ^ p * Real.exp (-(2 * y)) ≤ 1 := by
  have h1 := rpow_le_one_add hy hp0 hp1
  have h2 : 1 + y ≤ Real.exp (2 * y) := by
    have := Real.add_one_le_exp (2 * y)
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  linarith

/-- For `0 ≤ y`, `0 < τ` and a real exponent `g` with `0 ≤ g ≤ 1`,
`y ^ g * Real.exp (-(τ * y)) ≤ τ ^ (-g)`. The proof applies `s ^ g * Real.exp (-s) ≤ 1` to
`s = τ * y`. -/
theorem rpow_mul_exp_neg_mul_le_rpow {y τ g : ℝ} (hy : 0 ≤ y) (hτ : 0 < τ) (hg0 : 0 ≤ g)
    (hg1 : g ≤ 1) :
    y ^ g * Real.exp (-(τ * y)) ≤ τ ^ (-g) := by
  have h := rpow_mul_exp_neg_le_one (mul_nonneg hτ.le hy) hg0 hg1
  rw [Real.mul_rpow hτ.le hy] at h
  have hp : 0 < τ ^ g := Real.rpow_pos_of_pos hτ g
  rw [Real.rpow_neg hτ.le]
  calc y ^ g * Real.exp (-(τ * y)) = (τ ^ g)⁻¹ * (τ ^ g * y ^ g * Real.exp (-(τ * y))) := by
        rw [mul_assoc (τ ^ g), ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    _ ≤ (τ ^ g)⁻¹ * 1 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)
    _ = (τ ^ g)⁻¹ := mul_one _

/-- For `1 < α`, `0 < τ` and `0 ≤ r`,
`r ^ 2 * Real.exp (-(2 * (r ^ (2 * α) * τ))) ≤ τ ^ (-(1 / α))`. The proof applies
`y ^ p * Real.exp (-(2 * y)) ≤ 1` with `y = r ^ (2 * α) * τ` and `p = 1 / α`, for which
`y ^ p = r ^ 2 * τ ^ (1 / α)`. -/
theorem sq_mul_exp_neg_le_rpow_neg {α τ r : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hr : 0 ≤ r) :
    r ^ 2 * Real.exp (-(2 * (r ^ (2 * α) * τ))) ≤ τ ^ (-(1 / α)) := by
  have hα0 : 0 < α := by linarith
  have hy : 0 ≤ r ^ (2 * α) * τ := by positivity
  have hp0 : 0 ≤ 1 / α := by positivity
  have hp1 : 1 / α ≤ 1 := by rw [div_le_one hα0]; linarith
  have hyp : (r ^ (2 * α) * τ) ^ (1 / α) = r ^ 2 * τ ^ (1 / α) := by
    rw [Real.mul_rpow (by positivity) hτ.le, ← Real.rpow_mul hr]
    congr 1
    rw [show 2 * α * (1 / α) = ((2 : ℕ) : ℝ) by field_simp; norm_num, Real.rpow_natCast]
  have key := rpow_mul_exp_neg_two_mul_le hy hp0 hp1
  rw [hyp] at key
  have ht : 0 < τ ^ (1 / α) := Real.rpow_pos_of_pos hτ _
  calc r ^ 2 * Real.exp (-(2 * (r ^ (2 * α) * τ)))
      = (r ^ 2 * τ ^ (1 / α) * Real.exp (-(2 * (r ^ (2 * α) * τ)))) * (τ ^ (1 / α))⁻¹ := by
        field_simp
    _ ≤ 1 * (τ ^ (1 / α))⁻¹ := mul_le_mul_of_nonneg_right key (inv_nonneg.mpr ht.le)
    _ = τ ^ (-(1 / α)) := by rw [one_mul, Real.rpow_neg hτ.le]

/-- For real `c`, `d` and `γ ≥ 0`, if `c ≤ γ ^ 2 * d` then `√c ≤ γ * √d`. The square root is
monotone and `√(γ ^ 2 * d) = γ * √d`. -/
theorem sqrt_le_mul_sqrt_of_le {c d γ : ℝ} (hγ : 0 ≤ γ) (h : c ≤ γ ^ 2 * d) :
    Real.sqrt c ≤ γ * Real.sqrt d := by
  calc Real.sqrt c ≤ Real.sqrt (γ ^ 2 * d) := Real.sqrt_le_sqrt h
    _ = γ * Real.sqrt d := by rw [Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq hγ]

/-- Let `x`, `D`, `t`, `r` be real with `0 ≤ x` and `0 ≤ t`, and let `m`, `n` be natural numbers
with `m * n = r`. If `x ≤ D / (1 + t) ^ m`, then `x ^ n ≤ D ^ n * (1 + t) ^ (-r)`. Both sides
of the hypothesis are raised to the power `n`. -/
theorem pow_le_pow_mul_rpow_neg {x D t r : ℝ} (m n : ℕ) (hx0 : 0 ≤ x) (ht : 0 ≤ t)
    (hr : (m : ℝ) * n = r) (hx : x ≤ D / (1 + t) ^ m) : x ^ n ≤ D ^ n * (1 + t) ^ (-r) := by
  have hpos : 0 < 1 + t := by linarith
  calc x ^ n ≤ (D / (1 + t) ^ m) ^ n := pow_le_pow_left₀ hx0 hx n
    _ = D ^ n * (1 + t) ^ (-r) := by
        rw [Real.rpow_neg hpos.le, ← hr, Real.rpow_mul hpos.le, Real.rpow_natCast,
          Real.rpow_natCast, div_pow, ← pow_mul, div_eq_mul_inv, pow_mul]

/-- If `κ = √a` or `κ = √b` for real `a`, `b`, then `0 ≤ κ`. -/
theorem nonneg_of_eq_sqrt_or_eq_sqrt {κ a b : ℝ} (hκ : κ = Real.sqrt a ∨ κ = Real.sqrt b) :
    0 ≤ κ := by
  rcases hκ with rfl | rfl <;> exact Real.sqrt_nonneg _

/-- For real `x > 0` and `0 ≤ m ≤ g`, `min 1 (x ^ g) ≤ x ^ m`, with real powers. If `x ≤ 1` then
`x ^ g ≤ x ^ m`, and if `1 ≤ x` then `1 ≤ x ^ m`. -/
theorem min_one_rpow_le {x g m : ℝ} (hx : 0 < x) (hm : 0 ≤ m) (hmg : m ≤ g) :
    min 1 (x ^ g) ≤ x ^ m := by
  rcases le_total x 1 with h | h
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_exponent_ge hx h hmg)
  · exact (min_le_left _ _).trans (Real.one_le_rpow h hm)

/-- For real `ε ≥ 0` and `x ≥ 0`, if `x ≤ ε ^ 4` then `x ^ (1 / 4) ≤ ε`, with the real power
`1 / 4`. The power `1 / 4` is monotone on the nonnegative reals and `(ε ^ 4) ^ (1 / 4) = ε`. -/
theorem rpow_quarter_le {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) (h : x ≤ ε ^ 4) :
    x ^ (1 / 4 : ℝ) ≤ ε := by
  have e : (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
  calc x ^ (1 / 4 : ℝ) ≤ (ε ^ 4) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hx h (by norm_num)
    _ = ε := by rw [e]; exact Real.pow_rpow_inv_natCast hε (by norm_num)

/-- For real `s ≥ 0` and `t ≥ 0`, `|exp (-s) - exp (-t)| ≤ |s - t|`. For `s ≤ t` the difference is
`exp (-s) * (1 - exp (-(t - s)))`, with `exp (-s) ≤ 1` and `1 - exp (-(t - s)) ≤ t - s`. -/
theorem abs_exp_neg_sub_exp_neg_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.exp (-s) - Real.exp (-t)| ≤ |s - t| := by
  have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t → |Real.exp (-s) - Real.exp (-t)| ≤ |s - t| := by
    intro s t hs hst
    have h1 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
      rw [← Real.exp_add]
      ring_nf
    have h2 := Real.add_one_le_exp (-(t - s))
    have h3 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : 0 < Real.exp (-s) := Real.exp_pos _
    have h5 : Real.exp (-(t - s)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [h1, abs_of_nonneg (by nlinarith), abs_of_nonpos (by linarith)]
    nlinarith
  rcases le_total s t with h | h
  · exact key s t hs h
  · rw [abs_sub_comm, abs_sub_comm s]
    exact key t s ht h

/-- For real `T > 0` and `b > 0`, if `T < 1 / (64 * b ^ 2)` then `√T * b ≤ 1 / 8`. The hypothesis
gives `T * (64 * b ^ 2) < 1`, that is `(√T * b) ^ 2 < 1 / 64`. -/
theorem sqrt_mul_le_eighth_of_lt {T b : ℝ} (hT : 0 < T) (hb : 0 < b) (hTb : T < 1 / (64 * b ^ 2)) :
    Real.sqrt T * b ≤ 1 / 8 := by
  have h64 : T * (64 * b ^ 2) < 1 := (lt_div_iff₀ (by positivity)).mp hTb
  nlinarith [Real.sq_sqrt hT.le, Real.sqrt_nonneg T, mul_nonneg (Real.sqrt_nonneg T) hb.le]

/-- For every real `τ > 0`, `0 < 1 - exp (-τ)`. -/
theorem one_sub_exp_neg_pos {τ : ℝ} (hτ : 0 < τ) : 0 < 1 - Real.exp (-τ) := by
  have : Real.exp (-τ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

/-- For real `τ > 0`, `exp (-τ) < 1`. -/
theorem exp_neg_lt_one {τ : ℝ} (h : 0 < τ) : Real.exp (-τ) < 1 := by
  have h1 := Real.exp_lt_exp.mpr (show -τ < 0 by linarith)
  rwa [Real.exp_zero] at h1

/-- For real `τ` with `0 < τ ≤ 1`, `τ / 2 ≤ 1 - exp (-τ)`. From `τ + 1 ≤ exp τ` and
`exp (-τ) * exp τ = 1`. -/
theorem half_le_one_sub_exp_neg {τ : ℝ} (h0 : 0 < τ) (h1 : τ ≤ 1) : τ / 2 ≤ 1 - Real.exp (-τ) := by
  have e1 : Real.exp (-τ) * Real.exp τ = 1 := by rw [← Real.exp_add]; simp
  have h2 := Real.add_one_le_exp τ
  have h3 := Real.exp_pos (-τ)
  nlinarith [mul_le_mul_of_nonneg_left h2 h3.le]

/-- For real `a ≥ 0` and `b ≥ 0`, if `1 + b ≤ 2 * (1 + a)` then
`(1 + a) ^ (-4) ≤ 16 * (1 + b) ^ (-4)`, with real powers. The fourth power of the hypothesis
gives `(1 + b) ^ 4 ≤ 16 * (1 + a) ^ 4`. -/
theorem rpow_neg_four_le_sixteen_mul_rpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : 1 + b ≤ 2 * (1 + a)) :
    (1 + a) ^ (-4 : ℝ) ≤ 16 * (1 + b) ^ (-4 : ℝ) := by
  have h1 : (1 + b) ^ (4 : ℝ) ≤ 16 * (1 + a) ^ (4 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h (by norm_num)
  have hpa : 0 < (1 + a) ^ (4 : ℝ) := by positivity
  have hpb : 0 < (1 + b) ^ (4 : ℝ) := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    inv_le_comm₀ hpa (by positivity), inv_div, div_le_iff₀ (by norm_num)]
  linarith

/-- For a real `r > 0` and reals `u`, `v`, `w` with `u + v = w`, `r ^ (-u) * r ^ (-v) = r ^ (-w)`.
-/
theorem rpow_neg_mul_rpow_neg_eq {r : ℝ} (hr : 0 < r) (u v w : ℝ) (h : u + v = w) :
    r ^ (-u) * r ^ (-v) = r ^ (-w) := by
  rw [← Real.rpow_add hr, ← h]
  congr 1
  ring

/-- For real `a ≥ 0` and `b ≥ 0`, `√a * √b ≤ a + b`. -/
theorem sqrt_mul_sqrt_le_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ a + b := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sqrt_nonneg a, Real.sqrt_nonneg b]

end PDE.Analysis
