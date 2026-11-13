/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Continuum.Interval.Rational.RelativeHull
public import PDE.Analysis.Calculus.SmoothTransitionDerivatives

/-!
# Rational bounds of the smooth transition

On `(0, 1)` Mathlib's `Real.smoothTransition` is `σ(t) = 1 / (1 + exp g)` with
`g = 1/t - 1/(1 - t)`. The rational bounds here use `1 + y ≤ exp y`: for `m > 0`,
`(1 + g/m)^m ≤ exp g` when `1 + g/m ≥ 0`, and `exp g ≤ (1 - g/m)^{-m}` when `g < m`, with
`m = 2^k` and the powers computed by `k` squarings rounded down (`squareChainLower`); outside these
ranges the bounds fall back to `0` and `1`. Hence `transitionLower t k bits ≤ σ(t)`
and `σ(t) ≤ transitionUpper t k bits` (`transitionLower_le`, `le_transitionUpper`), with
`σ = 0` for `t ≤ 0` and `σ = 1` for `t ≥ 1`. The relative error of the exponential bounds is
about `g²/m`. Only rational arithmetic is used.

## Main definitions

* `squareChainLower`: `k` squarings rounded down, a lower bound of `b ^ (2 ^ k)` for `b ≥ 0`.
* `transitionExponentRat`: the exponent `g = 1/t - 1/(1 - t)`.
* `transitionLower`, `transitionUpper`: rational lower and upper bounds of `σ(t)`.

## Main results

* `transitionLower_le`: `transitionLower t k bits ≤ Real.smoothTransition t`.
* `le_transitionUpper`: `Real.smoothTransition t ≤ transitionUpper t k bits`.
* `squareChainLower_mem`: for `b ≥ 0`, `squareChainLower bits k b` is a nonnegative lower bound
  of `b ^ (2 ^ k)`.
* `one_add_div_pow_le_exp`: `(1 + y/m)^m ≤ exp y` for `1 + y/m ≥ 0`.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Continuum.RationalInterval (roundDownRel roundDownRel_le)

/-- `k` squarings of `b`, each rounded down to about `bits` bits: a lower bound of `b ^ (2 ^ k)`
for `b ≥ 0`. -/
def squareChainLower (bits : ℕ) : ℕ → ℚ → ℚ
  | 0, b => b
  | k + 1, b => squareChainLower bits k (roundDownRel bits (b * b))

/-- For `b ≥ 0`, `squareChainLower bits k b` is a nonnegative lower bound of `b ^ (2 ^ k)`. -/
theorem squareChainLower_mem (bits : ℕ) :
    ∀ (k : ℕ) {b : ℚ}, 0 ≤ b →
      0 ≤ squareChainLower bits k b ∧ (squareChainLower bits k b : ℝ) ≤ (b : ℝ) ^ (2 ^ k)
  | 0, b, hb => by simp [squareChainLower, hb]
  | k + 1, b, hb => by
    have h0 : 0 ≤ roundDownRel bits (b * b) :=
      div_nonneg (by exact_mod_cast Int.floor_nonneg.2 (by positivity)) (by positivity)
    obtain ⟨ih0, ih⟩ := squareChainLower_mem bits k h0
    refine ⟨ih0, ih.trans ?_⟩
    have hr : (roundDownRel bits (b * b) : ℝ) ≤ (b : ℝ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).2 (roundDownRel_le bits (b * b))
      push_cast at this; nlinarith
    calc (roundDownRel bits (b * b) : ℝ) ^ (2 ^ k) ≤ ((b : ℝ) ^ 2) ^ (2 ^ k) :=
          pow_le_pow_left₀ (by exact_mod_cast h0) hr _
      _ = (b : ℝ) ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]; ring_nf

/-- The exponent `g = 1/t - 1/(1 - t)` of `σ(t) = 1 / (1 + exp g)` on `(0, 1)`. -/
def transitionExponentRat (t : ℚ) : ℚ := 1 / t - 1 / (1 - t)

/-- A lower bound of `σ(t)`: `1 / (1 + U)` with `U = 1 / ((1 - g/m)^m)₋ ≥ exp g`, `m = 2^k`. -/
def transitionLower (t : ℚ) (k bits : ℕ) : ℚ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else
    let g := transitionExponentRat t
    let L := squareChainLower bits k (1 - g / 2 ^ k)
    if 0 < 1 - g / 2 ^ k ∧ 0 < L then 1 / (1 + 1 / L) else 0

/-- An upper bound of `σ(t)`: `1 / (1 + L)` with `L = ((1 + g/m)^m)₋ ≤ exp g`, `m = 2^k`. -/
def transitionUpper (t : ℚ) (k bits : ℕ) : ℚ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else
    let g := transitionExponentRat t
    if 0 ≤ 1 + g / 2 ^ k then 1 / (1 + squareChainLower bits k (1 + g / 2 ^ k)) else 1

/-- `(1 + y/m)^m ≤ exp y` for `1 + y/m ≥ 0`. -/
theorem one_add_div_pow_le_exp {y : ℝ} {m : ℕ} (hm : 0 < m) (hy : 0 ≤ 1 + y / m) :
    (1 + y / m) ^ m ≤ Real.exp y := by
  have h := Real.add_one_le_exp (y / m)
  calc (1 + y / m) ^ m ≤ (Real.exp (y / m)) ^ m := pow_le_pow_left₀ hy (by linarith) m
    _ = Real.exp y := by rw [← Real.exp_nat_mul]; congr 1; field_simp

/-- `transitionLower t k bits` is a lower bound of the smooth transition `σ(t)`. -/
theorem transitionLower_le (t : ℚ) (k bits : ℕ) :
    (transitionLower t k bits : ℝ) ≤ Real.smoothTransition t := by
  unfold transitionLower
  dsimp only
  split_ifs with h0 h1 hL
  · simp [Real.smoothTransition.zero_of_nonpos (by exact_mod_cast h0 : (t : ℝ) ≤ 0)]
  · simp [Real.smoothTransition.one_of_one_le (by exact_mod_cast h1 : (1 : ℝ) ≤ t)]
  · set g := transitionExponentRat t
    have ht0 : (0 : ℝ) < t := by exact_mod_cast not_le.1 h0
    have ht1 : (t : ℝ) < 1 := by exact_mod_cast not_le.1 h1
    rw [PDE.Analysis.smoothTransition_eq_inv_one_add_exp ht0 ht1, inv_eq_one_div]
    set L := squareChainLower bits k (1 - g / 2 ^ k)
    obtain ⟨hb, hLp⟩ := hL
    have hLb := (squareChainLower_mem bits k hb.le).2
    have hm : (0 : ℕ) < 2 ^ k := by positivity
    have hexp : Real.exp (-(g : ℝ)) ≥ (1 - (g : ℝ) / (2 ^ k : ℕ)) ^ (2 ^ k) := by
      have h := one_add_div_pow_le_exp (y := -(g : ℝ)) hm (by
        have : (0 : ℝ) < 1 - (g : ℝ) / 2 ^ k := by exact_mod_cast hb
        push_cast; rw [neg_div]; linarith)
      push_cast at h ⊢
      rw [neg_div, ← sub_eq_add_neg] at h
      exact h
    have hgr : (g : ℝ) = 1 / t - 1 / (1 - t) := by
      simp [g, transitionExponentRat]
    have hLr : (0 : ℝ) < L := by exact_mod_cast hLp
    have hLexp : (L : ℝ) ≤ Real.exp (-(g : ℝ)) := by
      refine hLb.trans ?_
      push_cast at hexp ⊢
      exact hexp
    have hU : Real.exp (g : ℝ) ≤ 1 / L := by
      rw [le_div_iff₀ hLr]
      calc Real.exp (g : ℝ) * L ≤ Real.exp (g : ℝ) * Real.exp (-(g : ℝ)) :=
            mul_le_mul_of_nonneg_left hLexp (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [← hgr]
    push_cast
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · exact_mod_cast Real.smoothTransition.nonneg _

/-- `transitionUpper t k bits` is an upper bound of the smooth transition `σ(t)`. -/
theorem le_transitionUpper (t : ℚ) (k bits : ℕ) :
    Real.smoothTransition t ≤ (transitionUpper t k bits : ℝ) := by
  unfold transitionUpper
  dsimp only
  split_ifs with h0 h1 hL
  · simp [Real.smoothTransition.zero_of_nonpos (by exact_mod_cast h0 : (t : ℝ) ≤ 0)]
  · simp [Real.smoothTransition.one_of_one_le (by exact_mod_cast h1 : (1 : ℝ) ≤ t)]
  · set g := transitionExponentRat t
    have ht0 : (0 : ℝ) < t := by exact_mod_cast not_le.1 h0
    have ht1 : (t : ℝ) < 1 := by exact_mod_cast not_le.1 h1
    rw [PDE.Analysis.smoothTransition_eq_inv_one_add_exp ht0 ht1, inv_eq_one_div]
    obtain ⟨hL0, hLb⟩ := squareChainLower_mem bits k hL
    have hm : (0 : ℕ) < 2 ^ k := by positivity
    have hexp := one_add_div_pow_le_exp (y := (g : ℝ)) hm (by
      have : (0 : ℝ) ≤ 1 + (g : ℝ) / 2 ^ k := by exact_mod_cast hL
      push_cast; linarith)
    have hgr : (g : ℝ) = 1 / t - 1 / (1 - t) := by
      simp [g, transitionExponentRat]
    have hle : (squareChainLower bits k (1 + g / 2 ^ k) : ℝ) ≤ Real.exp (g : ℝ) := by
      refine hLb.trans ?_
      push_cast at hexp ⊢
      exact hexp
    rw [← hgr]
    push_cast
    have : (0 : ℝ) ≤ squareChainLower bits k (1 + g / 2 ^ k) := by exact_mod_cast hL0
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · exact_mod_cast Real.smoothTransition.le_one _

end CAS.Numerics
