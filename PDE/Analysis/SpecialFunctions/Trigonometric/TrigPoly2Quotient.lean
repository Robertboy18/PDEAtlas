/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Quotients of two-variable trigonometric tables by `sin` and `cos`

A table without cosines in `β` is divisible by `sin β`:
`sin (kβ) / sin β = ∑_{n < k} w(n, k) cos (nβ)`, where `w(n, k)` is `1` at `n = 0`, `2` for
`0 < n < k` with `k - n` odd, and `0` otherwise (`trigQuotientWeight`,
`sin_mul_sum_trigQuotientWeight`). A table odd about `π/2` in `β`, with cosines of odd and sines of
even frequency only, is divisible by `cos β`: `cos (kβ) / cos β` and `sin (kβ) / cos β` carry
the same weights with the signs `(-1)^((k - 1 - n) / 2)` (`trigQuotientSign`,
`cos_mul_sum_trigQuotientWeight`). These sums expand the smooth quotients `sineQuotient` and
`oddCosineQuotient` (`sum_trigQuotientWeight_mul_cos_eq_sineQuotient`,
`sum_trigQuotientWeight_mul_cos_eq_oddCosineQuotient`). The quotient tables `TrigPoly2.divSinβ`,
`TrigPoly2.divSinθ`, `TrigPoly2.divCosβ` and `TrigPoly2.divCosθ` have degree one lower in the
divided variable and satisfy `q · sin = p`, respectively `q · cos = p`, at every point, so
`q = p / sin` and `q = p / cos` wherever the divisor is nonzero (`TrigPoly2.eval_divSinβ_eq_div`
and its variants). At a zero of the sine or the cosine the quotient table takes the limit of the
quotient, not the value `p / 0 = 0` of Lean's division. These identities absorb the factors
`1 / sin` and `1 / cos` of spherical and compactified coordinates into trigonometric tables.

Parities pass through the weights. The sine and the cosine vanish only on countable sets
(`dense_sin_ne_zero`, `dense_cos_ne_zero`), so an identity `f · w = g` with `f` continuous gives
`f` the parity of `g` times the parity of `w` about any point (`IsEvenAt.of_mul_eq`,
`IsOddAt.of_mul_eq`), and keeps the parities in the other variable
(`TrigPoly2.IsEvenAtθ.of_eval_mul_β` and its variants).

## Main results

* `TrigPoly2.eval_divSinβ_mul_sin`, `TrigPoly2.eval_divSinθ_mul_sin`,
  `TrigPoly2.eval_divCosβ_mul_cos`, `TrigPoly2.eval_divCosθ_mul_cos`, and the quotient forms
  `TrigPoly2.eval_divSinβ_eq_div` and its variants.
* `TrigPoly2.isEvenAtβ_zero_divSinβ`, `TrigPoly2.isEvenAtβ_pi_div_two_divCosβ` and the other
  parities of the quotients.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Analysis
open Finset

/-! ### One-variable quotients -/

/-- The weight of `cos (n x)` in `sin (k x) / sin x`: `1` at `n = 0` and `2` at `0 < n < k`
when `k - n` is odd, `0` otherwise. Up to the sign `trigQuotientSign`, it is also the weight of
`m_i (n x)` in `m_i (k x) / cos x`. -/
def trigQuotientWeight (n k : ℕ) : ℤ :=
  if n < k ∧ (k - n) % 2 = 1 then (if n = 0 then 1 else 2) else 0

/-- The sign `(-1)^((k - 1 - n) / 2)` of `m_i (n x)` in `m_i (k x) / cos x`. -/
def trigQuotientSign (n k : ℕ) : ℤ :=
  (-1) ^ ((k - 1 - n) / 2)

theorem trigQuotientWeight_eq_zero {n k : ℕ} (h : k ≤ n) : trigQuotientWeight n k = 0 := by
  simp only [trigQuotientWeight]
  rw [ite_eq_right_iff.mpr fun h' ↦ absurd h'.1 (by omega)]

private theorem sum_range_trigQuotientWeight_succ_succ (f : ℕ → ℤ → ℝ) (hf : ∀ n, f n 0 = 0)
    (k : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ range (k + 2), f n (trigQuotientWeight n (k + 2)) * x n =
      ∑ n ∈ range k, f n (trigQuotientWeight n k) * x n + f (k + 1) 2 * x (k + 1) := by
  rw [sum_range_succ, sum_range_succ]
  have h₁ : trigQuotientWeight k (k + 2) = 0 := by
    simp only [trigQuotientWeight]
    rw [ite_eq_right_iff.mpr fun h' ↦ absurd h'.2 (by omega)]
  have h₂ : trigQuotientWeight (k + 1) (k + 2) = 2 := by
    simp only [trigQuotientWeight]
    rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_right_iff.mpr fun h' ↦ absurd h' (by omega)]
  rw [h₁, h₂, hf, zero_mul, add_zero]
  congr 1
  refine sum_congr rfl fun n hn ↦ ?_
  have := mem_range.mp hn
  congr 2
  simp only [trigQuotientWeight]
  congr 1
  apply propext
  omega

/-- `sin x · ∑_{n < k} w(n, k) cos (n x) = sin (k x)`. -/
theorem sin_mul_sum_trigQuotientWeight (k : ℕ) (x : ℝ) :
    Real.sin x * ∑ n ∈ range k, (trigQuotientWeight n k : ℝ) * Real.cos (n * x) =
      Real.sin (k * x) := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp [trigQuotientWeight]
  | more k ih _ =>
    rw [sum_range_trigQuotientWeight_succ_succ (fun _ w ↦ (w : ℝ)) (fun _ ↦ by simp) k
      (fun n ↦ Real.cos (n * x)), mul_add, ih]
    rw [show ((k + 2 : ℕ) : ℝ) * x = ((k + 1 : ℕ) : ℝ) * x + x by push_cast; ring,
      show (k : ℝ) * x = ((k + 1 : ℕ) : ℝ) * x - x by push_cast; ring, Real.sin_add,
      Real.sin_sub]
    push_cast
    ring

/-- The same identity with any range containing the frequencies below `k`. -/
theorem sin_mul_sum_range_trigQuotientWeight {k N : ℕ} (hk : k ≤ N) (x : ℝ) :
    Real.sin x * ∑ n ∈ range N, (trigQuotientWeight n k : ℝ) * Real.cos (n * x) =
      Real.sin (k * x) := by
  rw [← sin_mul_sum_trigQuotientWeight k x, ← sum_subset (range_subset_range.mpr hk)
    fun n _ hn ↦ by rw [trigQuotientWeight_eq_zero (by simpa using hn)]; simp]

private theorem trigQuotientSign_succ_succ {n k : ℕ} (h : n < k) :
    trigQuotientSign n (k + 2) = -trigQuotientSign n k := by
  rw [trigQuotientSign, trigQuotientSign, show (k + 2 - 1 - n) / 2 = (k - 1 - n) / 2 + 1 by omega,
    pow_succ]
  ring

/-- For `i + k` odd, `cos x · ∑_{n < k} w(n, k) σ(n, k) m_i (n x) = m_i (k x)`: the quotients
`cos ((2m+1) x) / cos x` and `sin (2m x) / cos x`. -/
theorem cos_mul_sum_trigQuotientWeight (i : Fin 2) (k : ℕ) (hik : (i.val + k) % 2 = 1) (x : ℝ) :
    Real.cos x * ∑ n ∈ range k,
      ((trigQuotientWeight n k * trigQuotientSign n k : ℤ) : ℝ) * trigMode i (n * x) =
      trigMode i (k * x) := by
  induction k using Nat.twoStepInduction with
  | zero =>
    have : i = 1 := by fin_cases i <;> simp_all
    subst this
    simp
  | one =>
    have : i = 0 := by fin_cases i <;> simp_all
    subst this
    simp [trigQuotientWeight, trigQuotientSign]
  | more k ih _ =>
    have hk : (i.val + k) % 2 = 1 := by omega
    have hterm : ∀ n ∈ range k,
        ((trigQuotientWeight n (k + 2) * trigQuotientSign n (k + 2) : ℤ) : ℝ) *
        trigMode i (n * x) =
          -(((trigQuotientWeight n k * trigQuotientSign n k : ℤ) : ℝ) * trigMode i (n * x)) := by
      intro n hn
      have hn' := mem_range.mp hn
      rw [trigQuotientSign_succ_succ hn']
      have hw : trigQuotientWeight n (k + 2) = trigQuotientWeight n k := by
        simp only [trigQuotientWeight]
        congr 1
        apply propext
        omega
      rw [hw]
      push_cast
      ring
    rw [sum_range_succ, sum_range_succ, sum_congr rfl hterm, sum_neg_distrib]
    have h₁ : trigQuotientWeight k (k + 2) = 0 := by
      simp only [trigQuotientWeight]
      rw [ite_eq_right_iff.mpr fun h' ↦ absurd h'.2 (by omega)]
    have h₂ : trigQuotientWeight (k + 1) (k + 2) = 2 := by
      simp only [trigQuotientWeight]
      rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_right_iff.mpr fun h' ↦ absurd h' (by omega)]
    have h₃ : trigQuotientSign (k + 1) (k + 2) = 1 := by
      simp [trigQuotientSign]
    rw [h₁, h₂, h₃, zero_mul, Int.cast_zero, zero_mul, add_zero, mul_add, mul_neg, ih hk]
    have hk2 : ((k + 2 : ℕ) : ℝ) * x = ((k + 1 : ℕ) : ℝ) * x + x := by push_cast; ring
    have hk0 : (k : ℝ) * x = ((k + 1 : ℕ) : ℝ) * x - x := by push_cast; ring
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, trigMode_zero]
      rw [hk2, hk0, Real.cos_add, Real.cos_sub]
      push_cast
      ring
    · simp only [Fin.mk_one, Fin.isValue, trigMode_one]
      rw [hk2, hk0, Real.sin_add, Real.sin_sub]
      push_cast
      ring

/-- The same identity with any range containing the frequencies below `k`. -/
theorem cos_mul_sum_range_trigQuotientWeight (i : Fin 2) {k N : ℕ} (hik : (i.val + k) % 2 = 1)
    (hk : k ≤ N) (x : ℝ) :
    Real.cos x * ∑ n ∈ range N,
      ((trigQuotientWeight n k * trigQuotientSign n k : ℤ) : ℝ) * trigMode i (n * x) =
      trigMode i (k * x) := by
  rw [← cos_mul_sum_trigQuotientWeight i k hik x, ← sum_subset (range_subset_range.mpr hk)
    fun n _ hn ↦ by rw [trigQuotientWeight_eq_zero (by simpa using hn)]; simp]

/-! ### Parity through a weight -/

/-- The sine vanishes only at the countably many points `nπ`. -/
theorem dense_sin_ne_zero : Dense {x : ℝ | Real.sin x ≠ 0} := by
  have hc : {x : ℝ | Real.sin x = 0}.Countable :=
    (Set.countable_range fun n : ℤ ↦ (n : ℝ) * Real.pi).mono fun x hx ↦
      Real.sin_eq_zero_iff.mp hx
  simpa only [Set.compl_ofPred] using hc.dense_compl ℝ

/-- The cosine vanishes only at the countably many points `nπ - π/2`. -/
theorem dense_cos_ne_zero : Dense {x : ℝ | Real.cos x ≠ 0} := by
  have hc : {x : ℝ | Real.cos x = 0}.Countable :=
    (Set.countable_range fun n : ℤ ↦ (n : ℝ) * Real.pi - Real.pi / 2).mono fun x hx ↦ by
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp
        (show Real.sin (x + Real.pi / 2) = 0 by rw [Real.sin_add_pi_div_two]; exact hx)
      exact ⟨n, by simp only; linarith⟩
  simpa only [Set.compl_ofPred] using hc.dense_compl ℝ

theorem isOddAt_zero_sin : IsOddAt 0 Real.sin := fun x ↦ by simp [Real.sin_neg]

theorem isEvenAt_pi_div_two_sin : IsEvenAt (Real.pi / 2) Real.sin := fun x ↦ by
  rw [show 2 * (Real.pi / 2) - x = Real.pi - x by ring, Real.sin_pi_sub]

theorem isEvenAt_zero_cos : IsEvenAt 0 Real.cos := fun x ↦ by simp [Real.cos_neg]

theorem isOddAt_pi_div_two_cos : IsOddAt (Real.pi / 2) Real.cos := fun x ↦ by
  rw [show 2 * (Real.pi / 2) - x = Real.pi - x by ring, Real.cos_pi_sub]

/-- If `f · w = g` with `f` continuous and `w` nonzero on a dense set, `f` is even about `a`
when `w` and `g` have the same parity there. -/
theorem IsEvenAt.of_mul_eq {a : ℝ} {f w g : ℝ → ℝ} (hf : Continuous f)
    (hw : Dense {x | w x ≠ 0}) (hfg : ∀ x, f x * w x = g x)
    (h : (IsEvenAt a w ∧ IsEvenAt a g) ∨ (IsOddAt a w ∧ IsOddAt a g)) : IsEvenAt a f := by
  have heq := Continuous.ext_on hw (hf.comp (continuous_const.sub continuous_id)) hf
    fun x (hx : w x ≠ 0) ↦ by
      have h₁ := hfg (2 * a - x)
      rcases h with ⟨hw', hg'⟩ | ⟨hw', hg'⟩
      · rw [hw' x, hg' x, ← hfg x] at h₁
        exact mul_right_cancel₀ hx h₁
      · rw [hw' x, hg' x, ← hfg x, mul_neg, neg_inj] at h₁
        exact mul_right_cancel₀ hx h₁
  exact fun x ↦ congrFun heq x

/-- If `f · w = g` with `f` continuous and `w` nonzero on a dense set, `f` is odd about `a`
when `w` and `g` have opposite parities there. -/
theorem IsOddAt.of_mul_eq {a : ℝ} {f w g : ℝ → ℝ} (hf : Continuous f)
    (hw : Dense {x | w x ≠ 0}) (hfg : ∀ x, f x * w x = g x)
    (h : (IsEvenAt a w ∧ IsOddAt a g) ∨ (IsOddAt a w ∧ IsEvenAt a g)) : IsOddAt a f := by
  have heq := Continuous.ext_on hw (hf.comp (continuous_const.sub continuous_id)) hf.neg
    fun x (hx : w x ≠ 0) ↦ by
      have h₁ := hfg (2 * a - x)
      change f (2 * a - x) = -f x
      rcases h with ⟨hw', hg'⟩ | ⟨hw', hg'⟩
      · rw [hw' x, hg' x, ← hfg x] at h₁
        exact mul_right_cancel₀ hx (by linarith)
      · rw [hw' x, hg' x, ← hfg x] at h₁
        exact mul_right_cancel₀ hx (by linarith)
  exact fun x ↦ congrFun heq x

/-- The sine quotient weights expand the Chebyshev quotient `sineQuotient (k - 1)`, the smooth
extension of `sin (kx) / sin x`. -/
theorem sum_trigQuotientWeight_mul_cos_eq_sineQuotient (k : ℕ) (x : ℝ) :
    ∑ n ∈ range (k + 1), (trigQuotientWeight n (k + 1) : ℝ) * Real.cos (n * x) =
      sineQuotient k x := by
  have hc : Continuous fun x : ℝ ↦
      ∑ n ∈ range (k + 1), (trigQuotientWeight n (k + 1) : ℝ) * Real.cos (n * x) := by
    fun_prop
  refine congrFun (Continuous.ext_on dense_sin_ne_zero hc
    (contDiff_sineQuotient k).continuous fun x (hx : Real.sin x ≠ 0) ↦ ?_) x
  refine mul_left_cancel₀ hx ?_
  rw [sin_mul_sum_trigQuotientWeight, mul_comm (Real.sin x), sineQuotient_mul_sin]
  push_cast
  ring_nf

/-- The cosine quotient weights expand `oddCosineQuotient m`, the smooth extension of
`cos ((2m+1) x) / cos x`. -/
theorem sum_trigQuotientWeight_mul_cos_eq_oddCosineQuotient (m : ℕ) (x : ℝ) :
    ∑ n ∈ range (2 * m + 1),
      ((trigQuotientWeight n (2 * m + 1) * trigQuotientSign n (2 * m + 1) : ℤ) : ℝ) *
        Real.cos (n * x) = oddCosineQuotient m x := by
  have hc : Continuous fun x : ℝ ↦ ∑ n ∈ range (2 * m + 1),
      ((trigQuotientWeight n (2 * m + 1) * trigQuotientSign n (2 * m + 1) : ℤ) : ℝ) *
        Real.cos (n * x) := by
    fun_prop
  refine congrFun (Continuous.ext_on dense_cos_ne_zero hc
    (contDiff_oddCosineQuotient m).continuous fun x (hx : Real.cos x ≠ 0) ↦ ?_) x
  refine mul_left_cancel₀ hx ?_
  have h := cos_mul_sum_trigQuotientWeight 0 (2 * m + 1) (by simp) x
  simp only [trigMode_zero] at h
  rw [h, cos_mul_oddCosineQuotient]
  push_cast
  ring_nf

/-! ### Quotient tables -/

namespace TrigPoly2

variable {Mβ Mθ : ℕ} {R : Type}

theorem coeffN_eq_zero_of_le_β [Zero R] (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) {k : ℕ} (l : ℕ)
    (hk : Mβ + 1 ≤ k) : p.coeffN i j k l = 0 :=
  dite_eq_right_iff.mpr fun h ↦ absurd h.1 (by omega)

theorem coeffN_eq_zero_of_le_θ [Zero R] (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k : ℕ) {l : ℕ}
    (hl : Mθ + 1 ≤ l) : p.coeffN i j k l = 0 :=
  dite_eq_right_iff.mpr fun h ↦ absurd h.2 (by omega)

variable [Field R]

/-- The quotient by `sin β` of a table without cosines in `β`: each `sin (kβ)` becomes
`∑_{n < k} w(n, k) cos (nβ)`. The degree in `β` drops by one. -/
def divSinβ (p : TrigPoly2 Mβ Mθ R) : TrigPoly2 (Mβ - 1) Mθ R :=
  ⟨fun i j n l ↦ if i = 0 then
    ∑ k ∈ range (Mβ + 1), (trigQuotientWeight n k : R) * p.coeffN 1 j k l else 0⟩

/-- The quotient by `sin θ` of a table without cosines in `θ`. -/
def divSinθ (p : TrigPoly2 Mβ Mθ R) : TrigPoly2 Mβ (Mθ - 1) R :=
  ⟨fun i j k n ↦ if j = 0 then
    ∑ l ∈ range (Mθ + 1), (trigQuotientWeight n l : R) * p.coeffN i 1 k l else 0⟩

/-- The quotient by `cos β` of a table odd about `π/2` in `β` (no `cos (kβ)` with `k` even and
no `sin (kβ)` with `k` odd): each mode `m_i (kβ)` becomes `∑_{n < k} w(n, k) σ(n, k) m_i (nβ)`. -/
def divCosβ (p : TrigPoly2 Mβ Mθ R) : TrigPoly2 (Mβ - 1) Mθ R :=
  ⟨fun i j n l ↦ ∑ k ∈ range (Mβ + 1),
    ((trigQuotientWeight n k * trigQuotientSign n k : ℤ) : R) * p.coeffN i j k l⟩

/-- The quotient by `cos θ` of a table odd about `π/2` in `θ`. -/
def divCosθ (p : TrigPoly2 Mβ Mθ R) : TrigPoly2 Mβ (Mθ - 1) R :=
  ⟨fun i j k n ↦ ∑ l ∈ range (Mθ + 1),
    ((trigQuotientWeight n l * trigQuotientSign n l : ℤ) : R) * p.coeffN i j k l⟩

theorem coeffN_divSinβ (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (n l : ℕ) :
    (divSinβ p).coeffN i j n l = if i = 0 then
      ∑ k ∈ range (Mβ + 1), (trigQuotientWeight n k : R) * p.coeffN 1 j k l else 0 := by
  by_cases h : n < Mβ - 1 + 1 ∧ l < Mθ + 1
  · rw [coeffN, dite_eq_left_of_eq_true (eq_true h)]
    rfl
  · rw [coeffN, dite_eq_right_of_eq_false (eq_false h)]
    split_ifs
    · refine (sum_eq_zero fun k hk ↦ ?_).symm
      have hk' := mem_range.mp hk
      rcases not_and_or.mp h with hn | hl
      · rw [trigQuotientWeight_eq_zero (by omega), Int.cast_zero, zero_mul]
      · rw [coeffN_eq_zero_of_le_θ p 1 j k (by omega), mul_zero]
    · rfl

theorem coeffN_divSinθ (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k n : ℕ) :
    (divSinθ p).coeffN i j k n = if j = 0 then
      ∑ l ∈ range (Mθ + 1), (trigQuotientWeight n l : R) * p.coeffN i 1 k l else 0 := by
  by_cases h : k < Mβ + 1 ∧ n < Mθ - 1 + 1
  · rw [coeffN, dite_eq_left_of_eq_true (eq_true h)]
    rfl
  · rw [coeffN, dite_eq_right_of_eq_false (eq_false h)]
    split_ifs
    · refine (sum_eq_zero fun l hl ↦ ?_).symm
      have hl' := mem_range.mp hl
      rcases not_and_or.mp h with hk | hn
      · rw [coeffN_eq_zero_of_le_β p i 1 l (by omega), mul_zero]
      · rw [trigQuotientWeight_eq_zero (by omega), Int.cast_zero, zero_mul]
    · rfl

theorem coeffN_divCosβ (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (n l : ℕ) :
    (divCosβ p).coeffN i j n l = ∑ k ∈ range (Mβ + 1),
      ((trigQuotientWeight n k * trigQuotientSign n k : ℤ) : R) * p.coeffN i j k l := by
  by_cases h : n < Mβ - 1 + 1 ∧ l < Mθ + 1
  · rw [coeffN, dite_eq_left_of_eq_true (eq_true h)]
    rfl
  · rw [coeffN, dite_eq_right_of_eq_false (eq_false h)]
    refine (sum_eq_zero fun k hk ↦ ?_).symm
    have hk' := mem_range.mp hk
    rcases not_and_or.mp h with hn | hl
    · rw [trigQuotientWeight_eq_zero (by omega), zero_mul, Int.cast_zero, zero_mul]
    · rw [coeffN_eq_zero_of_le_θ p i j k (by omega), mul_zero]

theorem coeffN_divCosθ (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k n : ℕ) :
    (divCosθ p).coeffN i j k n = ∑ l ∈ range (Mθ + 1),
      ((trigQuotientWeight n l * trigQuotientSign n l : ℤ) : R) * p.coeffN i j k l := by
  by_cases h : k < Mβ + 1 ∧ n < Mθ - 1 + 1
  · rw [coeffN, dite_eq_left_of_eq_true (eq_true h)]
    rfl
  · rw [coeffN, dite_eq_right_of_eq_false (eq_false h)]
    refine (sum_eq_zero fun l hl ↦ ?_).symm
    have hl' := mem_range.mp hl
    rcases not_and_or.mp h with hk | hn
    · rw [coeffN_eq_zero_of_le_β p i j l (by omega), mul_zero]
    · rw [trigQuotientWeight_eq_zero (by omega), zero_mul, Int.cast_zero, zero_mul]

variable [Algebra R ℝ]

/-- One summation step behind all quotient identities: if `B k = wt · ∑_n W n k A n` wherever the
coefficient `c k` is nonzero, then dividing the coefficients by the weights `W` and multiplying
by `wt` restores the series. -/
private theorem sum_quotient_mul (A B : ℕ → ℝ) (W : ℕ → ℕ → ℤ) (wt G : ℝ) (c : ℕ → R)
    (K N : ℕ) (hid : ∀ k ∈ range K, algebraMap R ℝ (c k) * B k =
      algebraMap R ℝ (c k) * (wt * ∑ n ∈ range N, (W n k : ℝ) * A n)) :
    (∑ n ∈ range N, algebraMap R ℝ (∑ k ∈ range K, (W n k : R) * c k) * A n * G) * wt =
      ∑ k ∈ range K, algebraMap R ℝ (c k) * B k * G := by
  have hR : ∑ k ∈ range K, algebraMap R ℝ (c k) * B k * G = ∑ k ∈ range K,
      algebraMap R ℝ (c k) * (wt * ∑ n ∈ range N, (W n k : ℝ) * A n) * G :=
    sum_congr rfl fun k hk ↦ by rw [hid k hk]
  rw [hR]
  simp only [map_sum, map_mul, map_intCast, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun k _ ↦ sum_congr rfl fun n _ ↦ by ring

/-- `sum_quotient_mul` with the fixed factor `G` before the mode. -/
private theorem sum_quotient_mul' (A B : ℕ → ℝ) (W : ℕ → ℕ → ℤ) (wt G : ℝ) (c : ℕ → R)
    (K N : ℕ) (hid : ∀ k ∈ range K, algebraMap R ℝ (c k) * B k =
      algebraMap R ℝ (c k) * (wt * ∑ n ∈ range N, (W n k : ℝ) * A n)) :
    (∑ n ∈ range N, algebraMap R ℝ (∑ k ∈ range K, (W n k : R) * c k) * G * A n) * wt =
      ∑ k ∈ range K, algebraMap R ℝ (c k) * G * B k := by
  have h := sum_quotient_mul A B W wt G c K N hid
  simp only [mul_right_comm _ G] at h ⊢
  exact h

omit [Algebra R ℝ] in
private theorem coeffN_eq_zero_of_coeff {p : TrigPoly2 Mβ Mθ R} {P : Fin 2 → Fin 2 → ℕ → ℕ → Prop}
    (h : ∀ i j (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)), P i j k l → p.coeff i j k l = 0)
    (i j : Fin 2) (k l : ℕ) (hP : P i j k l) : p.coeffN i j k l = 0 := by
  unfold coeffN
  split_ifs with hkl
  · exact h i j ⟨k, hkl.1⟩ ⟨l, hkl.2⟩ hP
  · rfl

/-- Without cosines in `β`, `divSinβ p · sin β = p`. -/
theorem eval_divSinβ_mul_sin (p : TrigPoly2 Mβ Mθ R) (h : ∀ j k l, p.coeff 0 j k l = 0)
    (β θ : ℝ) : (divSinβ p).eval β θ * Real.sin β = p.eval β θ := by
  have hp0 : ∀ j (k l : ℕ), p.coeffN 0 j k l = 0 := fun j k l ↦
    coeffN_eq_zero_of_coeff (P := fun i _ _ _ ↦ i = 0) (fun _ j k l hi ↦ hi ▸ h j k l) 0 j k l
      rfl
  have key : ∀ j : Fin 2, (∑ n ∈ range (Mβ - 1 + 1), ∑ l ∈ range (Mθ + 1),
      algebraMap R ℝ (∑ k ∈ range (Mβ + 1), (trigQuotientWeight n k : R) * p.coeffN 1 j k l) *
        trigMode 0 (n * β) * trigMode j (l * θ)) * Real.sin β =
      ∑ k ∈ range (Mβ + 1), ∑ l ∈ range (Mθ + 1),
        algebraMap R ℝ (p.coeffN 1 j k l) * trigMode 1 (k * β) * trigMode j (l * θ) := by
    intro j
    conv_lhs => rw [sum_comm]
    conv_rhs => rw [sum_comm]
    rw [sum_mul]
    refine sum_congr rfl fun l _ ↦ sum_quotient_mul _ _ _ _ _ _ _ _ fun k hk ↦ ?_
    simp only [trigMode_zero, trigMode_one]
    rw [sin_mul_sum_range_trigQuotientWeight (by have := mem_range.mp hk; omega)]
  rw [eval_eq_sum_range, eval_eq_sum_range]
  simp only [Fin.sum_univ_two, coeffN_divSinβ, hp0, Fin.isValue, ↓reduceIte, one_ne_zero,
    map_zero, zero_mul, sum_const_zero, add_zero, zero_add]
  rw [add_mul, key 0, key 1]

/-- Without cosines in `θ`, `divSinθ p · sin θ = p`. -/
theorem eval_divSinθ_mul_sin (p : TrigPoly2 Mβ Mθ R) (h : ∀ i k l, p.coeff i 0 k l = 0)
    (β θ : ℝ) : (divSinθ p).eval β θ * Real.sin θ = p.eval β θ := by
  have hp0 : ∀ i (k l : ℕ), p.coeffN i 0 k l = 0 := fun i k l ↦
    coeffN_eq_zero_of_coeff (P := fun _ j _ _ ↦ j = 0) (fun i _ k l hj ↦ hj ▸ h i k l) i 0 k l
      rfl
  rw [eval_eq_sum_range, eval_eq_sum_range, sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [coeffN_divSinθ, hp0, Fin.isValue, ↓reduceIte, one_ne_zero, map_zero, zero_mul,
    sum_const_zero, add_zero, zero_add, sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← sum_mul]
  refine sum_quotient_mul' _ _ _ _ _ _ _ _ fun l hl ↦ ?_
  simp only [trigMode_zero, trigMode_one]
  rw [sin_mul_sum_range_trigQuotientWeight (by have := mem_range.mp hl; omega)]

/-- Odd about `π/2` in `β`, `divCosβ p · cos β = p`. -/
theorem eval_divCosβ_mul_cos (p : TrigPoly2 Mβ Mθ R)
    (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0) (β θ : ℝ) :
    (divCosβ p).eval β θ * Real.cos β = p.eval β θ := by
  have hp : ∀ i j (k l : ℕ), (i.val + k) % 2 = 0 → p.coeffN i j k l = 0 := fun i j k l ↦
    coeffN_eq_zero_of_coeff (P := fun i _ k _ ↦ (i.val + k) % 2 = 0)
      (fun i j k l he ↦ h i j k l (Nat.even_iff.mpr he)) i j k l
  rw [eval_eq_sum_range, eval_eq_sum_range, sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun j _ ↦ ?_
  simp only [coeffN_divCosβ]
  conv_lhs => rw [sum_comm]
  conv_rhs => rw [sum_comm]
  rw [sum_mul]
  refine sum_congr rfl fun l _ ↦ sum_quotient_mul _ _ _ _ _ _ _ _ fun k hk ↦ ?_
  rcases Nat.mod_two_eq_zero_or_one (i.val + k) with he | ho
  · rw [hp i j k l he, map_zero, zero_mul, zero_mul]
  · rw [cos_mul_sum_range_trigQuotientWeight i ho (by have := mem_range.mp hk; omega)]

/-- Odd about `π/2` in `θ`, `divCosθ p · cos θ = p`. -/
theorem eval_divCosθ_mul_cos (p : TrigPoly2 Mβ Mθ R)
    (h : ∀ i j k l, Even (j.val + l.val) → p.coeff i j k l = 0) (β θ : ℝ) :
    (divCosθ p).eval β θ * Real.cos θ = p.eval β θ := by
  have hp : ∀ i j (k l : ℕ), (j.val + l) % 2 = 0 → p.coeffN i j k l = 0 := fun i j k l ↦
    coeffN_eq_zero_of_coeff (P := fun _ j _ l ↦ (j.val + l) % 2 = 0)
      (fun i j k l he ↦ h i j k l (Nat.even_iff.mpr he)) i j k l
  rw [eval_eq_sum_range, eval_eq_sum_range, sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [coeffN_divCosθ]
  refine sum_quotient_mul' _ _ _ _ _ _ _ _ fun l hl ↦ ?_
  rcases Nat.mod_two_eq_zero_or_one (j.val + l) with he | ho
  · rw [hp i j k l he, map_zero, zero_mul, zero_mul]
  · rw [cos_mul_sum_range_trigQuotientWeight j ho (by have := mem_range.mp hl; omega)]

/-- Where `sin β ≠ 0`, `divSinβ p` is the quotient `p / sin β`. -/
theorem eval_divSinβ_eq_div (p : TrigPoly2 Mβ Mθ R) (h : ∀ j k l, p.coeff 0 j k l = 0) {β : ℝ}
    (hβ : Real.sin β ≠ 0) (θ : ℝ) : (divSinβ p).eval β θ = p.eval β θ / Real.sin β :=
  (eq_div_iff hβ).mpr (eval_divSinβ_mul_sin p h β θ)

/-- Where `sin θ ≠ 0`, `divSinθ p` is the quotient `p / sin θ`. -/
theorem eval_divSinθ_eq_div (p : TrigPoly2 Mβ Mθ R) (h : ∀ i k l, p.coeff i 0 k l = 0) (β : ℝ)
    {θ : ℝ} (hθ : Real.sin θ ≠ 0) : (divSinθ p).eval β θ = p.eval β θ / Real.sin θ :=
  (eq_div_iff hθ).mpr (eval_divSinθ_mul_sin p h β θ)

/-- Where `cos β ≠ 0`, `divCosβ p` is the quotient `p / cos β`. -/
theorem eval_divCosβ_eq_div (p : TrigPoly2 Mβ Mθ R)
    (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0) {β : ℝ}
    (hβ : Real.cos β ≠ 0) (θ : ℝ) : (divCosβ p).eval β θ = p.eval β θ / Real.cos β :=
  (eq_div_iff hβ).mpr (eval_divCosβ_mul_cos p h β θ)

/-- Where `cos θ ≠ 0`, `divCosθ p` is the quotient `p / cos θ`. -/
theorem eval_divCosθ_eq_div (p : TrigPoly2 Mβ Mθ R)
    (h : ∀ i j k l, Even (j.val + l.val) → p.coeff i j k l = 0) (β : ℝ) {θ : ℝ}
    (hθ : Real.cos θ ≠ 0) : (divCosθ p).eval β θ = p.eval β θ / Real.cos θ :=
  (eq_div_iff hθ).mpr (eval_divCosθ_mul_cos p h β θ)

/-! ### Parities of quotient tables -/

section Parity

variable {Nβ Nθ : ℕ} {a : ℝ}

/-- If `q (β, θ) · w β = p (β, θ)` with `w` nonzero on a dense set, `q` is even in `θ` where `p`
is. -/
theorem IsEvenAtθ.of_eval_mul_β {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R} {w : ℝ → ℝ}
    (hw : Dense {β | w β ≠ 0}) (h : ∀ β θ, q.eval β θ * w β = p.eval β θ)
    (hp : p.IsEvenAtθ a) : q.IsEvenAtθ a := fun β x ↦
  congrFun (Continuous.ext_on hw (q.continuous_eval_β (2 * a - x)) (q.continuous_eval_β x)
    fun β (hβ : w β ≠ 0) ↦ mul_right_cancel₀ hβ (by rw [h, h, hp β x])) β

/-- If `q (β, θ) · w β = p (β, θ)` with `w` nonzero on a dense set, `q` is odd in `θ` where `p`
is. -/
theorem IsOddAtθ.of_eval_mul_β {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R} {w : ℝ → ℝ}
    (hw : Dense {β | w β ≠ 0}) (h : ∀ β θ, q.eval β θ * w β = p.eval β θ)
    (hp : p.IsOddAtθ a) : q.IsOddAtθ a := fun β x ↦
  congrFun (Continuous.ext_on hw (q.continuous_eval_β (2 * a - x)) (q.continuous_eval_β x).neg
    fun β (hβ : w β ≠ 0) ↦ mul_right_cancel₀ hβ (by
      change q.eval β (2 * a - x) * w β = -q.eval β x * w β
      rw [h, neg_mul, h, hp β x])) β

/-- If `q (β, θ) · w θ = p (β, θ)` with `w` nonzero on a dense set, `q` is even in `β` where `p`
is. -/
theorem IsEvenAtβ.of_eval_mul_θ {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R} {w : ℝ → ℝ}
    (hw : Dense {θ | w θ ≠ 0}) (h : ∀ β θ, q.eval β θ * w θ = p.eval β θ)
    (hp : p.IsEvenAtβ a) : q.IsEvenAtβ a := fun θ x ↦
  congrFun (Continuous.ext_on hw (q.continuous_eval_θ (2 * a - x)) (q.continuous_eval_θ x)
    fun θ (hθ : w θ ≠ 0) ↦ mul_right_cancel₀ hθ (by rw [h, h]; exact hp θ x)) θ

/-- If `q (β, θ) · w θ = p (β, θ)` with `w` nonzero on a dense set, `q` is odd in `β` where `p`
is. -/
theorem IsOddAtβ.of_eval_mul_θ {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R} {w : ℝ → ℝ}
    (hw : Dense {θ | w θ ≠ 0}) (h : ∀ β θ, q.eval β θ * w θ = p.eval β θ)
    (hp : p.IsOddAtβ a) : q.IsOddAtβ a := fun θ x ↦
  congrFun (Continuous.ext_on hw (q.continuous_eval_θ (2 * a - x)) (q.continuous_eval_θ x).neg
    fun θ (hθ : w θ ≠ 0) ↦ mul_right_cancel₀ hθ (by
      change q.eval (2 * a - x) θ * w θ = -q.eval x θ * w θ
      rw [h, neg_mul, h]
      exact hp θ x)) θ

variable {p : TrigPoly2 Mβ Mθ R}

/-- The quotient by `sin β` has no sines in `β`. -/
theorem isEvenAtβ_zero_divSinβ (p : TrigPoly2 Mβ Mθ R) : (divSinβ p).IsEvenAtβ 0 :=
  isEvenAtβ_zero_of_coeff fun _ _ _ ↦ by simp [divSinβ]

/-- The quotient by `sin θ` has no sines in `θ`. -/
theorem isEvenAtθ_zero_divSinθ (p : TrigPoly2 Mβ Mθ R) : (divSinθ p).IsEvenAtθ 0 :=
  isEvenAtθ_zero_of_coeff fun _ _ _ ↦ by simp [divSinθ]

theorem isEvenAtβ_pi_div_two_divSinβ (h : ∀ j k l, p.coeff 0 j k l = 0)
    (hp : p.IsEvenAtβ (Real.pi / 2)) : (divSinβ p).IsEvenAtβ (Real.pi / 2) := fun θ ↦
  IsEvenAt.of_mul_eq ((divSinβ p).continuous_eval_β θ) dense_sin_ne_zero
    (fun β ↦ eval_divSinβ_mul_sin p h β θ) (Or.inl ⟨isEvenAt_pi_div_two_sin, hp θ⟩)

theorem isOddAtβ_pi_div_two_divSinβ (h : ∀ j k l, p.coeff 0 j k l = 0)
    (hp : p.IsOddAtβ (Real.pi / 2)) : (divSinβ p).IsOddAtβ (Real.pi / 2) := fun θ ↦
  IsOddAt.of_mul_eq ((divSinβ p).continuous_eval_β θ) dense_sin_ne_zero
    (fun β ↦ eval_divSinβ_mul_sin p h β θ) (Or.inl ⟨isEvenAt_pi_div_two_sin, hp θ⟩)

theorem isEvenAtθ_pi_div_two_divSinθ (h : ∀ i k l, p.coeff i 0 k l = 0)
    (hp : p.IsEvenAtθ (Real.pi / 2)) : (divSinθ p).IsEvenAtθ (Real.pi / 2) := fun β ↦
  IsEvenAt.of_mul_eq ((divSinθ p).continuous_eval_θ β) dense_sin_ne_zero
    (fun θ ↦ eval_divSinθ_mul_sin p h β θ) (Or.inl ⟨isEvenAt_pi_div_two_sin, hp β⟩)

theorem isOddAtθ_pi_div_two_divSinθ (h : ∀ i k l, p.coeff i 0 k l = 0)
    (hp : p.IsOddAtθ (Real.pi / 2)) : (divSinθ p).IsOddAtθ (Real.pi / 2) := fun β ↦
  IsOddAt.of_mul_eq ((divSinθ p).continuous_eval_θ β) dense_sin_ne_zero
    (fun θ ↦ eval_divSinθ_mul_sin p h β θ) (Or.inl ⟨isEvenAt_pi_div_two_sin, hp β⟩)

/-- The quotient by `cos β` of a table odd about `π/2` in `β` is even there. -/
theorem isEvenAtβ_pi_div_two_divCosβ
    (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0) :
    (divCosβ p).IsEvenAtβ (Real.pi / 2) := fun θ ↦
  IsEvenAt.of_mul_eq ((divCosβ p).continuous_eval_β θ) dense_cos_ne_zero
    (fun β ↦ eval_divCosβ_mul_cos p h β θ)
    (Or.inr ⟨isOddAt_pi_div_two_cos, isOddAtβ_pi_div_two_of_coeff h θ⟩)

/-- The quotient by `cos θ` of a table odd about `π/2` in `θ` is even there. -/
theorem isEvenAtθ_pi_div_two_divCosθ
    (h : ∀ i j k l, Even (j.val + l.val) → p.coeff i j k l = 0) :
    (divCosθ p).IsEvenAtθ (Real.pi / 2) := fun β ↦
  IsEvenAt.of_mul_eq ((divCosθ p).continuous_eval_θ β) dense_cos_ne_zero
    (fun θ ↦ eval_divCosθ_mul_cos p h β θ)
    (Or.inr ⟨isOddAt_pi_div_two_cos, isOddAtθ_pi_div_two_of_coeff h β⟩)

theorem isEvenAtβ_zero_divCosβ (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0)
    (hp : p.IsEvenAtβ 0) : (divCosβ p).IsEvenAtβ 0 := fun θ ↦
  IsEvenAt.of_mul_eq ((divCosβ p).continuous_eval_β θ) dense_cos_ne_zero
    (fun β ↦ eval_divCosβ_mul_cos p h β θ) (Or.inl ⟨isEvenAt_zero_cos, hp θ⟩)

theorem isOddAtβ_zero_divCosβ (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0)
    (hp : p.IsOddAtβ 0) : (divCosβ p).IsOddAtβ 0 := fun θ ↦
  IsOddAt.of_mul_eq ((divCosβ p).continuous_eval_β θ) dense_cos_ne_zero
    (fun β ↦ eval_divCosβ_mul_cos p h β θ) (Or.inl ⟨isEvenAt_zero_cos, hp θ⟩)

theorem isEvenAtθ_zero_divCosθ (h : ∀ i j k l, Even (j.val + l.val) → p.coeff i j k l = 0)
    (hp : p.IsEvenAtθ 0) : (divCosθ p).IsEvenAtθ 0 := fun β ↦
  IsEvenAt.of_mul_eq ((divCosθ p).continuous_eval_θ β) dense_cos_ne_zero
    (fun θ ↦ eval_divCosθ_mul_cos p h β θ) (Or.inl ⟨isEvenAt_zero_cos, hp β⟩)

theorem isOddAtθ_zero_divCosθ (h : ∀ i j k l, Even (j.val + l.val) → p.coeff i j k l = 0)
    (hp : p.IsOddAtθ 0) : (divCosθ p).IsOddAtθ 0 := fun β ↦
  IsOddAt.of_mul_eq ((divCosθ p).continuous_eval_θ β) dense_cos_ne_zero
    (fun θ ↦ eval_divCosθ_mul_cos p h β θ) (Or.inl ⟨isEvenAt_zero_cos, hp β⟩)

/-- Division by `sin β` keeps the parities in `θ`. -/
theorem IsEvenAtθ.divSinβ (h : ∀ j k l, p.coeff 0 j k l = 0) (hp : p.IsEvenAtθ a) :
    (divSinβ p).IsEvenAtθ a :=
  IsEvenAtθ.of_eval_mul_β dense_sin_ne_zero (eval_divSinβ_mul_sin p h) hp

theorem IsOddAtθ.divSinβ (h : ∀ j k l, p.coeff 0 j k l = 0) (hp : p.IsOddAtθ a) :
    (divSinβ p).IsOddAtθ a :=
  IsOddAtθ.of_eval_mul_β dense_sin_ne_zero (eval_divSinβ_mul_sin p h) hp

/-- Division by `cos β` keeps the parities in `θ`. -/
theorem IsEvenAtθ.divCosβ (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0)
    (hp : p.IsEvenAtθ a) : (divCosβ p).IsEvenAtθ a :=
  IsEvenAtθ.of_eval_mul_β dense_cos_ne_zero (eval_divCosβ_mul_cos p h) hp

theorem IsOddAtθ.divCosβ (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0)
    (hp : p.IsOddAtθ a) : (divCosβ p).IsOddAtθ a :=
  IsOddAtθ.of_eval_mul_β dense_cos_ne_zero (eval_divCosβ_mul_cos p h) hp

/-- Division by `sin θ` keeps the parities in `β`. -/
theorem IsEvenAtβ.divSinθ (h : ∀ i k l, p.coeff i 0 k l = 0) (hp : p.IsEvenAtβ a) :
    (divSinθ p).IsEvenAtβ a :=
  IsEvenAtβ.of_eval_mul_θ dense_sin_ne_zero (eval_divSinθ_mul_sin p h) hp

theorem IsOddAtβ.divSinθ (h : ∀ i k l, p.coeff i 0 k l = 0) (hp : p.IsOddAtβ a) :
    (divSinθ p).IsOddAtβ a :=
  IsOddAtβ.of_eval_mul_θ dense_sin_ne_zero (eval_divSinθ_mul_sin p h) hp

/-- Division by `cos θ` keeps the parities in `β`. -/
theorem IsEvenAtβ.divCosθ (h : ∀ i j k l, Even (j.val + l.val) → p.coeff i j k l = 0)
    (hp : p.IsEvenAtβ a) : (divCosθ p).IsEvenAtβ a :=
  IsEvenAtβ.of_eval_mul_θ dense_cos_ne_zero (eval_divCosθ_mul_cos p h) hp

theorem IsOddAtβ.divCosθ (h : ∀ i j k l, Even (j.val + l.val) → p.coeff i j k l = 0)
    (hp : p.IsOddAtβ a) : (divCosθ p).IsOddAtβ a :=
  IsOddAtβ.of_eval_mul_θ dense_cos_ne_zero (eval_divCosθ_mul_cos p h) hp

end Parity

end TrigPoly2

end PDE.Analysis
