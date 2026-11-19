/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Quotient

/-!
# The sine-quotient weights by parity

The weights of `sin (k x) / sin x = Σ_{n<k} w(n, k) cos (n x)` select the frequencies of the
other parity: `Σ_{n<2j} w(n, 2j) f n = Σ_{s<j} 2 f (2s+1)` (`sum_range_trigQuotientWeight_even`)
and `Σ_{n<2l+1} w(n, 2l+1) f n = f 0 + Σ_{s<l} 2 f (2s+2)` (`sum_range_trigQuotientWeight_odd`).
Regrouped by the frequencies of the result, a series `Σ_j c_j 2j sin (2jx) / sin x` has the
coefficient `Σ_{j>s} 4j c_j` at `cos ((2s+1) x)` (`sum_mul_two_mul_quotient_even`), and
`sin ((2l+1) x) / sin x` has the coefficients `1, 2, …, 2, 0, …` at the even frequencies
(`sum_quotient_odd_eq`).
-/

@[expose] public section
namespace PDE.Analysis

open Finset

/-- The quotient weights of an even frequency:
`sin (2j x) / sin x = 2 Σ_{s<j} cos ((2s+1) x)`. -/
theorem sum_range_trigQuotientWeight_even (j : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ range (2 * j), (trigQuotientWeight n (2 * j) : ℝ) * f n =
      ∑ s ∈ range j, 2 * f (2 * s + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hw : ∀ n ∈ range (2 * j),
        trigQuotientWeight n (2 * (j + 1)) = trigQuotientWeight n (2 * j) := by
      intro n hn
      have := mem_range.mp hn
      simp only [trigQuotientWeight]
      congr 1
      apply propext
      constructor <;> intro ⟨h1, h2⟩ <;> refine ⟨by omega, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_congr rfl (fun n hn ↦ by rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, hw n hn]), ih,
      sum_range_succ]
    have e1 : trigQuotientWeight (2 * j) (2 * j + 1 + 1) = 0 := by
      simp only [trigQuotientWeight]; split_ifs <;> omega
    have e2 : trigQuotientWeight (2 * j + 1) (2 * j + 1 + 1) = 2 := by
      have c1 : 2 * j + 1 < 2 * j + 1 + 1 ∧ (2 * j + 1 + 1 - (2 * j + 1)) % 2 = 1 :=
        ⟨by omega, by omega⟩
      have c2 : 2 * j + 1 ≠ 0 := by omega
      simp only [trigQuotientWeight, c1, c2, and_self, ↓reduceIte]
    rw [e1, e2]
    push_cast
    ring

/-- The quotient weights of an odd frequency:
`sin ((2l+1) x) / sin x = 1 + 2 Σ_{s<l} cos ((2s+2) x)`. -/
theorem sum_range_trigQuotientWeight_odd (l : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ range (2 * l + 1), (trigQuotientWeight n (2 * l + 1) : ℝ) * f n =
      f 0 + ∑ s ∈ range l, 2 * f (2 * s + 2) := by
  induction l with
  | zero => simp [trigQuotientWeight]
  | succ l ih =>
    have hw : ∀ n ∈ range (2 * l + 1),
        trigQuotientWeight n (2 * (l + 1) + 1) = trigQuotientWeight n (2 * l + 1) := by
      intro n hn
      have := mem_range.mp hn
      simp only [trigQuotientWeight]
      congr 1
      apply propext
      constructor <;> intro ⟨h1, h2⟩ <;> refine ⟨by omega, by omega⟩
    rw [show 2 * (l + 1) + 1 = 2 * l + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_congr rfl (fun n hn ↦ by rw [show 2 * l + 1 + 1 + 1 = 2 * (l + 1) + 1 by ring,
        hw n hn]), ih, sum_range_succ]
    have e1 : trigQuotientWeight (2 * l + 1) (2 * l + 1 + 1 + 1) = 0 := by
      simp only [trigQuotientWeight]; split_ifs <;> omega
    have e2 : trigQuotientWeight (2 * l + 1 + 1) (2 * l + 1 + 1 + 1) = 2 := by
      have c1 : 2 * l + 1 + 1 < 2 * l + 1 + 1 + 1 ∧
          (2 * l + 1 + 1 + 1 - (2 * l + 1 + 1)) % 2 = 1 := ⟨by omega, by omega⟩
      have c2 : 2 * l + 1 + 1 ≠ 0 := by omega
      simp only [trigQuotientWeight, c1, c2, and_self, ↓reduceIte]
    rw [e1, e2]
    push_cast
    rw [show 2 * l + 1 + 1 = 2 * l + 2 by ring]
    ring


/-- The quotient by `sin` of the even modes of an angular series, regrouped by the odd
frequencies: `Σ_j c_j 2j Σ_{n<2j} w(n, 2j) g n = Σ_{s<L} (Σ_{j>s} 4j c_j) g (2s+1)`. -/
theorem sum_mul_two_mul_quotient_even {L : ℕ} (c : Fin (L + 1) → ℝ) (g : ℕ → ℝ) :
    ∑ j : Fin (L + 1), c j * (2 * (j : ℝ) *
        ∑ n ∈ range (2 * j), (trigQuotientWeight n (2 * j) : ℝ) * g n) =
      ∑ s ∈ range L, (∑ j : Fin (L + 1), if s < (j : ℕ) then 4 * (j : ℝ) * c j else 0) *
        g (2 * s + 1) := by
  simp only [sum_range_trigQuotientWeight_even]
  have h : ∀ j : Fin (L + 1), c j * (2 * (j : ℝ) * ∑ s ∈ range j, 2 * g (2 * s + 1)) =
      ∑ s ∈ range L, (if s < (j : ℕ) then 4 * (j : ℝ) * c j else 0) * g (2 * s + 1) := by
    intro j
    rw [mul_sum, mul_sum]
    rw [← sum_subset (range_subset_range.mpr (Nat.lt_succ_iff.mp j.isLt))
      (fun s hs hs' ↦ by
        have : ¬ s < (j : ℕ) := by simpa using hs'
        simp [this])]
    refine sum_congr rfl fun s hs ↦ ?_
    rw [ite_eq_left_iff.mpr (fun h ↦ absurd (mem_range.mp hs) h)]
    ring
  rw [sum_congr rfl fun j _ ↦ h j, sum_comm]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [sum_mul]

/-- The quotient by `sin` of the odd mode `2l + 1`, regrouped by the even frequencies:
`Σ_{n<2l+1} w(n, 2l+1) g n = Σ_{t<L} κ(l, t) g (2t)` with `κ(l, 0) = 1`, `κ(l, t) = 2` for
`1 ≤ t ≤ l` and `0` otherwise, for `l < L`. -/
theorem sum_quotient_odd_eq {L l : ℕ} (hl : l < L) (g : ℕ → ℝ) :
    ∑ n ∈ range (2 * l + 1), (trigQuotientWeight n (2 * l + 1) : ℝ) * g n =
      ∑ t ∈ range L, (if t = 0 then 1 else if t ≤ l then 2 else 0) * g (2 * t) := by
  rw [sum_range_trigQuotientWeight_odd]
  obtain ⟨K, rfl⟩ : ∃ K, L = K + 1 := ⟨L - 1, by omega⟩
  rw [sum_range_succ']
  simp only [Nat.succ_ne_zero, ↓reduceIte, mul_zero, one_mul]
  rw [add_comm]
  congr 1
  rw [← sum_subset (range_subset_range.mpr (show l ≤ K by omega)) (fun s hs hs' ↦ by
    have : ¬ s + 1 ≤ l := by simp at hs'; omega
    simp [this])]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [ite_eq_left_iff.mpr (fun h ↦ absurd (by simp at hs; omega) h)]
  ring_nf

end PDE.Analysis
