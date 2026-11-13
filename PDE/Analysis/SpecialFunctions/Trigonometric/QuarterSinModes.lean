/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2

/-!
# The quarter sine rule on products of two modes

The sine rule on `[0, π/2]` with nodes `θ_b = b π / (2P)` gives the moments
`∑_b w_b cos (2kθ_b) = μ_k = 1 / (1 - 4k²)` for `k ≤ P` (`sum_quarterSinWeight_mul_cos`). A
product of two cosines or two sines of frequencies `f`, `f'` of one parity is half the sum or
difference of the cosines of `f - f'` and `f + f'`, so its node sum is
`(μ_{|f - f'|/2} ± μ_{(f + f')/2}) / 2` when `f + f' ≤ 2P`
(`sum_quarterSinWeight_mul_trigMode_mul_trigMode`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Analysis
open Finset PDE.Analysis.TrigPoly2

/-- The moment `μ_k = 1 / (1 - 4k²)` of the quarter sine rule. -/
def quarterSinMoment (k : ℕ) : ℝ := 1 / (1 - 4 * (k : ℝ) ^ 2)

/-- `+1` for the cosine mode, `-1` for the sine mode. -/
def trigModeSign (ι : Fin 2) : ℝ := if ι = 0 then 1 else -1

private theorem sum_cos_dist {P : ℕ} (hP : 0 < P) {f f' : ℕ} (hpar : f % 2 = f' % 2)
    (hff : f + f' ≤ 2 * P) :
    ∑ b : Fin (P + 1), quarterSinWeight P b *
      Real.cos (((f : ℝ) - f') * (b * Real.pi / (2 * P))) =
        quarterSinMoment ((max f f' - min f f') / 2) := by
  set d := (max f f' - min f f') / 2
  have hd : d ≤ P := by omega
  have hrel : ((f : ℝ) - f') = 2 * d ∨ ((f : ℝ) - f') = -(2 * d) := by
    rcases le_total f' f with h | h
    · left
      have : max f f' - min f f' = f - f' := by omega
      have h2 : 2 * d = f - f' := by simp only [d]; omega
      have : ((2 * d : ℕ) : ℝ) = ((f - f' : ℕ) : ℝ) := by rw [h2]
      push_cast [Nat.cast_sub h] at this
      linarith
    · right
      have h2 : 2 * d = f' - f := by simp only [d]; omega
      have : ((2 * d : ℕ) : ℝ) = ((f' - f : ℕ) : ℝ) := by rw [h2]
      push_cast [Nat.cast_sub h] at this
      linarith
  have hcos : ∀ x : ℝ, Real.cos (((f : ℝ) - f') * x) = Real.cos (2 * d * x) := by
    intro x
    rcases hrel with h | h
    · rw [h]
    · rw [h, neg_mul, Real.cos_neg]
  simp only [hcos]
  exact sum_quarterSinWeight_mul_cos hP hd

private theorem sum_cos_add {P : ℕ} (hP : 0 < P) {f f' : ℕ} (hpar : f % 2 = f' % 2)
    (hff : f + f' ≤ 2 * P) :
    ∑ b : Fin (P + 1), quarterSinWeight P b *
      Real.cos (((f : ℝ) + f') * (b * Real.pi / (2 * P))) = quarterSinMoment ((f + f') / 2) := by
  have he : ((f : ℝ) + f') = 2 * (((f + f') / 2 : ℕ) : ℝ) := by
    have h2 : 2 * ((f + f') / 2) = f + f' := by omega
    have : ((2 * ((f + f') / 2) : ℕ) : ℝ) = ((f + f' : ℕ) : ℝ) := by rw [h2]
    push_cast at this
    linarith
  simp only [he]
  exact sum_quarterSinWeight_mul_cos hP (by omega)

/-- **The sine rule on a product of two modes.** For frequencies `f`, `f'` of one parity with
`f + f' ≤ 2P`, the node sum of `trigMode ι (f θ) · trigMode ι (f' θ)` is
`(μ_{|f - f'|/2} + s_ι μ_{(f + f')/2}) / 2` with `s_ι = ±1` for cosines and sines. -/
theorem sum_quarterSinWeight_mul_trigMode_mul_trigMode {P : ℕ} (hP : 0 < P) (ι : Fin 2)
    {f f' : ℕ} (hpar : f % 2 = f' % 2) (hff : f + f' ≤ 2 * P) :
    ∑ b : Fin (P + 1), quarterSinWeight P b * (trigMode ι (f * (b * Real.pi / (2 * P))) *
      trigMode ι (f' * (b * Real.pi / (2 * P)))) =
        (quarterSinMoment ((max f f' - min f f') / 2) +
          trigModeSign ι * quarterSinMoment ((f + f') / 2)) / 2 := by
  have hprod : ∀ x : ℝ, trigMode ι (f * x) * trigMode ι (f' * x) =
      (Real.cos (((f : ℝ) - f') * x) + trigModeSign ι * Real.cos (((f : ℝ) + f') * x)) / 2 := by
    intro x
    have e1 : ((f : ℝ) - f') * x = f * x - f' * x := by ring
    have e2 : ((f : ℝ) + f') * x = f * x + f' * x := by ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    fin_cases ι
    · simp only [Fin.zero_eta, trigMode, trigModeSign, ↓reduceIte]; ring
    · simp only [Fin.mk_one, trigMode, trigModeSign, one_ne_zero, ↓reduceIte]; ring
  rw [sum_congr rfl fun b _ ↦ by rw [hprod]]
  have hsplit : ∀ b : Fin (P + 1), quarterSinWeight P b *
      ((Real.cos (((f : ℝ) - f') * (b * Real.pi / (2 * P))) +
        trigModeSign ι * Real.cos (((f : ℝ) + f') * (b * Real.pi / (2 * P)))) / 2) =
      (quarterSinWeight P b * Real.cos (((f : ℝ) - f') * (b * Real.pi / (2 * P))) +
        trigModeSign ι * (quarterSinWeight P b *
          Real.cos (((f : ℝ) + f') * (b * Real.pi / (2 * P))))) / 2 := fun b ↦ by ring
  rw [sum_congr rfl fun b _ ↦ hsplit b, ← sum_div, sum_add_distrib, ← mul_sum,
    sum_cos_dist hP hpar hff, sum_cos_add hP hpar hff]

end PDE.Analysis
