/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Calculus

/-!
# Quotients by `sin β` of cosine tables vanishing at `0` and `π`

A finite cosine series `∑ₖ aₖ cos (k x)` vanishing at `x = 0` and `x = π` is divisible by
`sin x`: by the telescoping identity `cos (k x) - cos ((k+2) x) = 2 sin x sin ((k+1) x)`, the
quotient is `∑ₙ (∑ₖ w(n, k) aₖ) sin (n x)` with `w(n, k) = 2` when `k < n` and `n - k` is odd
(`cosQuotientWeight`), and the remainder `∑ₖ aₖ cos (T x)`, `T` the top index of the parity of
`k`, is the combination of `cos (N x)` and `cos ((N-1) x)` that vanishes at `0` and `π`
(`sum_cosQuotientWeight_mul_sin_mul_sin`). For a two-variable table without sines in `β` that
vanishes at `β = 0` and `β = π` the table `TrigPoly2.divSinβOfCos p`, of degree one lower in
`β`, satisfies `divSinβOfCos p · sin β = p` at every point (`TrigPoly2.eval_divSinβOfCos_mul_sin`).
This complements `TrigPoly2.divSinβ`, which divides tables of sines in `β`; it applies to
fields that do not vanish at the origin while the combination being divided does.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Finset

/-- The weight of `sin (n x)` in the quotient of `cos (k x)` by `sin x` in a series vanishing at
`0` and `π`: `2` when `k < n` and `n - k` is odd, `0` otherwise. -/
def cosQuotientWeight (n k : ℕ) : ℤ :=
  if k < n ∧ (n - k) % 2 = 1 then 2 else 0

/-- The largest index at most `N` with the parity of `k`. -/
def cosQuotientTop (N k : ℕ) : ℕ :=
  if (N - k) % 2 = 0 then N else N - 1

/-- Telescoping: `sin x · ∑_{n < N} w(n, k) sin (n x) = cos (k x) - cos (T x)`, `T` the largest
index at most `N` with the parity of `k`. -/
theorem sum_range_cosQuotientWeight_mul_sin {k N : ℕ} (hk : k ≤ N) (x : ℝ) :
    ∑ n ∈ range N, (cosQuotientWeight n k : ℝ) * (Real.sin x * Real.sin (n * x)) =
      Real.cos (k * x) - Real.cos (cosQuotientTop N k * x) := by
  induction N, hk using Nat.le_induction with
  | base =>
    rw [sum_eq_zero fun n hn ↦ by
      rw [cosQuotientWeight, ite_eq_right fun h ↦ by have := mem_range.mp hn; omega]; simp]
    simp [cosQuotientTop]
  | succ N hkN ih =>
    rw [sum_range_succ, ih]
    by_cases h : (N - k) % 2 = 0
    · have hw : cosQuotientWeight N k = 0 := by
        rw [cosQuotientWeight, ite_eq_right fun h' ↦ by omega]
      have ht : cosQuotientTop (N + 1) k = N := by
        rw [cosQuotientTop, ite_eq_right (by omega)]
        omega
      rw [hw, ht, cosQuotientTop, ite_eq_left h]
      simp
    · have hlt : k < N := by omega
      have hw : cosQuotientWeight N k = 2 := by
        rw [cosQuotientWeight, ite_eq_left ⟨hlt, by omega⟩]
      have ht : cosQuotientTop (N + 1) k = N + 1 := by
        rw [cosQuotientTop, ite_eq_left (by omega)]
      have ht' : cosQuotientTop N k = N - 1 := by
        rw [cosQuotientTop, ite_eq_right h]
      rw [hw, ht, ht', Nat.cast_sub (by omega : 1 ≤ N)]
      push_cast
      rw [show ((N : ℝ) - 1) * x = N * x - x by ring, show ((N : ℝ) + 1) * x = N * x + x by ring,
        Real.cos_sub, Real.cos_add]
      ring

/-- The quotient identity for a finite cosine series: `sin x` times the sine series of the
weights equals the series minus its values at the top indices of each parity. -/
theorem sum_cosQuotientWeight_mul_sin_mul_sin (a : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    (∑ n ∈ range N, (∑ k ∈ range (N + 1), (cosQuotientWeight n k : ℝ) * a k) *
        Real.sin (n * x)) * Real.sin x =
      ∑ k ∈ range (N + 1), a k * (Real.cos (k * x) - Real.cos (cosQuotientTop N k * x)) := by
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [← sum_range_cosQuotientWeight_mul_sin (Nat.lt_succ_iff.mp (mem_range.mp hk)) x, mul_sum]
  exact sum_congr rfl fun n _ ↦ by ring

/-- The values at the top indices split by the parity of `N - k`. -/
theorem sum_mul_cos_cosQuotientTop (a : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    ∑ k ∈ range (N + 1), a k * Real.cos (cosQuotientTop N k * x) =
      Real.cos (N * x) * ∑ k ∈ range (N + 1), (if (N - k) % 2 = 0 then a k else 0) +
        Real.cos (((N - 1 : ℕ) : ℝ) * x) *
          ∑ k ∈ range (N + 1), (if (N - k) % 2 = 0 then 0 else a k) := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  by_cases h : (N - k) % 2 = 0 <;> simp [cosQuotientTop, h, mul_comm]

namespace TrigPoly2

variable {Mβ Mθ : ℕ} {R : Type} [Field R]

/-- The quotient by `sin β` of a table of cosines in `β` that vanishes at `β = 0` and `β = π`:
each `cos (kβ)` contributes `∑_{n > k, n - k odd} 2 sin (nβ)`. The degree in `β` drops by one. -/
def divSinβOfCos (p : TrigPoly2 Mβ Mθ R) : TrigPoly2 (Mβ - 1) Mθ R :=
  ⟨fun i j n l ↦ if i = 1 then
    ∑ k ∈ range (Mβ + 1), (cosQuotientWeight n k : R) * p.coeffN 0 j k l else 0⟩

theorem coeffN_divSinβOfCos (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (n l : ℕ) (hn : n < Mβ) :
    (divSinβOfCos p).coeffN i j n l = if i = 1 then
      ∑ k ∈ range (Mβ + 1), (cosQuotientWeight n k : R) * p.coeffN 0 j k l else 0 := by
  by_cases hl : l < Mθ + 1
  · rw [coeffN, dite_eq_left ⟨by omega, hl⟩]
    rfl
  · rw [coeffN, dite_eq_right (by omega)]
    split_ifs
    · refine (sum_eq_zero fun k _ ↦ ?_).symm
      rw [coeffN, dite_eq_right (by omega), mul_zero]
    · rfl

/-- The quotient commutes with ring homomorphisms of the coefficients. -/
@[simp] theorem map_divSinβOfCos {S : Type} [Field S] (f : R →+* S) (p : TrigPoly2 Mβ Mθ R) :
    (divSinβOfCos p).map f = divSinβOfCos (p.map f) := by
  ext i j n l
  change f ((divSinβOfCos p).coeff i j n l) = (divSinβOfCos (p.map f)).coeff i j n l
  simp only [divSinβOfCos, coeffN_map]
  split_ifs <;> simp

variable [Algebra R ℝ]

omit [Algebra R ℝ] in
private theorem coeffN_one_eq_zero {p : TrigPoly2 Mβ Mθ R} (h : ∀ j k l, p.coeff 1 j k l = 0)
    (j : Fin 2) (k l : ℕ) : p.coeffN 1 j k l = 0 := by
  unfold coeffN
  split_ifs with hkl
  · exact h j _ _
  · rfl

/-- The sine sections of the quotient are the weighted sums of the cosine sections. -/
theorem sectionβ_divSinβOfCos_one (p : TrigPoly2 Mβ Mθ R) (θ : ℝ) {n : ℕ} (hn : n < Mβ) :
    (divSinβOfCos p).sectionβ θ 1 n =
      ∑ k ∈ range (Mβ + 1), (cosQuotientWeight n k : ℝ) * p.sectionβ θ 0 k := by
  simp only [sectionβ, coeffN_divSinβOfCos p _ _ n _ hn, ite_true, _root_.map_sum,
    _root_.map_mul, map_intCast, mul_sum, sum_mul]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  conv_rhs => rw [sum_comm]
  exact sum_congr rfl fun l _ ↦ sum_congr rfl fun k _ ↦ by ring

/-- The cosine sections of the quotient vanish. -/
theorem sectionβ_divSinβOfCos_zero (p : TrigPoly2 Mβ Mθ R) (θ : ℝ) {n : ℕ} (hn : n < Mβ) :
    (divSinβOfCos p).sectionβ θ 0 n = 0 := by
  simp [sectionβ, coeffN_divSinβOfCos p _ _ n _ hn]

/-- Without sines in `β`, `divSinβOfCos p · sin β` is `p` minus the values of the cosine
sections at the top indices of each parity. -/
theorem eval_divSinβOfCos_mul_sin_eq_sub (p : TrigPoly2 Mβ Mθ R) (hMβ : 1 ≤ Mβ)
    (hsin : ∀ j k l, p.coeff 1 j k l = 0) (β θ : ℝ) :
    (divSinβOfCos p).eval β θ * Real.sin β = p.eval β θ -
      ∑ k ∈ range (Mβ + 1), p.sectionβ θ 0 k * Real.cos (cosQuotientTop Mβ k * β) := by
  have hp1 (k : ℕ) : p.sectionβ θ 1 k = 0 := by
    simp [sectionβ, coeffN_one_eq_zero hsin]
  rw [eval_eq_sum_sectionβ, eval_eq_sum_sectionβ, Nat.sub_add_cancel hMβ]
  have hq : ∑ n ∈ range Mβ, ((divSinβOfCos p).sectionβ θ 0 n * Real.cos (n * β) +
      (divSinβOfCos p).sectionβ θ 1 n * Real.sin (n * β)) =
      ∑ n ∈ range Mβ, (∑ k ∈ range (Mβ + 1), (cosQuotientWeight n k : ℝ) * p.sectionβ θ 0 k) *
        Real.sin (n * β) :=
    sum_congr rfl fun n hn ↦ by
      rw [sectionβ_divSinβOfCos_zero p θ (mem_range.mp hn),
        sectionβ_divSinβOfCos_one p θ (mem_range.mp hn), zero_mul, zero_add]
  rw [hq, sum_cosQuotientWeight_mul_sin_mul_sin]
  simp only [hp1, zero_mul, add_zero, mul_sub, sum_sub_distrib]

/-- Without sines in `β`, and vanishing at `β = 0` and `β = π`, `divSinβOfCos p · sin β = p`. -/
theorem eval_divSinβOfCos_mul_sin (p : TrigPoly2 Mβ Mθ R) (hMβ : 1 ≤ Mβ)
    (hsin : ∀ j k l, p.coeff 1 j k l = 0) (h0 : ∀ θ, p.eval 0 θ = 0)
    (hπ : ∀ θ, p.eval Real.pi θ = 0) (β θ : ℝ) :
    (divSinβOfCos p).eval β θ * Real.sin β = p.eval β θ := by
  have htop (x : ℝ) := sum_mul_cos_cosQuotientTop (fun k ↦ p.sectionβ θ 0 k) Mβ x
  have hz := eval_divSinβOfCos_mul_sin_eq_sub p hMβ hsin 0 θ
  have hp := eval_divSinβOfCos_mul_sin_eq_sub p hMβ hsin Real.pi θ
  rw [htop, h0 θ] at hz
  rw [htop, hπ θ] at hp
  simp only [Real.sin_zero, mul_zero, Real.cos_zero, one_mul] at hz
  simp only [Real.sin_pi, mul_zero] at hp
  have hcN : Real.cos (Mβ * Real.pi) = (-1) ^ Mβ := Real.cos_nat_mul_pi Mβ
  have hcN1 : Real.cos (((Mβ - 1 : ℕ) : ℝ) * Real.pi) = -(-1) ^ Mβ := by
    obtain ⟨m, rfl⟩ : ∃ m, Mβ = m + 1 := ⟨Mβ - 1, by omega⟩
    rw [Real.cos_nat_mul_pi, Nat.add_sub_cancel, pow_succ]
    ring
  rw [hcN, hcN1] at hp
  set E := ∑ k ∈ range (Mβ + 1), (if (Mβ - k) % 2 = 0 then p.sectionβ θ 0 k else 0) with hE
  set O := ∑ k ∈ range (Mβ + 1), (if (Mβ - k) % 2 = 0 then 0 else p.sectionβ θ 0 k) with hO
  have h1 : E + O = 0 := by linarith
  have h2 : (-1 : ℝ) ^ Mβ * (E - O) = 0 := by linarith
  have h3 : E - O = 0 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ (by norm_num))
  have hE0 : E = 0 := by linarith
  have hO0 : O = 0 := by linarith
  rw [eval_divSinβOfCos_mul_sin_eq_sub p hMβ hsin, htop β, hE0, hO0]
  ring

end TrigPoly2

end PDE.Analysis
