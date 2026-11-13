/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Bounds
public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Quotient

/-!
# Coefficient norms of tables with bounded frequencies

A table whose coefficients vanish above the frequency `K` in `θ` (`SupportedThetaLE K`) keeps
this support under `dθ`, and `dθ` multiplies its `ℓ¹` norm by at most `K`
(`l1Norm_dθ_le_of_supported`), a sharper form of `l1Norm_dθ_le` for tables of low frequency
inside a table of high degree. The quotient weights of `sin (l x) / sin x` sum to `l`
(`sum_range_trigQuotientWeight`), and their sum over the nodes of a quotient table is at most
`l` (`sum_trigQuotientWeight_le`), so the quotient by `sin θ` of such a table also has at most
`K` times its norm (`l1Norm_divSinθ_le_of_supported`); both operations keep the support. The
same holds in `β` (`SupportedBetaLE`, `l1Norm_dβ_le_of_supported`,
`l1Norm_divSinβ_le_of_supported`), and a monomial is supported in its own frequencies.
-/

@[expose] public section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {Mβ Mθ : ℕ} {R : Type} [Field R] [Algebra R ℝ]

/-- A table whose coefficients vanish above the frequency `K` in `θ`. -/
def SupportedThetaLE (K : ℕ) (p : TrigPoly2 Mβ Mθ R) : Prop :=
  ∀ i j (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)), K < (l : ℕ) → p.coeff i j k l = 0

omit [Algebra R ℝ] in
theorem SupportedThetaLE.dθ {K : ℕ} {p : TrigPoly2 Mβ Mθ R} (h : SupportedThetaLE K p) :
    SupportedThetaLE K p.dθ := by
  intro i j k l hl
  simp only [TrigPoly2.dθ]
  split_ifs <;> simp [h _ _ _ _ hl]

/-- Differentiation in `θ` of a table supported in frequencies `≤ K` multiplies the `ℓ¹` norm
by at most `K`. -/
theorem l1Norm_dθ_le_of_supported {K : ℕ} {p : TrigPoly2 Mβ Mθ R}
    (h : SupportedThetaLE K p) : (dθ p).l1Norm ≤ K * p.l1Norm := by
  have hterm : ∀ i (j' : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)),
      |algebraMap R ℝ (((l : ℕ) : R) * (if j' = 0 then p.coeff i 1 k l else
        -p.coeff i 0 k l))| ≤ K * |algebraMap R ℝ (p.coeff i (j' + 1) k l)| := by
    intro i j' k l
    rw [map_mul, map_natCast, abs_mul, Nat.abs_cast]
    by_cases hl : (l : ℕ) ≤ K
    · have hl' : ((l : ℕ) : ℝ) ≤ K := by exact_mod_cast hl
      fin_cases j'
      · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, zero_add]
        gcongr
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, map_neg, abs_neg,
          show (1 : Fin 2) + 1 = 0 from rfl]
        gcongr
    · have hz : ∀ j, p.coeff i j k l = 0 := fun j ↦ h i j k l (by omega)
      fin_cases j' <;> simp [hz]
  unfold l1Norm
  calc ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1), |algebraMap R ℝ ((dθ p).coeff i j k l)|
      ≤ ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
          K * |algebraMap R ℝ (p.coeff i (j + 1) k l)| :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦
          hterm i j k l
    _ = K * ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
          |algebraMap R ℝ (p.coeff i j k l)| := by
        simp only [mul_sum]
        exact sum_congr rfl fun i _ ↦ Equiv.sum_comp (Equiv.addRight (1 : Fin 2)) fun j ↦
          ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1), (K : ℝ) * |algebraMap R ℝ (p.coeff i j k l)|

theorem sum_range_trigQuotientWeight (l : ℕ) :
    ∑ n ∈ range l, (trigQuotientWeight n l : ℤ) = l := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    rcases l with _ | _ | l
    · simp
    · simp [trigQuotientWeight]
    · have h := ih l (by omega)
      rw [sum_range_succ, sum_range_succ]
      have hw : ∀ n ∈ range l, trigQuotientWeight n (l + 2) = trigQuotientWeight n l := by
        intro n hn
        have := mem_range.mp hn
        simp only [trigQuotientWeight]
        congr 1
        apply propext
        constructor <;> intro ⟨h1, h2⟩ <;> refine ⟨by omega, by omega⟩
      rw [sum_congr rfl hw, h]
      simp only [trigQuotientWeight]
      have e1 : ¬ (l < l + 2 ∧ (l + 2 - l) % 2 = 1) := by omega
      have e2 : (l + 1 < l + 2 ∧ (l + 2 - (l + 1)) % 2 = 1) := by omega
      have e3 : l + 1 ≠ 0 := by omega
      simp only [e1, e2, e3, ↓reduceIte, and_self]
      push_cast
      ring

theorem sum_trigQuotientWeight_le {Mθ l : ℕ} (hl : l ≤ Mθ) :
    ∑ n : Fin (Mθ - 1 + 1), ((trigQuotientWeight n l : ℤ) : ℝ) ≤ l := by
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ ((trigQuotientWeight n l : ℤ) : ℝ))]
  have hsub : ∑ n ∈ range (Mθ - 1 + 1), ((trigQuotientWeight n l : ℤ) : ℝ) =
      ∑ n ∈ range l, ((trigQuotientWeight n l : ℤ) : ℝ) := by
    rcases Nat.lt_or_ge (Mθ - 1 + 1) l with h' | h'
    · have : l = Mθ - 1 + 1 + 0 := by omega
      rcases Nat.eq_zero_or_pos Mθ with h0 | h0 <;> omega
    · refine (sum_subset (range_subset_range.mpr h') fun n hn hn' ↦ ?_).symm
      rw [trigQuotientWeight_eq_zero (by simpa using hn'), Int.cast_zero]
  rw [hsub]
  have := sum_range_trigQuotientWeight l
  exact_mod_cast this.le

theorem trigQuotientWeight_nonneg (n l : ℕ) : 0 ≤ trigQuotientWeight n l := by
  unfold trigQuotientWeight
  split_ifs <;> norm_num

/-- The quotient by `sin θ` of a table supported in frequencies `≤ K` has `ℓ¹` norm at most `K`
times that of the table. -/
theorem l1Norm_divSinθ_le_of_supported {K : ℕ} {p : TrigPoly2 Mβ Mθ R}
    (h : SupportedThetaLE K p) : (divSinθ p).l1Norm ≤ K * p.l1Norm := by
  have hcN : ∀ i k l, l ∈ range (Mθ + 1) →
      |algebraMap R ℝ (p.coeffN i 1 k l)| * l ≤ K * |algebraMap R ℝ (p.coeffN i 1 k l)| := by
    intro i k l hl
    by_cases hlK : l ≤ K
    · rw [mul_comm]
      gcongr
    · by_cases hk : k < Mβ + 1
      · have : p.coeffN i 1 k l = 0 := by
          rw [show p.coeffN i 1 k l = p.coeff i 1 ⟨k, hk⟩ ⟨l, mem_range.mp hl⟩ by
            simp [coeffN, hk, mem_range.mp hl]]
          exact h i 1 _ _ (by simp; omega)
        simp [this]
      · simp [coeffN, hk]
  have hterm : ∀ i (k : Fin (Mβ + 1)),
      ∑ j, ∑ n : Fin (Mθ - 1 + 1), |algebraMap R ℝ ((divSinθ p).coeff i j k n)| ≤
        K * ∑ j, ∑ l : Fin (Mθ + 1), |algebraMap R ℝ (p.coeff i j k l)| := by
    intro i k
    have hj1 : ∑ n : Fin (Mθ - 1 + 1), |algebraMap R ℝ ((divSinθ p).coeff i 1 k n)| = 0 := by
      simp [divSinθ]
    rw [Fin.sum_univ_two, hj1, add_zero]
    calc ∑ n : Fin (Mθ - 1 + 1), |algebraMap R ℝ ((divSinθ p).coeff i 0 k n)|
        ≤ ∑ n : Fin (Mθ - 1 + 1), ∑ l ∈ range (Mθ + 1),
            ((trigQuotientWeight n l : ℤ) : ℝ) * |algebraMap R ℝ (p.coeffN i 1 k l)| := by
          refine sum_le_sum fun n _ ↦ ?_
          simp only [divSinθ, Fin.isValue, ↓reduceIte, map_sum, map_mul, map_intCast]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ ↦ ?_)
          rw [abs_mul, abs_of_nonneg (by exact_mod_cast trigQuotientWeight_nonneg n l)]
      _ = ∑ l ∈ range (Mθ + 1), |algebraMap R ℝ (p.coeffN i 1 k l)| *
            ∑ n : Fin (Mθ - 1 + 1), ((trigQuotientWeight n l : ℤ) : ℝ) := by
          rw [sum_comm]
          exact sum_congr rfl fun l _ ↦ by rw [mul_sum]; exact sum_congr rfl fun n _ ↦ by ring
      _ ≤ ∑ l ∈ range (Mθ + 1), |algebraMap R ℝ (p.coeffN i 1 k l)| * l := by
          refine sum_le_sum fun l hl ↦ ?_
          gcongr
          exact sum_trigQuotientWeight_le (Nat.lt_succ_iff.mp (mem_range.mp hl))
      _ ≤ ∑ l ∈ range (Mθ + 1), K * |algebraMap R ℝ (p.coeffN i 1 k l)| :=
          sum_le_sum fun l hl ↦ hcN i k l hl
      _ = K * ∑ l : Fin (Mθ + 1), |algebraMap R ℝ (p.coeff i 1 k l)| := by
          rw [← mul_sum, ← Fin.sum_univ_eq_sum_range (fun l ↦ |algebraMap R ℝ (p.coeffN i 1 k l)|)]
          simp
      _ ≤ K * ∑ j, ∑ l : Fin (Mθ + 1), |algebraMap R ℝ (p.coeff i j k l)| := by
          gcongr
          rw [Fin.sum_univ_two]
          exact le_add_of_nonneg_left (sum_nonneg fun _ _ ↦ abs_nonneg _)
  unfold l1Norm
  calc ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ n : Fin (Mθ - 1 + 1),
        |algebraMap R ℝ ((divSinθ p).coeff i j k n)|
      = ∑ i, ∑ k : Fin (Mβ + 1), ∑ j, ∑ n : Fin (Mθ - 1 + 1),
          |algebraMap R ℝ ((divSinθ p).coeff i j k n)| :=
        sum_congr rfl fun i _ ↦ sum_comm
    _ ≤ ∑ i, ∑ k : Fin (Mβ + 1), K * ∑ j, ∑ l : Fin (Mθ + 1),
          |algebraMap R ℝ (p.coeff i j k l)| :=
        sum_le_sum fun i _ ↦ sum_le_sum fun k _ ↦ hterm i k
    _ = K * ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
          |algebraMap R ℝ (p.coeff i j k l)| := by
        simp only [← mul_sum]
        exact congrArg _ (sum_congr rfl fun i _ ↦ sum_comm)

omit [Algebra R ℝ] in
theorem SupportedThetaLE.divSinθ {K : ℕ} {p : TrigPoly2 Mβ Mθ R} (h : SupportedThetaLE K p) :
    SupportedThetaLE K (divSinθ p) := by
  intro i j k n hn
  simp only [TrigPoly2.divSinθ]
  split_ifs
  · refine sum_eq_zero fun l hl ↦ ?_
    by_cases hnl : (n : ℕ) < l
    · have hl' := mem_range.mp hl
      have : p.coeffN i 1 k l = 0 := by
        rw [show p.coeffN i 1 k l = p.coeff i 1 k ⟨l, hl'⟩ by
          rw [coeffN, dite_eq_left_of_eq_true (eq_true ⟨k.isLt, hl'⟩)]]
        exact h i 1 k _ (by simp; omega)
      rw [this, mul_zero]
    · rw [trigQuotientWeight_eq_zero (by omega), Int.cast_zero, zero_mul]
  · rfl

/-- A table whose coefficients vanish above the frequency `K` in `β`. -/
def SupportedBetaLE (K : ℕ) (p : TrigPoly2 Mβ Mθ R) : Prop :=
  ∀ i j (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)), K < (k : ℕ) → p.coeff i j k l = 0

omit [Algebra R ℝ] in
theorem SupportedBetaLE.dβ {K : ℕ} {p : TrigPoly2 Mβ Mθ R} (h : SupportedBetaLE K p) :
    SupportedBetaLE K p.dβ := by
  intro i j k l hk
  simp only [TrigPoly2.dβ]
  split_ifs <;> simp [h _ _ _ _ hk]

omit [Algebra R ℝ] in
theorem SupportedBetaLE.divSinβ {K : ℕ} {p : TrigPoly2 Mβ Mθ R} (h : SupportedBetaLE K p) :
    SupportedBetaLE K (divSinβ p) := by
  intro i j n l hn
  simp only [TrigPoly2.divSinβ]
  split_ifs
  · refine sum_eq_zero fun k hk ↦ ?_
    by_cases hnk : (n : ℕ) < k
    · have hk' := mem_range.mp hk
      have : p.coeffN 1 j k l = 0 := by
        rw [show p.coeffN 1 j k l = p.coeff 1 j ⟨k, hk'⟩ l by
          rw [coeffN, dite_eq_left_of_eq_true (eq_true ⟨hk', l.isLt⟩)]]
        exact h 1 j _ l (by simp; omega)
      rw [this, mul_zero]
    · rw [trigQuotientWeight_eq_zero (by omega), Int.cast_zero, zero_mul]
  · rfl

/-- Differentiation in `β` of a table supported in frequencies `≤ K` multiplies the `ℓ¹` norm
by at most `K`. -/
theorem l1Norm_dβ_le_of_supported {K : ℕ} {p : TrigPoly2 Mβ Mθ R}
    (h : SupportedBetaLE K p) : (dβ p).l1Norm ≤ K * p.l1Norm := by
  have hterm : ∀ (i' : Fin 2) j (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)),
      |algebraMap R ℝ (((k : ℕ) : R) * (if i' = 0 then p.coeff 1 j k l else
        -p.coeff 0 j k l))| ≤ K * |algebraMap R ℝ (p.coeff (i' + 1) j k l)| := by
    intro i' j k l
    rw [map_mul, map_natCast, abs_mul, Nat.abs_cast]
    by_cases hk : (k : ℕ) ≤ K
    · have hk' : ((k : ℕ) : ℝ) ≤ K := by exact_mod_cast hk
      fin_cases i'
      · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, zero_add]
        gcongr
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, map_neg, abs_neg,
          show (1 : Fin 2) + 1 = 0 from rfl]
        gcongr
    · have hz : ∀ i, p.coeff i j k l = 0 := fun i ↦ h i j k l (by omega)
      fin_cases i' <;> simp [hz]
  unfold l1Norm
  calc ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1), |algebraMap R ℝ ((dβ p).coeff i j k l)|
      ≤ ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
          K * |algebraMap R ℝ (p.coeff (i + 1) j k l)| :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦
          hterm i j k l
    _ = K * ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
          |algebraMap R ℝ (p.coeff i j k l)| := by
        simp only [mul_sum]
        exact Equiv.sum_comp (Equiv.addRight (1 : Fin 2)) fun i ↦ ∑ j, ∑ k : Fin (Mβ + 1),
          ∑ l : Fin (Mθ + 1), (K : ℝ) * |algebraMap R ℝ (p.coeff i j k l)|

private theorem sum_four_comm {a b : ℕ} (f : Fin 2 → Fin 2 → Fin a → Fin b → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ j, ∑ l, ∑ i, ∑ k, f i j k l := by
  rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [show ∑ i, ∑ k, ∑ l, f i j k l = ∑ i, ∑ l, ∑ k, f i j k l from
    sum_congr rfl fun i _ ↦ sum_comm]
  exact sum_comm

/-- The quotient by `sin β` of a table supported in frequencies `≤ K` has `ℓ¹` norm at most `K`
times that of the table. -/
theorem l1Norm_divSinβ_le_of_supported {K : ℕ} {p : TrigPoly2 Mβ Mθ R}
    (h : SupportedBetaLE K p) : (divSinβ p).l1Norm ≤ K * p.l1Norm := by
  have hcN : ∀ j k l, k ∈ range (Mβ + 1) →
      |algebraMap R ℝ (p.coeffN 1 j k l)| * k ≤ K * |algebraMap R ℝ (p.coeffN 1 j k l)| := by
    intro j k l hk
    by_cases hkK : k ≤ K
    · rw [mul_comm]
      gcongr
    · by_cases hl : l < Mθ + 1
      · have : p.coeffN 1 j k l = 0 := by
          rw [show p.coeffN 1 j k l = p.coeff 1 j ⟨k, mem_range.mp hk⟩ ⟨l, hl⟩ by
            simp [coeffN, hl, mem_range.mp hk]]
          exact h 1 j _ _ (by simp; omega)
        simp [this]
      · simp [coeffN, hl]
  have hterm : ∀ j (l : Fin (Mθ + 1)),
      ∑ i, ∑ n : Fin (Mβ - 1 + 1), |algebraMap R ℝ ((divSinβ p).coeff i j n l)| ≤
        K * ∑ i, ∑ k : Fin (Mβ + 1), |algebraMap R ℝ (p.coeff i j k l)| := by
    intro j l
    have hi1 : ∑ n : Fin (Mβ - 1 + 1), |algebraMap R ℝ ((divSinβ p).coeff 1 j n l)| = 0 := by
      simp [divSinβ]
    rw [Fin.sum_univ_two, hi1, add_zero]
    calc ∑ n : Fin (Mβ - 1 + 1), |algebraMap R ℝ ((divSinβ p).coeff 0 j n l)|
        ≤ ∑ n : Fin (Mβ - 1 + 1), ∑ k ∈ range (Mβ + 1),
            ((trigQuotientWeight n k : ℤ) : ℝ) * |algebraMap R ℝ (p.coeffN 1 j k l)| := by
          refine sum_le_sum fun n _ ↦ ?_
          simp only [divSinβ, Fin.isValue, ↓reduceIte, map_sum, map_mul, map_intCast]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ ?_)
          rw [abs_mul, abs_of_nonneg (by exact_mod_cast trigQuotientWeight_nonneg n k)]
      _ = ∑ k ∈ range (Mβ + 1), |algebraMap R ℝ (p.coeffN 1 j k l)| *
            ∑ n : Fin (Mβ - 1 + 1), ((trigQuotientWeight n k : ℤ) : ℝ) := by
          rw [sum_comm]
          exact sum_congr rfl fun k _ ↦ by rw [mul_sum]; exact sum_congr rfl fun n _ ↦ by ring
      _ ≤ ∑ k ∈ range (Mβ + 1), |algebraMap R ℝ (p.coeffN 1 j k l)| * k := by
          refine sum_le_sum fun k hk ↦ ?_
          gcongr
          exact sum_trigQuotientWeight_le (Nat.lt_succ_iff.mp (mem_range.mp hk))
      _ ≤ ∑ k ∈ range (Mβ + 1), K * |algebraMap R ℝ (p.coeffN 1 j k l)| :=
          sum_le_sum fun k hk ↦ hcN j k l hk
      _ = K * ∑ k : Fin (Mβ + 1), |algebraMap R ℝ (p.coeff 1 j k l)| := by
          rw [← mul_sum, ← Fin.sum_univ_eq_sum_range (fun k ↦ |algebraMap R ℝ (p.coeffN 1 j k l)|)]
          simp
      _ ≤ K * ∑ i, ∑ k : Fin (Mβ + 1), |algebraMap R ℝ (p.coeff i j k l)| := by
          gcongr
          rw [Fin.sum_univ_two]
          exact le_add_of_nonneg_left (sum_nonneg fun _ _ ↦ abs_nonneg _)
  unfold l1Norm
  rw [sum_four_comm, sum_four_comm (f := fun i j k l ↦ |algebraMap R ℝ (p.coeff i j k l)|),
    mul_sum]
  exact sum_le_sum fun j _ ↦ by rw [mul_sum]; exact sum_le_sum fun l _ ↦ hterm j l

omit [Algebra R ℝ] in
theorem supportedThetaLE_monomial (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    SupportedThetaLE l (monomial i j k l c) := by
  intro i' j' k' l' hl
  have : l' ≠ l := fun e ↦ by rw [e] at hl; exact lt_irrefl _ hl
  simp [monomial, this]

omit [Algebra R ℝ] in
theorem supportedBetaLE_monomial (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    SupportedBetaLE k (monomial i j k l c) := by
  intro i' j' k' l' hk
  have : k' ≠ k := fun e ↦ by rw [e] at hk; exact lt_irrefl _ hk
  simp [monomial, this]

end PDE.Analysis.TrigPoly2
