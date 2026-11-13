/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2

/-!
# Coefficient norms of two-variable trigonometric tables

The `ℓ¹` norm of a table, the sum of the absolute values of its coefficients, bounds its values
(`TrigPoly2.abs_eval_le_l1Norm`), is subadditive, and is submultiplicative under the product
(`TrigPoly2.l1Norm_mul_le`), since the product of two modes is half the sum of two modes in each
variable; a derivative multiplies it by at most the degree in its variable
(`TrigPoly2.l1Norm_dβ_le`, `TrigPoly2.l1Norm_dθ_le`). When the modes are replaced by
approximations within `εβ` and `εθ`, as with fixed-point tables of sines and cosines, the value
changes by at most `‖p‖₁ (εβ + εθ + εβ εθ)` (`TrigPoly2.abs_eval_sub_sum_le`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Finset

theorem abs_trigMode_le_one (i : Fin 2) (x : ℝ) : |trigMode i x| ≤ 1 := by
  fin_cases i
  · exact Real.abs_cos_le_one x
  · exact Real.abs_sin_le_one x

namespace TrigPoly2

variable {Mβ Mθ Nβ Nθ : ℕ} {R : Type} [Field R] [Algebra R ℝ]

/-- The sum of the absolute values of the coefficients. -/
def l1Norm (p : TrigPoly2 Mβ Mθ R) : ℝ :=
  ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1), |algebraMap R ℝ (p.coeff i j k l)|

theorem l1Norm_nonneg (p : TrigPoly2 Mβ Mθ R) : 0 ≤ p.l1Norm :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦
    abs_nonneg _

/-- The `ℓ¹` norm bounds every value. -/
theorem abs_eval_le_l1Norm (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) : |p.eval β θ| ≤ p.l1Norm := by
  unfold eval l1Norm
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun j _ ↦ (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ ↦ ?_))))
  rw [abs_mul, abs_mul]
  calc _ ≤ |algebraMap R ℝ (p.coeff i j k l)| * 1 * 1 := by
        gcongr
        · exact abs_trigMode_le_one _ _
        · exact abs_trigMode_le_one _ _
    _ = _ := by ring

@[simp] theorem l1Norm_zero : (0 : TrigPoly2 Mβ Mθ R).l1Norm = 0 := by
  simp [l1Norm]

theorem l1Norm_add_le (p q : TrigPoly2 Mβ Mθ R) : (p + q).l1Norm ≤ p.l1Norm + q.l1Norm := by
  simp only [l1Norm, coeff_add, map_add, ← sum_add_distrib]
  exact sum_le_sum fun _ _ ↦ sum_le_sum fun _ _ ↦ sum_le_sum fun _ _ ↦ sum_le_sum fun _ _ ↦
    abs_add_le _ _

theorem l1Norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R) :
    (∑ x ∈ s, f x).l1Norm ≤ ∑ x ∈ s, (f x).l1Norm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [sum_insert hx, sum_insert hx]
    exact (l1Norm_add_le _ _).trans (by gcongr)

theorem l1Norm_smul (c : R) (p : TrigPoly2 Mβ Mθ R) :
    (c • p).l1Norm = |algebraMap R ℝ c| * p.l1Norm := by
  simp only [l1Norm, coeff_smul, map_mul, abs_mul, mul_sum]

theorem l1Norm_monomial (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    (monomial i j k l c).l1Norm = |algebraMap R ℝ c| := by
  simp only [l1Norm, monomial]
  rw [sum_eq_single i (fun i' _ hi' ↦ by simp [hi']) (by simp), sum_eq_single j
    (fun j' _ hj' ↦ by simp [hj']) (by simp), sum_eq_single k (fun k' _ hk' ↦ by simp [hk'])
    (by simp), sum_eq_single l (fun l' _ hl' ↦ by simp [hl']) (by simp)]
  simp

private theorem abs_sign_mul_sign_div_four {s t : ℝ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (c : ℝ) : |c * s * t / 4| = |c| / 4 := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [abs_div, abs_neg]

private theorem trigSumSign_mem (i i' : Fin 2) :
    (trigSumSign i i' : ℝ) = 1 ∨ (trigSumSign i i' : ℝ) = -1 := by
  unfold trigSumSign
  split_ifs <;> simp

private theorem trigDiffSign_mem (i i' : Fin 2) (k k' : ℕ) :
    (trigDiffSign i i' k k' : ℝ) = 1 ∨ (trigDiffSign i i' k k' : ℝ) = -1 := by
  unfold trigDiffSign
  split_ifs <;> simp

theorem l1Norm_mulTerm_le (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (i' j' : Fin 2)
    (k' : Fin (Nβ + 1)) (l' : Fin (Nθ + 1)) (c : R) :
    (mulTerm i j k l i' j' k' l' c).l1Norm ≤ |algebraMap R ℝ c| := by
  dsimp only [mulTerm]
  refine ((l1Norm_add_le _ _).trans (add_le_add_left ((l1Norm_add_le _ _).trans
    (add_le_add_left (l1Norm_add_le _ _) _)) _)).trans ?_
  simp only [l1Norm_monomial, map_div₀, map_mul, map_trigSumSign, map_trigDiffSign, map_ofNat,
    abs_sign_mul_sign_div_four (trigSumSign_mem _ _) (trigSumSign_mem _ _),
    abs_sign_mul_sign_div_four (trigSumSign_mem _ _) (trigDiffSign_mem _ _ _ _),
    abs_sign_mul_sign_div_four (trigDiffSign_mem _ _ _ _) (trigSumSign_mem _ _),
    abs_sign_mul_sign_div_four (trigDiffSign_mem _ _ _ _) (trigDiffSign_mem _ _ _ _)]
  linarith

/-- The `ℓ¹` norm is submultiplicative under the product of tables. -/
theorem l1Norm_mul_le (p : TrigPoly2 Mβ Mθ R) (q : TrigPoly2 Nβ Nθ R) :
    (p.mul q).l1Norm ≤ p.l1Norm * q.l1Norm := by
  unfold mul
  refine (l1Norm_sum_le _ _).trans ?_
  conv_rhs => rw [l1Norm, sum_mul]
  refine sum_le_sum fun i _ ↦ (l1Norm_sum_le _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun j _ ↦ (l1Norm_sum_le _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun k _ ↦ (l1Norm_sum_le _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun l _ ↦ ?_
  conv_rhs => rw [l1Norm, mul_sum]
  refine (l1Norm_sum_le _ _).trans (sum_le_sum fun i' _ ↦ ?_)
  rw [mul_sum]
  refine (l1Norm_sum_le _ _).trans (sum_le_sum fun j' _ ↦ ?_)
  rw [mul_sum]
  refine (l1Norm_sum_le _ _).trans (sum_le_sum fun k' _ ↦ ?_)
  rw [mul_sum]
  refine (l1Norm_sum_le _ _).trans (sum_le_sum fun l' _ ↦ ?_)
  exact (l1Norm_mulTerm_le _ _ _ _ _ _ _ _ _).trans (by rw [map_mul, abs_mul])

/-- Differentiation in `β` multiplies the `ℓ¹` norm by at most the degree `Mβ`. -/
theorem l1Norm_dβ_le (p : TrigPoly2 Mβ Mθ R) : (dβ p).l1Norm ≤ Mβ * p.l1Norm := by
  have hterm : ∀ (i' : Fin 2) j (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)),
      |algebraMap R ℝ (((k : ℕ) : R) * (if i' = 0 then p.coeff 1 j k l else
        -p.coeff 0 j k l))| ≤ Mβ * |algebraMap R ℝ (p.coeff (i' + 1) j k l)| := by
    intro i' j k l
    rw [map_mul, map_natCast, abs_mul, Nat.abs_cast]
    have hk : ((k : ℕ) : ℝ) ≤ Mβ := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
    fin_cases i'
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, zero_add]
      gcongr
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, map_neg, abs_neg,
        show (1 : Fin 2) + 1 = 0 from rfl]
      gcongr
  unfold l1Norm
  calc ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1), |algebraMap R ℝ ((dβ p).coeff i j k l)|
      ≤ ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
          Mβ * |algebraMap R ℝ (p.coeff (i + 1) j k l)| :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦
          hterm i j k l
    _ = Mβ * ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
          |algebraMap R ℝ (p.coeff i j k l)| := by
        simp only [mul_sum]
        exact Equiv.sum_comp (Equiv.addRight (1 : Fin 2)) fun i ↦ ∑ j, ∑ k : Fin (Mβ + 1),
          ∑ l : Fin (Mθ + 1), (Mβ : ℝ) * |algebraMap R ℝ (p.coeff i j k l)|

/-- Differentiation in `θ` multiplies the `ℓ¹` norm by at most the degree `Mθ`. -/
theorem l1Norm_dθ_le (p : TrigPoly2 Mβ Mθ R) : (dθ p).l1Norm ≤ Mθ * p.l1Norm := by
  have hterm : ∀ i (j' : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)),
      |algebraMap R ℝ (((l : ℕ) : R) * (if j' = 0 then p.coeff i 1 k l else
        -p.coeff i 0 k l))| ≤ Mθ * |algebraMap R ℝ (p.coeff i (j' + 1) k l)| := by
    intro i j' k l
    rw [map_mul, map_natCast, abs_mul, Nat.abs_cast]
    have hl : ((l : ℕ) : ℝ) ≤ Mθ := by exact_mod_cast Nat.lt_succ_iff.mp l.isLt
    fin_cases j'
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, zero_add]
      gcongr
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, map_neg, abs_neg,
        show (1 : Fin 2) + 1 = 0 from rfl]
      gcongr
  unfold l1Norm
  calc ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1), |algebraMap R ℝ ((dθ p).coeff i j k l)|
      ≤ ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
          Mθ * |algebraMap R ℝ (p.coeff i (j + 1) k l)| :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦
          hterm i j k l
    _ = Mθ * ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
          |algebraMap R ℝ (p.coeff i j k l)| := by
        simp only [mul_sum]
        exact sum_congr rfl fun i _ ↦ Equiv.sum_comp (Equiv.addRight (1 : Fin 2)) fun j ↦
          ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1), (Mθ : ℝ) * |algebraMap R ℝ (p.coeff i j k l)|

/-- Replacing the modes by approximations within `εβ` in `β` and `εθ` in `θ` changes the value
by at most `‖p‖₁ (εβ + εθ + εβ εθ)`. -/
theorem abs_eval_sub_sum_le (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) (A B : Fin 2 → ℕ → ℝ)
    {εβ εθ : ℝ} (hA : ∀ i (k : Fin (Mβ + 1)), |A i k - trigMode i ((k : ℕ) * β)| ≤ εβ)
    (hB : ∀ j (l : Fin (Mθ + 1)), |B j l - trigMode j ((l : ℕ) * θ)| ≤ εθ) :
    |p.eval β θ - ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
      algebraMap R ℝ (p.coeff i j k l) * A i k * B j l| ≤
      p.l1Norm * (εβ + εθ + εβ * εθ) := by
  unfold eval l1Norm
  simp only [← sum_sub_distrib, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun j _ ↦ (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ ↦ ?_))))
  set c := algebraMap R ℝ (p.coeff i j k l)
  set m := trigMode i ((k : ℕ) * β)
  set n := trigMode j ((l : ℕ) * θ)
  have hm : |m| ≤ 1 := abs_trigMode_le_one _ _
  have hn : |n| ≤ 1 := abs_trigMode_le_one _ _
  have ha := hA i k
  have hb := hB j l
  have hεθ : 0 ≤ εθ := (abs_nonneg _).trans hb
  have hεβ : 0 ≤ εβ := (abs_nonneg _).trans ha
  have hBb : |B j l| ≤ 1 + εθ := by
    calc |B j l| = |(B j l - n) + n| := by ring_nf
      _ ≤ |B j l - n| + |n| := abs_add_le _ _
      _ ≤ εθ + 1 := add_le_add hb hn
      _ = 1 + εθ := add_comm _ _
  have key : |m * n - A i k * B j l| ≤ εβ + εθ + εβ * εθ := by
    calc |m * n - A i k * B j l| = |m * (n - B j l) + (m - A i k) * B j l| := by ring_nf
      _ ≤ |m| * |n - B j l| + |m - A i k| * |B j l| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ 1 * εθ + εβ * (1 + εθ) := by
          gcongr
          · rwa [abs_sub_comm]
          · rwa [abs_sub_comm]
      _ = _ := by ring
  calc |c * m * n - c * A i k * B j l| = |c| * |m * n - A i k * B j l| := by
        rw [← abs_mul]; ring_nf
    _ ≤ |c| * (εβ + εθ + εβ * εθ) := by gcongr

end TrigPoly2

end PDE.Analysis
