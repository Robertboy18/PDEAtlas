/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.QuarterSinGram

/-!
# Trigonometric series in exponential coefficients

A cosine series is written `laurentCos T φ θ = ∑_{i ≤ 2T} φ_i cos ((i - T) θ)` and a sine series
`laurentSin T φ θ = ∑_{i ≤ 2T} φ_i sin ((i - T) θ)`, with one coefficient per frequency
`i - T ∈ [-T, T]`. The term `a cos (f θ)` has the symmetric coefficients `cosLaurent T f a`
(`a / 2` at `T ± f`) and `a sin (f θ)` the antisymmetric ones `sinLaurent T f a`
(`laurentCos_cosLaurent`, `laurentSin_sinLaurent`). Symmetry, antisymmetry and the parity of
the frequencies (`IsLaurentSymm`, `IsLaurentAnti`, `HasLaurentParity`) are kept by sums and
scalar multiples. In this form the quarter sine rule pairs two series by one convolution of
their coefficients
(`sum_quarterSinWeight_mul_laurentCos`, `sum_quarterSinWeight_mul_laurentSin`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Analysis
open Finset

/-- The cosine series `∑_{i ≤ 2T} φ_i cos ((i - T) θ)`. -/
def laurentCos (T : ℕ) (φ : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * T + 1), φ i * Real.cos (((i : ℝ) - T) * θ)

/-- The sine series `∑_{i ≤ 2T} φ_i sin ((i - T) θ)`. -/
def laurentSin (T : ℕ) (φ : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * T + 1), φ i * Real.sin (((i : ℝ) - T) * θ)

/-- The symmetric coefficients of `a cos (f θ)`: `a` at `T` for `f = 0`, else `a / 2` at
`T ± f`. -/
def cosLaurent (T f : ℕ) (a : ℝ) (i : ℕ) : ℝ :=
  if f = 0 then (if i = T then a else 0) else (if i = T + f ∨ i + f = T then a / 2 else 0)

/-- The antisymmetric coefficients of `a sin (f θ)`: `a / 2` at `T + f` and `-a / 2` at
`T - f`. -/
def sinLaurent (T f : ℕ) (a : ℝ) (i : ℕ) : ℝ :=
  if f = 0 then 0 else (if i = T + f then a / 2 else if i + f = T then -(a / 2) else 0)

theorem laurentCos_add (T : ℕ) (φ ψ : ℕ → ℝ) (θ : ℝ) :
    laurentCos T (φ + ψ) θ = laurentCos T φ θ + laurentCos T ψ θ := by
  simp only [laurentCos, Pi.add_apply, add_mul, sum_add_distrib]

theorem laurentSin_add (T : ℕ) (φ ψ : ℕ → ℝ) (θ : ℝ) :
    laurentSin T (φ + ψ) θ = laurentSin T φ θ + laurentSin T ψ θ := by
  simp only [laurentSin, Pi.add_apply, add_mul, sum_add_distrib]

theorem laurentCos_sum {ι : Type*} (s : Finset ι) (T : ℕ) (φ : ι → ℕ → ℝ) (θ : ℝ) :
    laurentCos T (fun i ↦ ∑ x ∈ s, φ x i) θ = ∑ x ∈ s, laurentCos T (φ x) θ := by
  simp only [laurentCos, sum_mul]
  exact sum_comm

theorem laurentSin_sum {ι : Type*} (s : Finset ι) (T : ℕ) (φ : ι → ℕ → ℝ) (θ : ℝ) :
    laurentSin T (fun i ↦ ∑ x ∈ s, φ x i) θ = ∑ x ∈ s, laurentSin T (φ x) θ := by
  simp only [laurentSin, sum_mul]
  exact sum_comm

theorem laurentCos_smul (T : ℕ) (c : ℝ) (φ : ℕ → ℝ) (θ : ℝ) :
    laurentCos T (fun i ↦ c * φ i) θ = c * laurentCos T φ θ := by
  simp only [laurentCos, mul_sum, mul_assoc]

theorem laurentSin_smul (T : ℕ) (c : ℝ) (φ : ℕ → ℝ) (θ : ℝ) :
    laurentSin T (fun i ↦ c * φ i) θ = c * laurentSin T φ θ := by
  simp only [laurentSin, mul_sum, mul_assoc]

/-- The coefficients `cosLaurent T f a` give `a cos (f θ)` when `f ≤ T`. -/
theorem laurentCos_cosLaurent {T f : ℕ} (hf : f ≤ T) (a θ : ℝ) :
    laurentCos T (cosLaurent T f a) θ = a * Real.cos (f * θ) := by
  unfold laurentCos cosLaurent
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · simp only [↓reduceIte, ite_mul, zero_mul, sum_ite_eq', mem_range,
      show T < 2 * T + 1 by omega, sub_self, Nat.cast_zero]
  · have hne : f ≠ 0 := by omega
    simp only [hne, ↓reduceIte, ite_mul, zero_mul]
    rw [sum_ite, sum_const_zero, add_zero,
      show (range (2 * T + 1)).filter (fun i ↦ i = T + f ∨ i + f = T) = {T + f, T - f} by
        ext i
        simp only [mem_filter, mem_range, mem_insert, mem_singleton]
        omega,
      sum_pair (by omega), Nat.cast_add, Nat.cast_sub hf, ← Real.cos_neg ((((T - f : ℝ)) - T) * θ)]
    ring_nf

/-- The coefficients `sinLaurent T f a` give `a sin (f θ)` when `f ≤ T`. -/
theorem laurentSin_sinLaurent {T f : ℕ} (hf : f ≤ T) (a θ : ℝ) :
    laurentSin T (sinLaurent T f a) θ = a * Real.sin (f * θ) := by
  unfold laurentSin sinLaurent
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · simp
  · have hne : f ≠ 0 := by omega
    have hsplit : ∀ i, (if i = T + f then a / 2 else if i + f = T then -(a / 2) else 0) =
        (if i = T + f then a / 2 else 0) + (if i = T - f then -(a / 2) else 0) := by
      intro i
      by_cases h₁ : i = T + f
      · rw [ite_eq_left h₁, ite_eq_left h₁, ite_eq_right (by omega), add_zero]
      · by_cases h₂ : i + f = T
        · rw [ite_eq_right h₁, ite_eq_left h₂, ite_eq_right h₁, ite_eq_left (by omega), zero_add]
        · rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₁, ite_eq_right (by omega),
            add_zero]
    simp only [hne, ↓reduceIte, hsplit, add_mul, sum_add_distrib, ite_mul, zero_mul,
      sum_ite_eq', mem_range, show T + f < 2 * T + 1 by omega,
      show T - f < 2 * T + 1 by omega, Nat.cast_add, Nat.cast_sub hf]
    rw [show (((T : ℝ) - f) - T) * θ = -(f * θ) by ring, Real.sin_neg]
    ring_nf

theorem cosLaurent_symm (T f : ℕ) (a : ℝ) {i : ℕ} (hi : i < 2 * T + 1) :
    cosLaurent T f a (2 * T - i) = cosLaurent T f a i := by
  unfold cosLaurent
  split_ifs <;> first | rfl | omega

theorem sinLaurent_anti (T f : ℕ) (a : ℝ) {i : ℕ} (hi : i < 2 * T + 1) :
    sinLaurent T f a (2 * T - i) = -sinLaurent T f a i := by
  unfold sinLaurent
  split_ifs <;> first | omega | simp

theorem cosLaurent_parity (T f : ℕ) (a : ℝ) {i : ℕ} (h : cosLaurent T f a i ≠ 0) :
    i % 2 = (T + f) % 2 := by
  unfold cosLaurent at h
  split_ifs at h <;> first | omega | exact absurd rfl h

theorem sinLaurent_parity (T f : ℕ) (a : ℝ) {i : ℕ} (h : sinLaurent T f a i ≠ 0) :
    i % 2 = (T + f) % 2 := by
  unfold sinLaurent at h
  split_ifs at h <;> first | omega | exact absurd rfl h

/-! ### Symmetry and parity of coefficient rows -/

/-- Symmetric coefficients `φ (2T - i) = φ i`, those of a cosine series. -/
def IsLaurentSymm (T : ℕ) (φ : ℕ → ℝ) : Prop := ∀ i < 2 * T + 1, φ (2 * T - i) = φ i

/-- Antisymmetric coefficients `φ (2T - i) = -φ i`, those of a sine series. -/
def IsLaurentAnti (T : ℕ) (φ : ℕ → ℝ) : Prop := ∀ i < 2 * T + 1, φ (2 * T - i) = -φ i

/-- Coefficients supported on the slots of parity `r`. -/
def HasLaurentParity (r : ℕ) (φ : ℕ → ℝ) : Prop := ∀ i, φ i ≠ 0 → i % 2 = r

theorem isLaurentSymm_cosLaurent (T f : ℕ) (a : ℝ) : IsLaurentSymm T (cosLaurent T f a) :=
  fun _ hi ↦ cosLaurent_symm T f a hi

theorem isLaurentAnti_sinLaurent (T f : ℕ) (a : ℝ) : IsLaurentAnti T (sinLaurent T f a) :=
  fun _ hi ↦ sinLaurent_anti T f a hi

theorem hasLaurentParity_cosLaurent (T f : ℕ) (a : ℝ) :
    HasLaurentParity ((T + f) % 2) (cosLaurent T f a) :=
  fun _ h ↦ cosLaurent_parity T f a h

theorem hasLaurentParity_sinLaurent (T f : ℕ) (a : ℝ) :
    HasLaurentParity ((T + f) % 2) (sinLaurent T f a) :=
  fun _ h ↦ sinLaurent_parity T f a h

theorem hasLaurentParity_cosLaurent_of {T f r : ℕ} (h : (T + f) % 2 = r) (a : ℝ) :
    HasLaurentParity r (cosLaurent T f a) := by
  subst h
  exact hasLaurentParity_cosLaurent T f a

theorem hasLaurentParity_sinLaurent_of {T f r : ℕ} (h : (T + f) % 2 = r) (a : ℝ) :
    HasLaurentParity r (sinLaurent T f a) := by
  subst h
  exact hasLaurentParity_sinLaurent T f a

theorem IsLaurentSymm.add {T : ℕ} {φ ψ : ℕ → ℝ} (hφ : IsLaurentSymm T φ)
    (hψ : IsLaurentSymm T ψ) : IsLaurentSymm T (φ + ψ) :=
  fun i hi ↦ by simp only [Pi.add_apply, hφ i hi, hψ i hi]

theorem IsLaurentAnti.add {T : ℕ} {φ ψ : ℕ → ℝ} (hφ : IsLaurentAnti T φ)
    (hψ : IsLaurentAnti T ψ) : IsLaurentAnti T (φ + ψ) :=
  fun i hi ↦ by simp only [Pi.add_apply, hφ i hi, hψ i hi, neg_add]

theorem IsLaurentSymm.smul {T : ℕ} {φ : ℕ → ℝ} (hφ : IsLaurentSymm T φ) (c : ℝ) :
    IsLaurentSymm T (fun i ↦ c * φ i) :=
  fun i hi ↦ by simp only [hφ i hi]

theorem IsLaurentAnti.smul {T : ℕ} {φ : ℕ → ℝ} (hφ : IsLaurentAnti T φ) (c : ℝ) :
    IsLaurentAnti T (fun i ↦ c * φ i) :=
  fun i hi ↦ by simp only [hφ i hi, mul_neg]

theorem isLaurentSymm_sum {ι : Type*} (s : Finset ι) {T : ℕ} {φ : ι → ℕ → ℝ}
    (h : ∀ x ∈ s, IsLaurentSymm T (φ x)) : IsLaurentSymm T (fun i ↦ ∑ x ∈ s, φ x i) :=
  fun i hi ↦ sum_congr rfl fun x hx ↦ h x hx i hi

theorem isLaurentAnti_sum {ι : Type*} (s : Finset ι) {T : ℕ} {φ : ι → ℕ → ℝ}
    (h : ∀ x ∈ s, IsLaurentAnti T (φ x)) : IsLaurentAnti T (fun i ↦ ∑ x ∈ s, φ x i) :=
  fun i hi ↦ by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun x hx ↦ h x hx i hi

theorem HasLaurentParity.add {r : ℕ} {φ ψ : ℕ → ℝ} (hφ : HasLaurentParity r φ)
    (hψ : HasLaurentParity r ψ) : HasLaurentParity r (φ + ψ) := by
  intro i h
  by_cases h₁ : φ i = 0
  · exact hψ i (by simpa [h₁] using h)
  · exact hφ i h₁

theorem HasLaurentParity.smul {r : ℕ} {φ : ℕ → ℝ} (hφ : HasLaurentParity r φ) (c : ℝ) :
    HasLaurentParity r (fun i ↦ c * φ i) :=
  fun i h ↦ hφ i (right_ne_zero_of_mul h)

theorem hasLaurentParity_sum {ι : Type*} (s : Finset ι) {r : ℕ} {φ : ι → ℕ → ℝ}
    (h : ∀ x ∈ s, HasLaurentParity r (φ x)) : HasLaurentParity r (fun i ↦ ∑ x ∈ s, φ x i) := by
  intro i hi
  obtain ⟨x, hx, hne⟩ := exists_ne_zero_of_sum_ne_zero hi
  exact h x hx i hne

/-- The quarter sine rule pairs two cosine series with symmetric coefficients of one parity by
the convolution of their coefficients. -/
theorem sum_quarterSinWeight_mul_laurentCos {P T r : ℕ} (hP : 0 < P) (hT : T ≤ P)
    {φ ψ : ℕ → ℝ} (hφ : HasLaurentParity r φ) (hψ : HasLaurentParity r ψ)
    (hsym : IsLaurentSymm T ψ) :
    ∑ n : Fin (P + 1), quarterSinWeight P n *
      (laurentCos T φ (n * Real.pi / (2 * P)) * laurentCos T ψ (n * Real.pi / (2 * P))) =
      ∑ i ∈ range (2 * T + 1), ∑ j ∈ range (2 * T + 1),
        φ i * ψ j * quarterSinLaurentMoment (((i + j : ℕ) : ℤ) - 2 * T) :=
  sum_quarterSinWeight_mul_cosSum_mul_cosSum hP hT φ ψ hφ hψ hsym

/-- The quarter sine rule pairs two sine series with antisymmetric coefficients of one parity
by minus the convolution of their coefficients. -/
theorem sum_quarterSinWeight_mul_laurentSin {P T r : ℕ} (hP : 0 < P) (hT : T ≤ P)
    {φ ψ : ℕ → ℝ} (hφ : HasLaurentParity r φ) (hψ : HasLaurentParity r ψ)
    (hanti : IsLaurentAnti T ψ) :
    ∑ n : Fin (P + 1), quarterSinWeight P n *
      (laurentSin T φ (n * Real.pi / (2 * P)) * laurentSin T ψ (n * Real.pi / (2 * P))) =
      -∑ i ∈ range (2 * T + 1), ∑ j ∈ range (2 * T + 1),
        φ i * ψ j * quarterSinLaurentMoment (((i + j : ℕ) : ℤ) - 2 * T) :=
  sum_quarterSinWeight_mul_sinSum_mul_sinSum hP hT φ ψ hφ hψ hanti

end PDE.Analysis
