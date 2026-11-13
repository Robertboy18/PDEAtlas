/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigLaurent

/-!
# Products of trigonometric series in exponential coefficients

The product of two series in exponential coefficients is the series of the convolution of the
coefficients, `laurentConv T S φ ψ`, on the window `T + S`, when the second factor has the
symmetry of its kind: a cosine series times a symmetric cosine series is a cosine series, a
cosine series times an antisymmetric sine series is a sine series, a sine series times a
symmetric cosine series is a sine series and a sine series times an antisymmetric sine series is
minus a cosine series (`laurentCos_mul_laurentCos` and its companions). A series on the window
`T` is also a series on every larger window, its coefficients shifted (`laurentCos_widen`,
`laurentSin_widen`). Convolutions and shifts keep symmetry, antisymmetry and the parity of the
frequencies (`IsLaurentSymm.conv` and its companions, `HasLaurentParity.conv`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Finset

/-- The convolution of the coefficients `φ` on the window `T` and `ψ` on the window `S`:
`∑_{i + j = k} φ_i ψ_j`, `i ≤ 2T`, `j ≤ 2S`. -/
def laurentConv (T S : ℕ) (φ ψ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (2 * T + 1), φ i * (if i ≤ k ∧ k - i < 2 * S + 1 then ψ (k - i) else 0)

/-- The coefficients `φ` on the window `T` shifted to the window `T + d`. -/
def laurentShift (T d : ℕ) (φ : ℕ → ℝ) (i : ℕ) : ℝ :=
  if d ≤ i ∧ i - d < 2 * T + 1 then φ (i - d) else 0

private theorem sum_ite_shift {m n i : ℕ} (hn : i + m ≤ n) (F : ℕ → ℝ) (G : ℕ → ℝ) :
    ∑ k ∈ range n, (if i ≤ k ∧ k - i < m then F (k - i) else 0) * G k =
      ∑ j ∈ range m, F j * G (i + j) := by
  have hfilt : (range n).filter (fun k ↦ i ≤ k ∧ k - i < m) = (range m).image (i + ·) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨k - i, h2, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨by omega, by omega, by omega⟩
  simp only [ite_mul, zero_mul]
  rw [← sum_filter, hfilt, sum_image (fun a _ b _ h ↦ by simpa using h)]
  exact sum_congr rfl fun j _ ↦ by rw [Nat.add_sub_cancel_left]

/-- The double sum of a product series regrouped by the total index. -/
private theorem sum_conv_eq (T S : ℕ) (φ ψ : ℕ → ℝ) (G : ℕ → ℝ) :
    ∑ k ∈ range (2 * (T + S) + 1), laurentConv T S φ ψ k * G k =
      ∑ i ∈ range (2 * T + 1), ∑ j ∈ range (2 * S + 1), φ i * ψ j * G (i + j) := by
  simp only [laurentConv, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  simp only [mul_assoc]
  rw [← mul_sum, sum_ite_shift (by omega) ψ G, mul_sum]

/-- Reflection of a symmetric or antisymmetric factor. -/
private theorem sum_reflect (S : ℕ) (ψ : ℕ → ℝ) (g : ℝ → ℝ) :
    ∑ j ∈ range (2 * S + 1), ψ j * g ((j : ℝ) - S) =
      ∑ j ∈ range (2 * S + 1), ψ (2 * S - j) * g (-((j : ℝ) - S)) := by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' := mem_range.mp hj
  rw [show 2 * S + 1 - 1 - j = 2 * S - j by omega, Nat.cast_sub (by omega)]
  congr 2
  push_cast
  ring

private theorem sum_reflect_symm {S : ℕ} {ψ : ℕ → ℝ} (hψ : IsLaurentSymm S ψ) (g : ℝ → ℝ) :
    ∑ j ∈ range (2 * S + 1), ψ j * g ((j : ℝ) - S) =
      ∑ j ∈ range (2 * S + 1), ψ j * g (-((j : ℝ) - S)) := by
  rw [sum_reflect]
  exact sum_congr rfl fun j hj ↦ by rw [hψ j (mem_range.mp hj)]

private theorem sum_reflect_anti {S : ℕ} {ψ : ℕ → ℝ} (hψ : IsLaurentAnti S ψ) (g : ℝ → ℝ) :
    ∑ j ∈ range (2 * S + 1), ψ j * g ((j : ℝ) - S) =
      -∑ j ∈ range (2 * S + 1), ψ j * g (-((j : ℝ) - S)) := by
  rw [sum_reflect, ← sum_neg_distrib]
  exact sum_congr rfl fun j hj ↦ by rw [hψ j (mem_range.mp hj)]; ring

private theorem freq_add (T S i j : ℕ) (θ : ℝ) :
    (((i : ℝ) - T) * θ) + (((j : ℝ) - S) * θ) = (((i + j : ℕ) : ℝ) - (T + S : ℕ)) * θ := by
  push_cast; ring

/-- A cosine series times a symmetric cosine series. -/
theorem laurentCos_mul_laurentCos {T S : ℕ} (φ : ℕ → ℝ) {ψ : ℕ → ℝ} (hψ : IsLaurentSymm S ψ)
    (θ : ℝ) :
    laurentCos T φ θ * laurentCos S ψ θ = laurentCos (T + S) (laurentConv T S φ ψ) θ := by
  unfold laurentCos
  rw [sum_conv_eq T S φ ψ fun k ↦ Real.cos (((k : ℝ) - (T + S : ℕ)) * θ), sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum]
  have h := sum_reflect_symm hψ fun b ↦ Real.cos (((i : ℝ) - T) * θ - b * θ)
  have e : ∀ j ∈ range (2 * S + 1), φ i * Real.cos (((i : ℝ) - T) * θ) *
      (ψ j * Real.cos (((j : ℝ) - S) * θ)) = φ i * (ψ j * Real.cos ((((i : ℝ) - T) * θ) +
        ((j : ℝ) - S) * θ)) / 2 + φ i * (ψ j * Real.cos ((((i : ℝ) - T) * θ) -
        ((j : ℝ) - S) * θ)) / 2 := fun j _ ↦ by
    rw [Real.cos_add, Real.cos_sub]; ring
  rw [sum_congr rfl e, sum_add_distrib, ← sum_div, ← sum_div, ← mul_sum, ← mul_sum]
  have h' : ∑ j ∈ range (2 * S + 1), ψ j * Real.cos (((i : ℝ) - T) * θ - ((j : ℝ) - S) * θ) =
      ∑ j ∈ range (2 * S + 1), ψ j * Real.cos (((i : ℝ) - T) * θ + ((j : ℝ) - S) * θ) := by
    rw [h]
    exact sum_congr rfl fun j _ ↦ by ring_nf
  rw [h', ← add_div, ← two_mul, mul_div_cancel_left₀ _ (two_ne_zero), mul_sum]
  exact sum_congr rfl fun j _ ↦ by rw [freq_add]; ring

/-- A cosine series times an antisymmetric sine series. -/
theorem laurentCos_mul_laurentSin {T S : ℕ} (φ : ℕ → ℝ) {ψ : ℕ → ℝ} (hψ : IsLaurentAnti S ψ)
    (θ : ℝ) :
    laurentCos T φ θ * laurentSin S ψ θ = laurentSin (T + S) (laurentConv T S φ ψ) θ := by
  unfold laurentCos laurentSin
  rw [sum_conv_eq T S φ ψ fun k ↦ Real.sin (((k : ℝ) - (T + S : ℕ)) * θ), sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum]
  have h := sum_reflect_anti hψ fun b ↦ Real.sin (((i : ℝ) - T) * θ - b * θ)
  have e : ∀ j ∈ range (2 * S + 1), φ i * Real.cos (((i : ℝ) - T) * θ) *
      (ψ j * Real.sin (((j : ℝ) - S) * θ)) = φ i * (ψ j * Real.sin ((((i : ℝ) - T) * θ) +
        ((j : ℝ) - S) * θ)) / 2 - φ i * (ψ j * Real.sin ((((i : ℝ) - T) * θ) -
        ((j : ℝ) - S) * θ)) / 2 := fun j _ ↦ by
    rw [Real.sin_add, Real.sin_sub]; ring
  rw [sum_congr rfl e, sum_sub_distrib, ← sum_div, ← sum_div, ← mul_sum, ← mul_sum]
  have h' : ∑ j ∈ range (2 * S + 1), ψ j * Real.sin (((i : ℝ) - T) * θ - ((j : ℝ) - S) * θ) =
      -∑ j ∈ range (2 * S + 1), ψ j * Real.sin (((i : ℝ) - T) * θ + ((j : ℝ) - S) * θ) := by
    rw [h]
    congr 1
    exact sum_congr rfl fun j _ ↦ by ring_nf
  have hY : ∑ j ∈ range (2 * S + 1), φ i * ψ j *
      Real.sin ((((i + j : ℕ) : ℝ) - (T + S : ℕ)) * θ) = φ i * ∑ j ∈ range (2 * S + 1),
        ψ j * Real.sin (((i : ℝ) - T) * θ + ((j : ℝ) - S) * θ) := by
    rw [mul_sum]; exact sum_congr rfl fun j _ ↦ by rw [freq_add]; ring
  rw [h', hY]
  ring

/-- A sine series times a symmetric cosine series. -/
theorem laurentSin_mul_laurentCos {T S : ℕ} (φ : ℕ → ℝ) {ψ : ℕ → ℝ} (hψ : IsLaurentSymm S ψ)
    (θ : ℝ) :
    laurentSin T φ θ * laurentCos S ψ θ = laurentSin (T + S) (laurentConv T S φ ψ) θ := by
  unfold laurentCos laurentSin
  rw [sum_conv_eq T S φ ψ fun k ↦ Real.sin (((k : ℝ) - (T + S : ℕ)) * θ), sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum]
  have h := sum_reflect_symm hψ fun b ↦ Real.sin (((i : ℝ) - T) * θ - b * θ)
  have e : ∀ j ∈ range (2 * S + 1), φ i * Real.sin (((i : ℝ) - T) * θ) *
      (ψ j * Real.cos (((j : ℝ) - S) * θ)) = φ i * (ψ j * Real.sin ((((i : ℝ) - T) * θ) +
        ((j : ℝ) - S) * θ)) / 2 + φ i * (ψ j * Real.sin ((((i : ℝ) - T) * θ) -
        ((j : ℝ) - S) * θ)) / 2 := fun j _ ↦ by
    rw [Real.sin_add, Real.sin_sub]; ring
  rw [sum_congr rfl e, sum_add_distrib, ← sum_div, ← sum_div, ← mul_sum, ← mul_sum]
  have h' : ∑ j ∈ range (2 * S + 1), ψ j * Real.sin (((i : ℝ) - T) * θ - ((j : ℝ) - S) * θ) =
      ∑ j ∈ range (2 * S + 1), ψ j * Real.sin (((i : ℝ) - T) * θ + ((j : ℝ) - S) * θ) := by
    rw [h]
    exact sum_congr rfl fun j _ ↦ by ring_nf
  rw [h', ← add_div, ← two_mul, mul_div_cancel_left₀ _ two_ne_zero, mul_sum]
  exact sum_congr rfl fun j _ ↦ by rw [freq_add]; ring

/-- A sine series times an antisymmetric sine series. -/
theorem laurentSin_mul_laurentSin {T S : ℕ} (φ : ℕ → ℝ) {ψ : ℕ → ℝ} (hψ : IsLaurentAnti S ψ)
    (θ : ℝ) :
    laurentSin T φ θ * laurentSin S ψ θ = -laurentCos (T + S) (laurentConv T S φ ψ) θ := by
  unfold laurentCos laurentSin
  rw [sum_conv_eq T S φ ψ fun k ↦ Real.cos (((k : ℝ) - (T + S : ℕ)) * θ), sum_mul,
    ← sum_neg_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum]
  have h := sum_reflect_anti hψ fun b ↦ Real.cos (((i : ℝ) - T) * θ - b * θ)
  have e : ∀ j ∈ range (2 * S + 1), φ i * Real.sin (((i : ℝ) - T) * θ) *
      (ψ j * Real.sin (((j : ℝ) - S) * θ)) = φ i * (ψ j * Real.cos ((((i : ℝ) - T) * θ) -
        ((j : ℝ) - S) * θ)) / 2 - φ i * (ψ j * Real.cos ((((i : ℝ) - T) * θ) +
        ((j : ℝ) - S) * θ)) / 2 := fun j _ ↦ by
    rw [Real.cos_add, Real.cos_sub]; ring
  rw [sum_congr rfl e, sum_sub_distrib, ← sum_div, ← sum_div, ← mul_sum, ← mul_sum]
  have h' : ∑ j ∈ range (2 * S + 1), ψ j * Real.cos (((i : ℝ) - T) * θ - ((j : ℝ) - S) * θ) =
      -∑ j ∈ range (2 * S + 1), ψ j * Real.cos (((i : ℝ) - T) * θ + ((j : ℝ) - S) * θ) := by
    rw [h]
    congr 1
    exact sum_congr rfl fun j _ ↦ by ring_nf
  have hY : ∑ j ∈ range (2 * S + 1), φ i * ψ j *
      Real.cos ((((i + j : ℕ) : ℝ) - (T + S : ℕ)) * θ) = φ i * ∑ j ∈ range (2 * S + 1),
        ψ j * Real.cos (((i : ℝ) - T) * θ + ((j : ℝ) - S) * θ) := by
    rw [mul_sum]; exact sum_congr rfl fun j _ ↦ by rw [freq_add]; ring
  rw [h', hY]
  ring

/-- A cosine series on a larger window. -/
theorem laurentCos_widen (T d : ℕ) (φ : ℕ → ℝ) (θ : ℝ) :
    laurentCos T φ θ = laurentCos (T + d) (laurentShift T d φ) θ := by
  unfold laurentCos laurentShift
  rw [sum_ite_shift (by omega) φ fun k ↦ Real.cos (((k : ℝ) - (T + d : ℕ)) * θ)]
  refine sum_congr rfl fun i _ ↦ ?_
  congr 2
  push_cast
  ring

/-- A sine series on a larger window. -/
theorem laurentSin_widen (T d : ℕ) (φ : ℕ → ℝ) (θ : ℝ) :
    laurentSin T φ θ = laurentSin (T + d) (laurentShift T d φ) θ := by
  unfold laurentSin laurentShift
  rw [sum_ite_shift (by omega) φ fun k ↦ Real.sin (((k : ℝ) - (T + d : ℕ)) * θ)]
  refine sum_congr rfl fun i _ ↦ ?_
  congr 2
  push_cast
  ring

/-! ### Symmetry and parity of products -/

private theorem laurentConv_reflect (T S : ℕ) (φ ψ : ℕ → ℝ) {k : ℕ} (hk : k < 2 * (T + S) + 1) :
    laurentConv T S φ ψ (2 * (T + S) - k) = ∑ i ∈ range (2 * T + 1),
      φ (2 * T - i) * (if i ≤ k ∧ k - i < 2 * S + 1 then ψ (2 * S - (k - i)) else 0) := by
  unfold laurentConv
  rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [show 2 * T + 1 - 1 - i = 2 * T - i by omega]
  congr 1
  by_cases h : i ≤ k ∧ k - i < 2 * S + 1
  · rw [ite_eq_left (show 2 * T - i ≤ 2 * (T + S) - k ∧ 2 * (T + S) - k - (2 * T - i) <
      2 * S + 1 by omega), ite_eq_left h, show 2 * (T + S) - k - (2 * T - i) =
      2 * S - (k - i) by omega]
  · rw [ite_eq_right (show ¬ (2 * T - i ≤ 2 * (T + S) - k ∧ 2 * (T + S) - k - (2 * T - i) <
      2 * S + 1) by omega), ite_eq_right h]

private theorem laurentConv_reflect_eq {T S : ℕ} {φ ψ : ℕ → ℝ} (a b : ℝ)
    (hφ : ∀ i < 2 * T + 1, φ (2 * T - i) = a * φ i)
    (hψ : ∀ j < 2 * S + 1, ψ (2 * S - j) = b * ψ j) {k : ℕ} (hk : k < 2 * (T + S) + 1) :
    laurentConv T S φ ψ (2 * (T + S) - k) = a * b * laurentConv T S φ ψ k := by
  rw [laurentConv_reflect T S φ ψ hk, laurentConv, mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [hφ i (mem_range.mp hi)]
  split_ifs with h
  · rw [hψ _ h.2]; ring
  · ring

theorem IsLaurentSymm.conv {T S : ℕ} {φ ψ : ℕ → ℝ} (hφ : IsLaurentSymm T φ)
    (hψ : IsLaurentSymm S ψ) : IsLaurentSymm (T + S) (laurentConv T S φ ψ) := fun k hk ↦ by
  rw [laurentConv_reflect_eq 1 1 (fun i hi ↦ by rw [hφ i hi, one_mul])
    (fun j hj ↦ by rw [hψ j hj, one_mul]) hk, one_mul, one_mul]

theorem IsLaurentSymm.conv_anti {T S : ℕ} {φ ψ : ℕ → ℝ} (hφ : IsLaurentSymm T φ)
    (hψ : IsLaurentAnti S ψ) : IsLaurentAnti (T + S) (laurentConv T S φ ψ) := fun k hk ↦ by
  rw [laurentConv_reflect_eq 1 (-1) (fun i hi ↦ by rw [hφ i hi, one_mul])
    (fun j hj ↦ by rw [hψ j hj, neg_one_mul]) hk]
  ring

theorem IsLaurentAnti.conv_symm {T S : ℕ} {φ ψ : ℕ → ℝ} (hφ : IsLaurentAnti T φ)
    (hψ : IsLaurentSymm S ψ) : IsLaurentAnti (T + S) (laurentConv T S φ ψ) := fun k hk ↦ by
  rw [laurentConv_reflect_eq (-1) 1 (fun i hi ↦ by rw [hφ i hi, neg_one_mul])
    (fun j hj ↦ by rw [hψ j hj, one_mul]) hk]
  ring

theorem IsLaurentAnti.conv {T S : ℕ} {φ ψ : ℕ → ℝ} (hφ : IsLaurentAnti T φ)
    (hψ : IsLaurentAnti S ψ) : IsLaurentSymm (T + S) (laurentConv T S φ ψ) := fun k hk ↦ by
  rw [laurentConv_reflect_eq (-1) (-1) (fun i hi ↦ by rw [hφ i hi, neg_one_mul])
    (fun j hj ↦ by rw [hψ j hj, neg_one_mul]) hk]
  ring

theorem HasLaurentParity.conv {T S r s : ℕ} {φ ψ : ℕ → ℝ} (hφ : HasLaurentParity r φ)
    (hψ : HasLaurentParity s ψ) : HasLaurentParity ((r + s) % 2) (laurentConv T S φ ψ) := by
  intro k hk
  obtain ⟨i, _, hne⟩ := exists_ne_zero_of_sum_ne_zero hk
  have h1 : φ i ≠ 0 := left_ne_zero_of_mul hne
  have h2 := right_ne_zero_of_mul hne
  split_ifs at h2 with h
  · have e1 := hφ i h1
    have e2 := hψ _ h2
    omega
  · exact absurd rfl h2

theorem IsLaurentSymm.shift {T : ℕ} {φ : ℕ → ℝ} (hφ : IsLaurentSymm T φ) (d : ℕ) :
    IsLaurentSymm (T + d) (laurentShift T d φ) := fun i hi ↦ by
  unfold laurentShift
  by_cases h : d ≤ i ∧ i - d < 2 * T + 1
  · rw [ite_eq_left (show d ≤ 2 * (T + d) - i ∧ 2 * (T + d) - i - d < 2 * T + 1 by omega),
      ite_eq_left h, show 2 * (T + d) - i - d = 2 * T - (i - d) by omega, hφ _ h.2]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem IsLaurentAnti.shift {T : ℕ} {φ : ℕ → ℝ} (hφ : IsLaurentAnti T φ) (d : ℕ) :
    IsLaurentAnti (T + d) (laurentShift T d φ) := fun i hi ↦ by
  unfold laurentShift
  by_cases h : d ≤ i ∧ i - d < 2 * T + 1
  · rw [ite_eq_left (show d ≤ 2 * (T + d) - i ∧ 2 * (T + d) - i - d < 2 * T + 1 by omega),
      ite_eq_left h, show 2 * (T + d) - i - d = 2 * T - (i - d) by omega, hφ _ h.2]
  · rw [ite_eq_right h, ite_eq_right (by omega), neg_zero]

theorem HasLaurentParity.shift {T r : ℕ} {φ : ℕ → ℝ} (hφ : HasLaurentParity r φ) (d : ℕ) :
    HasLaurentParity ((r + d) % 2) (laurentShift T d φ) := by
  intro i hi
  unfold laurentShift at hi
  split_ifs at hi with h
  · have := hφ _ hi
    omega
  · exact absurd rfl hi

end PDE.Analysis
