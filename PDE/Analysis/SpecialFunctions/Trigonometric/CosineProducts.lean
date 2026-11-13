/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Numerics.PackedConvolution
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Products of cosine sums collected by frequency

For natural coefficients `u`, `v` and frequencies `2j + a`, `2j' + b`, the product of the two
cosine sums is half the sum of the cosine sums with the convolution `u * v` at the frequencies
`2k + a + b` and with the convolution of `u` and the reversed `v` at the frequencies
`2 (d - (J' - 1)) + a - b` (`sum_cos_mul_sum_cos`); products of two sine sums and of a cosine and
a sine sum have the same form (`sum_sin_mul_sum_sin`, `sum_cos_mul_sum_sin`). Both convolutions
are slots of one natural multiplication of packed rows (`slot_packSlots_mul`).
-/

@[expose] public section

namespace PDE.Analysis

open Finset CAS.Numerics

/-- The reversed coefficients `v (J' - 1 - j)` for `j < J'`. -/
def reverseCoeffs (J' : ℕ) (v : ℕ → ℕ) (j : ℕ) : ℕ := v (J' - 1 - j)

private theorem sum_conv_mul {J J' : ℕ} (u v : ℕ → ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ range (J + J'), (packedConvolution J J' u v k : ℝ) * F k =
      ∑ j ∈ range J, ∑ j' ∈ range J', (u j : ℝ) * v j' * F (j + j') := by
  unfold packedConvolution
  push_cast
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun j' hj' ↦ ?_
  rw [mem_range] at hj hj'
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq (range (J + J')) (j + j') (fun k ↦ (u j : ℝ) * v j' * F k)]
  simp [show j + j' < J + J' by omega]

private theorem sum_rev_eq {J' : ℕ} (u v : ℕ → ℕ) (a b j : ℕ) (G : ℝ → ℝ) (θ : ℝ) :
    ∑ j' ∈ range J', (u j : ℝ) * (reverseCoeffs J' v j' : ℝ) *
        G (((2 * (((j + j' : ℕ) : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ) =
      ∑ j' ∈ range J', (u j : ℝ) * (v j' : ℝ) * G (((2 * ((j : ℤ) - j') + a - b : ℤ) : ℝ) * θ) := by
  refine sum_nbij' (fun j' ↦ J' - 1 - j') (fun j' ↦ J' - 1 - j') ?_ ?_ ?_ ?_ ?_
  · intro j' hj'; simp only [mem_range] at hj' ⊢; omega
  · intro j' hj'; simp only [mem_range] at hj' ⊢; omega
  · intro j' hj'; simp only [mem_range] at hj'; omega
  · intro j' hj'; simp only [mem_range] at hj'; omega
  · intro j' hj'
    simp only [mem_range] at hj'
    unfold reverseCoeffs
    have hz : (2 * (((j + j' : ℕ) : ℤ) - ((J' : ℤ) - 1)) + a - b : ℤ) =
        2 * ((j : ℤ) - ((J' - 1 - j' : ℕ) : ℤ)) + a - b := by omega
    rw [hz]

/-- The product of two cosine sums collected by frequency. -/
theorem sum_cos_mul_sum_cos (J J' : ℕ) (u v : ℕ → ℕ) (a b : ℕ) (θ : ℝ) :
    (∑ j ∈ range J, (u j : ℝ) * Real.cos ((2 * j + a : ℕ) * θ)) *
        (∑ j' ∈ range J', (v j' : ℝ) * Real.cos ((2 * j' + b : ℕ) * θ)) =
      (∑ k ∈ range (J + J'), (packedConvolution J J' u v k : ℝ) *
          Real.cos ((2 * k + a + b : ℕ) * θ) +
        ∑ d ∈ range (J + J'), (packedConvolution J J' u (reverseCoeffs J' v) d : ℝ) *
          Real.cos (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ)) / 2 := by
  rw [sum_conv_mul u v (fun k ↦ Real.cos ((2 * k + a + b : ℕ) * θ)),
    sum_conv_mul u (reverseCoeffs J' v)
      (fun d ↦ Real.cos (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ))]
  rw [sum_mul_sum, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_rev_eq u v a b j Real.cos θ, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun j' _ ↦ ?_
  have hc : Real.cos ((2 * j + a : ℕ) * θ) * Real.cos ((2 * j' + b : ℕ) * θ) =
      (Real.cos (((2 * (j + j') + a + b : ℕ) : ℝ) * θ) +
        Real.cos (((2 * ((j : ℤ) - j') + a - b : ℤ) : ℝ) * θ)) / 2 := by
    rw [show (((2 * (j + j') + a + b : ℕ) : ℝ) * θ) =
        ((2 * j + a : ℕ) * θ) + ((2 * j' + b : ℕ) * θ) by push_cast; ring,
      show (((2 * ((j : ℤ) - j') + a - b : ℤ) : ℝ) * θ) =
        ((2 * j + a : ℕ) * θ) - ((2 * j' + b : ℕ) * θ) by push_cast; ring,
      Real.cos_add, Real.cos_sub]
    ring
  calc (u j : ℝ) * Real.cos ((2 * j + a : ℕ) * θ) * ((v j' : ℝ) * Real.cos ((2 * j' + b : ℕ) * θ))
      = (u j : ℝ) * v j' * (Real.cos ((2 * j + a : ℕ) * θ) * Real.cos ((2 * j' + b : ℕ) * θ)) := by
        ring
    _ = _ := by rw [hc]; push_cast; ring

/-- The product of two sine sums collected by frequency. -/
theorem sum_sin_mul_sum_sin (J J' : ℕ) (u v : ℕ → ℕ) (a b : ℕ) (θ : ℝ) :
    (∑ j ∈ range J, (u j : ℝ) * Real.sin ((2 * j + a : ℕ) * θ)) *
        (∑ j' ∈ range J', (v j' : ℝ) * Real.sin ((2 * j' + b : ℕ) * θ)) =
      (∑ d ∈ range (J + J'), (packedConvolution J J' u (reverseCoeffs J' v) d : ℝ) *
          Real.cos (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ) -
        ∑ k ∈ range (J + J'), (packedConvolution J J' u v k : ℝ) *
          Real.cos ((2 * k + a + b : ℕ) * θ)) / 2 := by
  rw [sum_conv_mul u v (fun k ↦ Real.cos ((2 * k + a + b : ℕ) * θ)),
    sum_conv_mul u (reverseCoeffs J' v)
      (fun d ↦ Real.cos (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ))]
  rw [sum_mul_sum, ← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_rev_eq u v a b j Real.cos θ, ← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun j' _ ↦ ?_
  have hc : Real.sin ((2 * j + a : ℕ) * θ) * Real.sin ((2 * j' + b : ℕ) * θ) =
      (Real.cos (((2 * ((j : ℤ) - j') + a - b : ℤ) : ℝ) * θ) -
        Real.cos (((2 * (j + j') + a + b : ℕ) : ℝ) * θ)) / 2 := by
    rw [show (((2 * (j + j') + a + b : ℕ) : ℝ) * θ) =
        ((2 * j + a : ℕ) * θ) + ((2 * j' + b : ℕ) * θ) by push_cast; ring,
      show (((2 * ((j : ℤ) - j') + a - b : ℤ) : ℝ) * θ) =
        ((2 * j + a : ℕ) * θ) - ((2 * j' + b : ℕ) * θ) by push_cast; ring,
      Real.cos_add, Real.cos_sub]
    ring
  calc (u j : ℝ) * Real.sin ((2 * j + a : ℕ) * θ) * ((v j' : ℝ) * Real.sin ((2 * j' + b : ℕ) * θ))
      = (u j : ℝ) * v j' * (Real.sin ((2 * j + a : ℕ) * θ) * Real.sin ((2 * j' + b : ℕ) * θ)) := by
        ring
    _ = _ := by rw [hc]; push_cast; ring

/-- The product of a cosine sum and a sine sum collected by frequency. -/
theorem sum_cos_mul_sum_sin (J J' : ℕ) (u v : ℕ → ℕ) (a b : ℕ) (θ : ℝ) :
    (∑ j ∈ range J, (u j : ℝ) * Real.cos ((2 * j + a : ℕ) * θ)) *
        (∑ j' ∈ range J', (v j' : ℝ) * Real.sin ((2 * j' + b : ℕ) * θ)) =
      (∑ k ∈ range (J + J'), (packedConvolution J J' u v k : ℝ) *
          Real.sin ((2 * k + a + b : ℕ) * θ) -
        ∑ d ∈ range (J + J'), (packedConvolution J J' u (reverseCoeffs J' v) d : ℝ) *
          Real.sin (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ)) / 2 := by
  rw [sum_conv_mul u v (fun k ↦ Real.sin ((2 * k + a + b : ℕ) * θ)),
    sum_conv_mul u (reverseCoeffs J' v)
      (fun d ↦ Real.sin (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ))]
  rw [sum_mul_sum, ← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_rev_eq u v a b j Real.sin θ, ← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun j' _ ↦ ?_
  have hc : Real.cos ((2 * j + a : ℕ) * θ) * Real.sin ((2 * j' + b : ℕ) * θ) =
      (Real.sin (((2 * (j + j') + a + b : ℕ) : ℝ) * θ) -
        Real.sin (((2 * ((j : ℤ) - j') + a - b : ℤ) : ℝ) * θ)) / 2 := by
    rw [show (((2 * (j + j') + a + b : ℕ) : ℝ) * θ) =
        ((2 * j + a : ℕ) * θ) + ((2 * j' + b : ℕ) * θ) by push_cast; ring,
      show (((2 * ((j : ℤ) - j') + a - b : ℤ) : ℝ) * θ) =
        ((2 * j + a : ℕ) * θ) - ((2 * j' + b : ℕ) * θ) by push_cast; ring,
      Real.sin_add, Real.sin_sub]
    ring
  calc (u j : ℝ) * Real.cos ((2 * j + a : ℕ) * θ) * ((v j' : ℝ) * Real.sin ((2 * j' + b : ℕ) * θ))
      = (u j : ℝ) * v j' * (Real.cos ((2 * j + a : ℕ) * θ) * Real.sin ((2 * j' + b : ℕ) * θ)) := by
        ring
    _ = _ := by rw [hc]; push_cast; ring

end PDE.Analysis
