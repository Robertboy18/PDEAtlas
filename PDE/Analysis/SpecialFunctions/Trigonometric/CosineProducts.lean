/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
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
a sine sum have the same form (`sum_sin_mul_sum_sin`, `sum_cos_mul_sum_sin`). All three are the
one statement `sum_mul_sum_of_mul_eq`, for any functions with a product-to-sum rule
`f x * g y = (F (x + y) + G (x - y)) / 2`, at the three rules for cosines and sines. Both
convolutions are slots of one natural multiplication of packed rows (`slot_packSlots_mul`).
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

/-- **Products of two sums collected by frequency.** Let `f x * g y = (F (x + y) + G (x - y)) / 2`
for all real `x`, `y`. Then the product of the sums of `u_j f ((2j + a) θ)` and
`v_j' g ((2j' + b) θ)` is half the sum of the `F` sum with the convolution `u * v` at the
frequencies `2k + a + b` and of the `G` sum with the convolution of `u` and the reversed `v` at
the frequencies `2 (d - (J' - 1)) + a - b`. -/
theorem sum_mul_sum_of_mul_eq {f g F G : ℝ → ℝ}
    (hfg : ∀ x y, f x * g y = (F (x + y) + G (x - y)) / 2)
    (J J' : ℕ) (u v : ℕ → ℕ) (a b : ℕ) (θ : ℝ) :
    (∑ j ∈ range J, (u j : ℝ) * f ((2 * j + a : ℕ) * θ)) *
        (∑ j' ∈ range J', (v j' : ℝ) * g ((2 * j' + b : ℕ) * θ)) =
      (∑ k ∈ range (J + J'), (packedConvolution J J' u v k : ℝ) *
          F ((2 * k + a + b : ℕ) * θ) +
        ∑ d ∈ range (J + J'), (packedConvolution J J' u (reverseCoeffs J' v) d : ℝ) *
          G (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ)) / 2 := by
  rw [sum_conv_mul u v (fun k ↦ F ((2 * k + a + b : ℕ) * θ)),
    sum_conv_mul u (reverseCoeffs J' v)
      (fun d ↦ G (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ))]
  rw [sum_mul_sum, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_rev_eq u v a b j G θ, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun j' _ ↦ ?_
  have hc : f ((2 * j + a : ℕ) * θ) * g ((2 * j' + b : ℕ) * θ) =
      (F (((2 * (j + j') + a + b : ℕ) : ℝ) * θ) +
        G (((2 * ((j : ℤ) - j') + a - b : ℤ) : ℝ) * θ)) / 2 := by
    rw [show (((2 * (j + j') + a + b : ℕ) : ℝ) * θ) =
        ((2 * j + a : ℕ) * θ) + ((2 * j' + b : ℕ) * θ) by push_cast; ring,
      show (((2 * ((j : ℤ) - j') + a - b : ℤ) : ℝ) * θ) =
        ((2 * j + a : ℕ) * θ) - ((2 * j' + b : ℕ) * θ) by push_cast; ring]
    exact hfg _ _
  calc (u j : ℝ) * f ((2 * j + a : ℕ) * θ) * ((v j' : ℝ) * g ((2 * j' + b : ℕ) * θ))
      = (u j : ℝ) * v j' * (f ((2 * j + a : ℕ) * θ) * g ((2 * j' + b : ℕ) * θ)) := by
        ring
    _ = _ := by rw [hc]; push_cast; ring

/-- The product of two cosine sums collected by frequency. -/
theorem sum_cos_mul_sum_cos (J J' : ℕ) (u v : ℕ → ℕ) (a b : ℕ) (θ : ℝ) :
    (∑ j ∈ range J, (u j : ℝ) * Real.cos ((2 * j + a : ℕ) * θ)) *
        (∑ j' ∈ range J', (v j' : ℝ) * Real.cos ((2 * j' + b : ℕ) * θ)) =
      (∑ k ∈ range (J + J'), (packedConvolution J J' u v k : ℝ) *
          Real.cos ((2 * k + a + b : ℕ) * θ) +
        ∑ d ∈ range (J + J'), (packedConvolution J J' u (reverseCoeffs J' v) d : ℝ) *
          Real.cos (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ)) / 2 :=
  sum_mul_sum_of_mul_eq (f := Real.cos) (g := Real.cos) (F := Real.cos) (G := Real.cos)
    (fun x y ↦ by rw [Real.cos_add, Real.cos_sub]; ring) J J' u v a b θ

/-- The product of two sine sums collected by frequency. -/
theorem sum_sin_mul_sum_sin (J J' : ℕ) (u v : ℕ → ℕ) (a b : ℕ) (θ : ℝ) :
    (∑ j ∈ range J, (u j : ℝ) * Real.sin ((2 * j + a : ℕ) * θ)) *
        (∑ j' ∈ range J', (v j' : ℝ) * Real.sin ((2 * j' + b : ℕ) * θ)) =
      (∑ d ∈ range (J + J'), (packedConvolution J J' u (reverseCoeffs J' v) d : ℝ) *
          Real.cos (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ) -
        ∑ k ∈ range (J + J'), (packedConvolution J J' u v k : ℝ) *
          Real.cos ((2 * k + a + b : ℕ) * θ)) / 2 := by
  rw [sum_mul_sum_of_mul_eq (f := Real.sin) (g := Real.sin) (F := fun x ↦ -Real.cos x)
    (G := Real.cos) (fun x y ↦ by rw [Real.cos_add, Real.cos_sub]; ring) J J' u v a b θ]
  simp only [mul_neg, sum_neg_distrib]
  ring

/-- The product of a cosine sum and a sine sum collected by frequency. -/
theorem sum_cos_mul_sum_sin (J J' : ℕ) (u v : ℕ → ℕ) (a b : ℕ) (θ : ℝ) :
    (∑ j ∈ range J, (u j : ℝ) * Real.cos ((2 * j + a : ℕ) * θ)) *
        (∑ j' ∈ range J', (v j' : ℝ) * Real.sin ((2 * j' + b : ℕ) * θ)) =
      (∑ k ∈ range (J + J'), (packedConvolution J J' u v k : ℝ) *
          Real.sin ((2 * k + a + b : ℕ) * θ) -
        ∑ d ∈ range (J + J'), (packedConvolution J J' u (reverseCoeffs J' v) d : ℝ) *
          Real.sin (((2 * ((d : ℤ) - (J' - 1)) + a - b : ℤ) : ℝ) * θ)) / 2 := by
  rw [sum_mul_sum_of_mul_eq (f := Real.cos) (g := Real.sin) (F := Real.sin)
    (G := fun x ↦ -Real.sin x) (fun x y ↦ by rw [Real.sin_add, Real.sin_sub]; ring) J J' u v a b θ]
  simp only [mul_neg, sum_neg_distrib]
  ring

end PDE.Analysis
