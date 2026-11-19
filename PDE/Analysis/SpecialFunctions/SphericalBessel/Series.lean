/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Basic

/-!
# Partial sums of the spherical Bessel series

The reduced series `g_l x = ∑ (-1) ^ k a_k` alternates, with magnitudes
`a_k = (x ^ 2 / 2) ^ k / (k! (2l + 2k + 1)‼)` and ratios
`a_{k+1} / a_k = x ^ 2 / (2 (k + 1) (2l + 2k + 3))`. Once `x ^ 2 ≤ 2 (K + 1) (2l + 2K + 3)` the
magnitudes decrease from index `K` on, so `g_l x` lies between the partial sums with `K` and
`K + 1` terms. In particular the tail after `K` terms is at most the first omitted magnitude;
for `|x| ≤ l + 10` this holds as soon as `l + 10 ≤ 2K + 2`. No cancellation enters these
bounds, so they apply in the regime `|x| ≲ l` where the Rayleigh form cancels.

## Main results

* `reducedSphericalBesselJ_sub_sum_mem`: `(-1) ^ K (g_l x - S_K) ∈ [0, a_K]`.
* `abs_reducedSphericalBesselJ_sub_sum_le`: `|g_l x - S_K| ≤ a_K`.
* `abs_sphericalBesselJ_sub_sum_le_of_abs_le`: for `|x| ≤ l + 10` and `l + 10 ≤ 2K + 2`,
  `|j_l x - x ^ l S_K| ≤ |x| ^ l a_K`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open Nat Filter Set
open scoped Topology

/-- The magnitude `(x ^ 2 / 2) ^ k / (k! (2l + 2k + 1)‼)` of the `k`-th term. -/
def sphericalBesselTermAbs (l k : ℕ) (x : ℝ) : ℝ :=
  (x ^ 2 / 2) ^ k / (k ! * (2 * l + 2 * k + 1)‼)

/-- The terms alternate in sign. -/
theorem sphericalBesselTerm_eq_neg_one_pow_mul (l k : ℕ) (x : ℝ) :
    sphericalBesselTerm l k x = (-1) ^ k * sphericalBesselTermAbs l k x := by
  unfold sphericalBesselTerm sphericalBesselTermAbs
  rw [neg_div, neg_pow, mul_div_assoc]

/-- The magnitudes are nonnegative. -/
theorem sphericalBesselTermAbs_nonneg (l k : ℕ) (x : ℝ) : 0 ≤ sphericalBesselTermAbs l k x := by
  have := sphericalBesselTerm_denom_pos l k
  unfold sphericalBesselTermAbs
  positivity

/-- Consecutive magnitudes have ratio `x ^ 2 / (2 (k + 1) (2l + 2k + 3))`. -/
theorem sphericalBesselTermAbs_succ (l k : ℕ) (x : ℝ) :
    sphericalBesselTermAbs l (k + 1) x =
      sphericalBesselTermAbs l k x * (x ^ 2 / (2 * (k + 1) * (2 * l + 2 * k + 3))) := by
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hd : (0 : ℝ) < ((2 * l + 2 * k + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  unfold sphericalBesselTermAbs
  rw [doubleFactorial_succ_index, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The magnitudes decrease at index `k` when `x ^ 2 ≤ 2 (k + 1) (2l + 2k + 3)`. -/
theorem sphericalBesselTermAbs_succ_le {l k : ℕ} {x : ℝ}
    (h : x ^ 2 ≤ 2 * (k + 1) * (2 * l + 2 * k + 3)) :
    sphericalBesselTermAbs l (k + 1) x ≤ sphericalBesselTermAbs l k x := by
  rw [sphericalBesselTermAbs_succ]
  have hpos : (0 : ℝ) < 2 * (k + 1) * (2 * l + 2 * k + 3) := by positivity
  exact mul_le_of_le_one_right (sphericalBesselTermAbs_nonneg l k x)
    ((div_le_one hpos).mpr h)

/-- The magnitudes decrease from index `K` on when `x ^ 2 ≤ 2 (K + 1) (2l + 2K + 3)`. -/
theorem antitone_sphericalBesselTermAbs {l K : ℕ} {x : ℝ}
    (h : x ^ 2 ≤ 2 * (K + 1) * (2 * l + 2 * K + 3)) :
    Antitone fun i ↦ sphericalBesselTermAbs l (K + i) x := by
  refine antitone_nat_of_succ_le fun i ↦ ?_
  rw [← add_assoc]
  apply sphericalBesselTermAbs_succ_le
  refine h.trans ?_
  push_cast
  gcongr <;> linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]

/-- The magnitudes are summable. -/
theorem summable_sphericalBesselTermAbs (l : ℕ) (x : ℝ) :
    Summable fun k ↦ sphericalBesselTermAbs l k x := by
  refine (summable_sphericalBesselTerm l x).abs.congr fun k ↦ ?_
  rw [sphericalBesselTerm_eq_neg_one_pow_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg (sphericalBesselTermAbs_nonneg l k x)]

/-- **Alternating tail bound.** If `x ^ 2 ≤ 2 (K + 1) (2l + 2K + 3)`, the remainder after `K`
terms satisfies `0 ≤ (-1) ^ K (g_l x - S_K) ≤ a_K`. -/
theorem reducedSphericalBesselJ_sub_sum_mem {l K : ℕ} {x : ℝ}
    (h : x ^ 2 ≤ 2 * (K + 1) * (2 * l + 2 * K + 3)) :
    0 ≤ (-1) ^ K * (reducedSphericalBesselJ l x -
        ∑ k ∈ Finset.range K, sphericalBesselTerm l k x) ∧
      (-1) ^ K * (reducedSphericalBesselJ l x -
        ∑ k ∈ Finset.range K, sphericalBesselTerm l k x) ≤ sphericalBesselTermAbs l K x := by
  set f : ℕ → ℝ := fun i ↦ sphericalBesselTermAbs l (K + i) x with hf
  have hanti : Antitone f := antitone_sphericalBesselTermAbs h
  have hfs : Summable f := by
    have := (summable_nat_add_iff K).mpr (summable_sphericalBesselTermAbs l x)
    simpa only [hf, add_comm K] using this
  have htail : reducedSphericalBesselJ l x - ∑ k ∈ Finset.range K, sphericalBesselTerm l k x =
      (-1) ^ K * ∑' i, (-1) ^ i * f i := by
    unfold reducedSphericalBesselJ
    rw [← (summable_sphericalBesselTerm l x).sum_add_tsum_nat_add K, add_sub_cancel_left,
      ← tsum_mul_left]
    congr 1
    funext i
    rw [sphericalBesselTerm_eq_neg_one_pow_mul, hf, pow_add, add_comm i K]
    ring
  have hsq : ((-1 : ℝ) ^ K) * (-1) ^ K = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [htail, ← mul_assoc, hsq, one_mul]
  have hlim := hfs.tendsto_alternating_series_tsum
  constructor
  · simpa using hanti.alternating_series_le_tendsto hlim 0
  · simpa [hf] using hanti.tendsto_le_alternating_series hlim 0

/-- If `x ^ 2 ≤ 2 (K + 1) (2l + 2K + 3)`, the tail after `K` terms is at most `a_K`. -/
theorem abs_reducedSphericalBesselJ_sub_sum_le {l K : ℕ} {x : ℝ}
    (h : x ^ 2 ≤ 2 * (K + 1) * (2 * l + 2 * K + 3)) :
    |reducedSphericalBesselJ l x - ∑ k ∈ Finset.range K, sphericalBesselTerm l k x| ≤
      sphericalBesselTermAbs l K x := by
  obtain ⟨h₁, h₂⟩ := reducedSphericalBesselJ_sub_sum_mem h
  have habs : |(-1 : ℝ) ^ K| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
  calc |reducedSphericalBesselJ l x - ∑ k ∈ Finset.range K, sphericalBesselTerm l k x|
      = |(-1) ^ K * (reducedSphericalBesselJ l x -
          ∑ k ∈ Finset.range K, sphericalBesselTerm l k x)| := by rw [abs_mul, habs, one_mul]
    _ ≤ sphericalBesselTermAbs l K x := by rw [abs_of_nonneg h₁]; exact h₂

/-- `x ^ 2 ≤ 2 (K + 1) (2l + 2K + 3)` holds for `|x| ≤ l + 10` once `l + 10 ≤ 2K + 2`. -/
theorem sq_le_of_abs_le_add_ten {l K : ℕ} {x : ℝ} (hx : |x| ≤ l + 10)
    (hK : (l : ℝ) + 10 ≤ 2 * K + 2) :
    x ^ 2 ≤ 2 * (K + 1) * (2 * l + 2 * K + 3) := by
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hsq : x ^ 2 ≤ ((l : ℝ) + 10) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  nlinarith

/-- **Certified series tail for `|x| ≤ l + 10`.** If `l + 10 ≤ 2K + 2`, then
`|j_l x - x ^ l S_K| ≤ |x| ^ l a_K`. -/
theorem abs_sphericalBesselJ_sub_sum_le_of_abs_le {l K : ℕ} {x : ℝ} (hx : |x| ≤ l + 10)
    (hK : (l : ℝ) + 10 ≤ 2 * K + 2) :
    |sphericalBesselJ l x - x ^ l * ∑ k ∈ Finset.range K, sphericalBesselTerm l k x| ≤
      |x| ^ l * sphericalBesselTermAbs l K x := by
  rw [sphericalBesselJ_eq_pow_mul, ← mul_sub, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (abs_reducedSphericalBesselJ_sub_sum_le (sq_le_of_abs_le_add_ten hx hK)) (by positivity)

end PDE.Analysis.SpecialFunctions
