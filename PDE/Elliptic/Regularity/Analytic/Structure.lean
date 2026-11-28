/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Analytic.FrozenFlux
public import PDE.Elliptic.Regularity.Analytic.Bernstein

/-!
# The structure estimate for the frozen system

## Motivation

If the derivatives of a solution `v` of the autonomous diagonal system obey
`θⁱ |Dⁱv| ≤ i! · 2M · ψ(i) · Bⁱ` at a point for the orders `1 ≤ i ≤ N`, where `θ` is the weight of
a ball, how large is the cross term `|Dᵏv| |Dᵏ(L v)|` of the Bernstein inequality for `k ≤ N`?

## The idea

By `sum_iteratedCoordinateNorm_mul_frozenOperator_le` the cross term is a sum of products of
derivatives of `aᵢⱼ ∘ v` of order `r ≥ 1` with derivatives of `v` of order `k + 2 - r`, plus
derivatives of `f ∘ v`. The derivatives of the compositions are bounded by
`iteratedCoordinateNorm_comp_le_of_convolutionWeight`, and the convolution weight `ψ` absorbs
the binomial sums: `∑ᵣ (k+1 choose r+1) w(r+1) w(k+1-r) ≤ w(k+2)` for `w(i) = i! ψ(i) βⁱ`.

Two terms contain the derivative of order `k + 1`, which for `k = N` is not covered by the
hypothesis: the term `r = 1`, and the linear part of the chain rule in the term `r = k + 1` and
in `f ∘ v`. They are kept, with the small coefficient `M B (k + 1)`. Everything else is
quadratic in `M`. In weighted form, with `X i = θⁱ |Dⁱv|`,

`θ^{2k+2} ∑_l |Dᵏv_l| |Dᵏ(L v_l)| ≤ X k · (c M (k+1) B · X (k+1) + c M² (k+2)! ψ(k+2) B^{k+2})`.

## Main results

* `sum_choose_mul_weight_le`: the binomial sum of the weights, for all `k` and `β ≥ 0`.
* `structure_sum_le`: the arithmetic of the three kinds of terms, for all real sequences with the
  stated bounds.
* `weighted_cross_le`: the weighted estimate above for all solutions, all `1 ≤ k ≤ N`.

## Relations

`weighted_cross_le` combines `sum_iteratedCoordinateNorm_mul_frozenOperator_le`,
`iteratedCoordinateNorm_comp_le_of_convolutionWeight` and `structure_sum_le`. It is the only
place where the equation enters the regularity argument, and it is used in
`PDE.Elliptic.Regularity.Analytic.Improvement`, at two consecutive orders.

## What stays open

The constant `structureConstant` is far from optimal.
-/

@[expose] public noncomputable section

open Filter Set Finset
open scoped ContDiff Topology
open PDE.Analysis

namespace PDE.Elliptic.Regularity.Analytic

/-- **The weights absorb the binomial sum.** For `w(i) = i! ψ(i) βⁱ` with the convolution weight
`ψ` and `β ≥ 0`: `∑_{r ≤ k} (k+1 choose r+1) w(r+1) w(k+1-r) ≤ w(k+2)`. -/
theorem sum_choose_mul_weight_le {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    ∑ r ∈ range (k + 1), ((k + 1).choose (r + 1) : ℝ) *
        ((r + 1).factorial * convolutionWeight (r + 1) * β ^ (r + 1)) *
        ((k + 1 - r).factorial * convolutionWeight (k + 1 - r) * β ^ (k + 1 - r)) ≤
      (k + 2).factorial * convolutionWeight (k + 2) * β ^ (k + 2) := by
  -- the sub-sum of the antidiagonal sum of the weights
  have hψ : ∑ r ∈ range (k + 1), convolutionWeight (r + 1) * convolutionWeight (k + 1 - r) ≤
      convolutionWeight (k + 2) := by
    refine le_trans ?_ (sum_antidiagonal_convolutionWeight_mul_le (k + 2))
    have e1 : ∑ ab ∈ antidiagonal (k + 2), convolutionWeight ab.1 * convolutionWeight ab.2 =
        ∑ i ∈ range (k + 2 + 1), convolutionWeight i * convolutionWeight (k + 2 - i) :=
      Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b ↦ convolutionWeight a * convolutionWeight b) (k + 2)
    have e2 : ∑ i ∈ range (k + 2 + 1), convolutionWeight i * convolutionWeight (k + 2 - i) =
        ∑ i ∈ range (k + 2), convolutionWeight (i + 1) * convolutionWeight (k + 2 - (i + 1)) +
          convolutionWeight 0 * convolutionWeight (k + 2 - 0) :=
      sum_range_succ' _ _
    have e3 : ∑ i ∈ range (k + 2),
        convolutionWeight (i + 1) * convolutionWeight (k + 2 - (i + 1)) =
        ∑ i ∈ range (k + 1), convolutionWeight (i + 1) * convolutionWeight (k + 2 - (i + 1)) +
          convolutionWeight (k + 1 + 1) * convolutionWeight (k + 2 - (k + 1 + 1)) :=
      sum_range_succ _ _
    have e4 : ∑ i ∈ range (k + 1),
        convolutionWeight (i + 1) * convolutionWeight (k + 2 - (i + 1)) =
        ∑ r ∈ range (k + 1), convolutionWeight (r + 1) * convolutionWeight (k + 1 - r) :=
      sum_congr rfl fun i _ ↦ by rw [show k + 2 - (i + 1) = k + 1 - i by omega]
    have h1 := mul_nonneg (convolutionWeight_pos (k + 1 + 1)).le
      (convolutionWeight_pos (k + 2 - (k + 1 + 1))).le
    have h2 := mul_nonneg (convolutionWeight_pos 0).le (convolutionWeight_pos (k + 2 - 0)).le
    rw [e1, e2, e3, e4]
    linarith
  calc ∑ r ∈ range (k + 1), ((k + 1).choose (r + 1) : ℝ) *
        ((r + 1).factorial * convolutionWeight (r + 1) * β ^ (r + 1)) *
        ((k + 1 - r).factorial * convolutionWeight (k + 1 - r) * β ^ (k + 1 - r))
      ≤ ∑ r ∈ range (k + 1), ((k + 2).factorial : ℝ) * β ^ (k + 2) *
          (convolutionWeight (r + 1) * convolutionWeight (k + 1 - r)) := by
        refine sum_le_sum fun r hr ↦ ?_
        have hrk : r ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hr)
        have hfac : ((k + 1).choose (r + 1) : ℝ) * (r + 1).factorial * (k + 1 - r).factorial ≤
            (k + 2).factorial := by
          have h1 : (k + 1).choose (r + 1) * (r + 1).factorial * (k - r).factorial =
              (k + 1).factorial := by
            have := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_succ hrk)
            rwa [Nat.succ_sub_succ] at this
          have h2 : (k + 1 - r).factorial = (k + 1 - r) * (k - r).factorial := by
            rw [show k + 1 - r = (k - r) + 1 by omega, Nat.factorial_succ]
          have h3 : (k + 1).choose (r + 1) * (r + 1).factorial * (k + 1 - r).factorial ≤
              (k + 2).factorial := by
            rw [h2, ← mul_assoc, mul_right_comm _ (k + 1 - r), h1, Nat.factorial_succ (k + 1),
              mul_comm]
            exact Nat.mul_le_mul_right _ (by omega)
          exact_mod_cast h3
        have hpow : β ^ (r + 1) * β ^ (k + 1 - r) = β ^ (k + 2) := by
          rw [← pow_add]; congr 1; omega
        have hw : 0 ≤ convolutionWeight (r + 1) * convolutionWeight (k + 1 - r) * β ^ (k + 2) :=
          mul_nonneg (mul_nonneg (convolutionWeight_pos _).le (convolutionWeight_pos _).le)
            (pow_nonneg hβ _)
        calc ((k + 1).choose (r + 1) : ℝ) *
              ((r + 1).factorial * convolutionWeight (r + 1) * β ^ (r + 1)) *
              ((k + 1 - r).factorial * convolutionWeight (k + 1 - r) * β ^ (k + 1 - r))
            = (((k + 1).choose (r + 1) : ℝ) * (r + 1).factorial * (k + 1 - r).factorial) *
                (convolutionWeight (r + 1) * convolutionWeight (k + 1 - r) *
                  (β ^ (r + 1) * β ^ (k + 1 - r))) := by ring
          _ ≤ ((k + 2).factorial : ℝ) *
                (convolutionWeight (r + 1) * convolutionWeight (k + 1 - r) * β ^ (k + 2)) := by
              rw [hpow]
              exact mul_le_mul_of_nonneg_right hfac hw
          _ = _ := by ring
    _ = ((k + 2).factorial : ℝ) * β ^ (k + 2) *
          ∑ r ∈ range (k + 1), convolutionWeight (r + 1) * convolutionWeight (k + 1 - r) := by
        rw [mul_sum]
    _ ≤ ((k + 2).factorial : ℝ) * β ^ (k + 2) * convolutionWeight (k + 2) :=
        mul_le_mul_of_nonneg_left hψ (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hβ _))
    _ = _ := by ring

/-- **The arithmetic of the structure estimate.** Let `F` be a nonnegative sequence with
`F i ≤ i! c ψ(i) βⁱ` for `1 ≤ i ≤ N`, let
`α r ≤ C K F r + r! ψ(r) βʳ · 2 C (c K)²` for `1 ≤ r ≤ N + 1`, and let `φ` obey the same bound
as `α (k + 1)`, with `c K ≤ 1/2`. Then for `1 ≤ k ≤ N`,
`A₂ ∑_{r ≤ k} (k+1 choose r+1) α(r+1) F(k+1-r) + A₁ φ` is at most a multiple of `F (k + 1)` with
coefficient `A₂ (2k+3) C K c ψ(1) β + A₁ C K`, plus
`A₂ · 2 C K c² · w(k+2) + A₁ · 2 C (c K)² · w(k+1)`, where `w(i) = i! ψ(i) βⁱ`. -/
theorem structure_sum_le {F α : ℕ → ℝ} {C K c β φ A₂ A₁ : ℝ} {N k : ℕ} (hF0 : ∀ i, 0 ≤ F i)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hcK : c * K ≤ 1 / 2) (hA₂ : 0 ≤ A₂)
    (hA₁ : 0 ≤ A₁)
    (hF : ∀ i, 1 ≤ i → i ≤ N → F i ≤ i.factorial * c * convolutionWeight i * β ^ i)
    (hα : ∀ r, 1 ≤ r → r ≤ N + 1 → α r ≤ C * K * F r +
      r.factorial * convolutionWeight r * β ^ r * (2 * C * (c * K) ^ 2))
    (hφ : φ ≤ C * K * F (k + 1) +
      (k + 1).factorial * convolutionWeight (k + 1) * β ^ (k + 1) * (2 * C * (c * K) ^ 2))
    (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    A₂ * ∑ r ∈ range (k + 1), ((k + 1).choose (r + 1) : ℝ) * α (r + 1) * F (k + 1 - r) +
        A₁ * φ ≤
      (A₂ * (2 * k + 3) * (C * K * c * (convolutionWeight 1 * β)) + A₁ * (C * K)) * F (k + 1) +
        (A₂ * (2 * C * K * c ^ 2) *
            ((k + 2).factorial * convolutionWeight (k + 2) * β ^ (k + 2)) +
          A₁ * (2 * C * (c * K) ^ 2) *
            ((k + 1).factorial * convolutionWeight (k + 1) * β ^ (k + 1))) := by
  set w : ℕ → ℝ := fun i ↦ (i.factorial : ℝ) * convolutionWeight i * β ^ i with hw
  have hw0 (i : ℕ) : 0 ≤ w i :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (convolutionWeight_pos i).le) (pow_nonneg hβ i)
  have hw1 : w 1 = convolutionWeight 1 * β := by simp [hw]
  have hCK : 0 ≤ C * K := mul_nonneg hC hK
  have hcK0 : 0 ≤ c * K := mul_nonneg hc hK
  -- the bounds in terms of `w`
  have hF' (i : ℕ) (h1 : 1 ≤ i) (hN : i ≤ N) : F i ≤ c * w i :=
    (hF i h1 hN).trans_eq (by simp only [hw]; ring)
  have hαt (r : ℕ) (h1 : 1 ≤ r) (hN : r ≤ N + 1) :
      α r ≤ C * K * F r + w r * (2 * C * (c * K) ^ 2) := hα r h1 hN
  have hαf (r : ℕ) (h1 : 1 ≤ r) (hN : r ≤ N) : α r ≤ w r * (2 * C * K * c) := by
    have h2 : 2 * C * (c * K) ^ 2 ≤ C * K * c := by
      have h := mul_le_mul_of_nonneg_left hcK (mul_nonneg hCK hc)
      calc 2 * C * (c * K) ^ 2 = 2 * (C * K * c * (c * K)) := by ring
        _ ≤ 2 * (C * K * c * (1 / 2)) := by linarith
        _ = C * K * c := by ring
    have h3 := mul_le_mul_of_nonneg_left (hF' r h1 hN) hCK
    have h4 := mul_le_mul_of_nonneg_left h2 (hw0 r)
    calc α r ≤ C * K * F r + w r * (2 * C * (c * K) ^ 2) := hαt r h1 (Nat.le_succ_of_le hN)
      _ ≤ C * K * (c * w r) + w r * (C * K * c) := add_le_add h3 h4
      _ = w r * (2 * C * K * c) := by ring
  have hαf0 (r : ℕ) : 0 ≤ w r * (2 * C * K * c) := by have := hw0 r; positivity
  -- the binomial sum of the weights, split like the sum to be bounded
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hW := sum_choose_mul_weight_le hβ (k' + 1)
  rw [sum_range_succ, sum_range_succ'] at hW ⊢
  simp only [Nat.add_sub_add_right, Nat.sub_zero, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.add_sub_cancel_left, zero_add] at hW ⊢
  have hch : ((k' + 1 + 1).choose 1 : ℝ) = (k' : ℝ) + 2 := by
    rw [Nat.choose_one_right]; push_cast; ring
  rw [hch] at hW ⊢
  -- the middle terms
  have hmid : ∑ r ∈ range k', ((k' + 1 + 1).choose (r + 1 + 1) : ℝ) * α (r + 1 + 1) *
      F (k' + 1 - r) ≤ 2 * C * K * c ^ 2 * ∑ r ∈ range k',
        ((k' + 1 + 1).choose (r + 1 + 1) : ℝ) * w (r + 1 + 1) * w (k' + 1 - r) := by
    rw [mul_sum]
    refine sum_le_sum fun r hr ↦ ?_
    have hrk : r < k' := mem_range.mp hr
    have h1 := hαf (r + 1 + 1) (by omega) (by omega)
    have h2 := hF' (k' + 1 - r) (by omega) (by omega)
    calc ((k' + 1 + 1).choose (r + 1 + 1) : ℝ) * α (r + 1 + 1) * F (k' + 1 - r)
        ≤ ((k' + 1 + 1).choose (r + 1 + 1) : ℝ) * (w (r + 1 + 1) * (2 * C * K * c)) *
            (c * w (k' + 1 - r)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (hF0 _)
            (mul_nonneg (Nat.cast_nonneg _) (hαf0 _))
      _ = _ := by ring
  -- the two terms that contain `F (k + 1)`
  have hfirst : ((k' : ℝ) + 2) * α 1 * F (k' + 1 + 1) ≤
      ((k' : ℝ) + 2) * (w 1 * (2 * C * K * c)) * F (k' + 1 + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hαf 1 le_rfl (by omega))
      (by positivity)) (hF0 _)
  have hlast : α (k' + 1 + 1) * F 1 ≤
      (C * K * F (k' + 1 + 1) + w (k' + 1 + 1) * (2 * C * (c * K) ^ 2)) * (c * w 1) :=
    mul_le_mul (hαt (k' + 1 + 1) (by omega) (by omega)) (hF' 1 le_rfl (by omega)) (hF0 _)
      (add_nonneg (mul_nonneg hCK (hF0 _)) (mul_nonneg (hw0 _) (by positivity)))
  have hφ' : A₁ * φ ≤ A₁ * (C * K * F (k' + 1 + 1) +
      w (k' + 1 + 1) * (2 * C * (c * K) ^ 2)) := mul_le_mul_of_nonneg_left hφ hA₁
  -- collect
  set Wmid := ∑ r ∈ range k', ((k' + 1 + 1).choose (r + 1 + 1) : ℝ) * w (r + 1 + 1) *
    w (k' + 1 - r)
  set Smid := ∑ r ∈ range k', ((k' + 1 + 1).choose (r + 1 + 1) : ℝ) * α (r + 1 + 1) *
    F (k' + 1 - r)
  have hWmid0 : 0 ≤ Wmid := sum_nonneg fun r _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw0 _)) (hw0 _)
  have hFk := hF0 (k' + 1 + 1)
  have hw10 := hw0 1
  have hwk := hw0 (k' + 1 + 1)
  have hwk2 := hw0 (k' + 1 + 2)
  have hk' : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
  have hW1 : Wmid + ((k' : ℝ) + 2) * w 1 * w (k' + 1 + 1) + w (k' + 1 + 1) * w 1 ≤
      w (k' + 1 + 2) := hW
  rw [hw1] at hfirst hlast hW1
  have e1 : (((k' + 1 : ℕ) : ℝ)) = (k' : ℝ) + 1 := by push_cast; ring
  have eg2 : ((k' + 1 + 2).factorial : ℝ) * convolutionWeight (k' + 1 + 2) * β ^ (k' + 1 + 2) =
      w (k' + 1 + 2) := rfl
  have eg1 : ((k' + 1 + 1).factorial : ℝ) * convolutionWeight (k' + 1 + 1) * β ^ (k' + 1 + 1) =
      w (k' + 1 + 1) := rfl
  rw [e1, eg2, eg1]
  have hψ1β : 0 ≤ convolutionWeight 1 * β := mul_nonneg (convolutionWeight_pos 1).le hβ
  -- `2 C (c K)² c ≤ 2 C K c²` turns the last quadratic term into the common form
  have hq : 2 * C * (c * K) ^ 2 * c ≤ 2 * C * K * c ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcK (mul_nonneg hCK (sq_nonneg c))
    have h' : 0 ≤ C * K * c ^ 2 := mul_nonneg hCK (sq_nonneg c)
    calc 2 * C * (c * K) ^ 2 * c = 2 * (C * K * c ^ 2 * (c * K)) := by ring
      _ ≤ 2 * (C * K * c ^ 2 * (1 / 2)) := by linarith
      _ ≤ 2 * C * K * c ^ 2 := by linarith
  have hW' : Wmid + w (k' + 1 + 1) * (convolutionWeight 1 * β) ≤ w (k' + 1 + 2) := by
    have h0 : 0 ≤ ((k' : ℝ) + 2) * (convolutionWeight 1 * β) * w (k' + 1 + 1) :=
      mul_nonneg (mul_nonneg (by positivity) hψ1β) hwk
    linarith
  have hprod : w (k' + 1 + 1) * (2 * C * (c * K) ^ 2) * (c * (convolutionWeight 1 * β)) ≤
      2 * C * K * c ^ 2 * (w (k' + 1 + 1) * (convolutionWeight 1 * β)) := by
    have hnn : 0 ≤ w (k' + 1 + 1) * (convolutionWeight 1 * β) := mul_nonneg hwk hψ1β
    have h := mul_le_mul_of_nonneg_left hq hnn
    calc w (k' + 1 + 1) * (2 * C * (c * K) ^ 2) * (c * (convolutionWeight 1 * β))
        = w (k' + 1 + 1) * (convolutionWeight 1 * β) * (2 * C * (c * K) ^ 2 * c) := by ring
      _ ≤ w (k' + 1 + 1) * (convolutionWeight 1 * β) * (2 * C * K * c ^ 2) := h
      _ = _ := by ring
  have hmid' := mul_le_mul_of_nonneg_left hmid hA₂
  have hfirst' := mul_le_mul_of_nonneg_left hfirst hA₂
  have hlast' := mul_le_mul_of_nonneg_left hlast hA₂
  have hprod' := mul_le_mul_of_nonneg_left hprod hA₂
  have hfin : A₂ * (2 * C * K * c ^ 2 * (Wmid + w (k' + 1 + 1) * (convolutionWeight 1 * β))) ≤
      A₂ * (2 * C * K * c ^ 2 * w (k' + 1 + 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW' (by positivity)) hA₂
  linarith [hmid', hfirst', hlast', hprod', hfin, hφ']

/-- The coefficient of the top order in the structure estimate, after multiplying by the
weight. -/
private theorem top_coefficient_le {a₂ a₁ CK M B θ β ψ₁ k : ℝ} (ha₂ : 0 ≤ a₂) (ha₁ : 0 ≤ a₁)
    (hCK : 0 ≤ CK) (hM : 0 ≤ M) (hB : 0 ≤ B) (hk : 0 ≤ k) (hψ : ψ₁ ≤ 1) (hβθ : β * θ = B)
    (hθB : θ ≤ M * B) :
    (a₂ * (2 * k + 3) * (CK * (2 * M) * (ψ₁ * β)) + a₁ * CK) * θ ≤
      CK * (12 * a₂ + 4 * a₁) * M * (k + 1) * B := by
  have e : (a₂ * (2 * k + 3) * (CK * (2 * M) * (ψ₁ * β)) + a₁ * CK) * θ =
      a₂ * (2 * k + 3) * (CK * (2 * M)) * B * ψ₁ + a₁ * CK * θ := by rw [← hβθ]; ring
  have h2 : a₂ * (2 * k + 3) * (CK * (2 * M)) * B * ψ₁ ≤
      a₂ * (2 * k + 3) * (CK * (2 * M)) * B * 1 := mul_le_mul_of_nonneg_left hψ (by positivity)
  have h3 : a₁ * CK * θ ≤ a₁ * CK * (M * B) := mul_le_mul_of_nonneg_left hθB (by positivity)
  have h4 : 0 ≤ a₂ * CK * M * B * k := by positivity
  have h5 : 0 ≤ a₁ * CK * M * B * k := by positivity
  have h6 : 0 ≤ a₂ * CK * M * B := by positivity
  have h7 : 0 ≤ a₁ * CK * M * B := by positivity
  rw [e]
  linarith

/-- The quadratic remainder in the structure estimate, after multiplying by the weight. -/
private theorem remainder_le {a₂ a₁ C K M W₂ W₁ β₂ β₁ Θ P Q : ℝ} (ha₂ : 0 ≤ a₂) (ha₁ : 0 ≤ a₁)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hW₂ : 0 ≤ W₂) (hW : W₁ ≤ 4 * W₂) (hP : 0 ≤ P)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ M * P) (h₂ : β₂ * Θ = P) (h₁ : β₁ * Θ = Q) (hKM : K * M ≤ 1 / 8) :
    (a₂ * (2 * C * K * (2 * M) ^ 2) * (W₂ * β₂) +
        a₁ * (2 * C * (2 * M * K) ^ 2) * (W₁ * β₁)) * Θ ≤
      C * K * (12 * a₂ + 4 * a₁) * M ^ 2 * (W₂ * P) := by
  have e : (a₂ * (2 * C * K * (2 * M) ^ 2) * (W₂ * β₂) +
      a₁ * (2 * C * (2 * M * K) ^ 2) * (W₁ * β₁)) * Θ =
      a₂ * (2 * C * K * (2 * M) ^ 2) * (W₂ * P) +
        a₁ * (2 * C * (2 * M * K) ^ 2) * (W₁ * Q) := by rw [← h₂, ← h₁]; ring
  have h1 : W₁ * Q ≤ (4 * W₂) * (M * P) := mul_le_mul hW hQ hQ0 (by positivity)
  have h2 : a₁ * (2 * C * (2 * M * K) ^ 2) * (W₁ * Q) ≤
      a₁ * (2 * C * (2 * M * K) ^ 2) * ((4 * W₂) * (M * P)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : (K * M) * (a₁ * C * K * M ^ 2 * (W₂ * P)) ≤
      (1 / 8) * (a₁ * C * K * M ^ 2 * (W₂ * P)) :=
    mul_le_mul_of_nonneg_right hKM (by positivity)
  have h4 : 0 ≤ a₂ * C * K * M ^ 2 * (W₂ * P) := by positivity
  rw [e]
  linarith

variable {n : ℕ} {I : Type*} [Fintype I] {a : Fin n → Fin n → (I → ℝ) → ℝ}
  {f : I → Fin n → (I → ℝ) → ℝ} {v : ℝ^n → I → ℝ}

/-- The constant of the structure estimate: `C K (12 n² + 4 n |I|)`, where `C`, `K` bound the
derivatives of the coefficients and of the forcing by `m! C Kᵐ`. -/
def structureConstant (n : ℕ) (I : Type*) [Fintype I] (C K : ℝ) : ℝ :=
  C * K * (12 * (n : ℝ) ^ 2 + 4 * (n * Fintype.card I))

/-- The structure constant is nonnegative. -/
theorem structureConstant_nonneg (n : ℕ) (I : Type*) [Fintype I] {C K : ℝ} (hC : 0 ≤ C)
    (hK : 0 ≤ K) : 0 ≤ structureConstant n I C K := by
  unfold structureConstant
  positivity

/-- **The structure estimate.** Let `v` be a smooth solution of the autonomous diagonal system
on an open set `U`, with coefficients and forcing smooth along `v` and with derivatives at `v x`
bounded by `m! C Kᵐ`. Let `θ > 0` be the value of the weight at `x ∈ U`, with `θ ≤ M B` and
`K M ≤ 1/8`, and suppose `θⁱ |Dⁱv(x)| ≤ i! · 2M · ψ(i) · Bⁱ` for `1 ≤ i ≤ N`. Then for
`1 ≤ k ≤ N`, with `X i = θⁱ |Dⁱv(x)|` and `c` the structure constant,
`θ^{2k+2} ∑_l |Dᵏv_l| |Dᵏ(L v_l)| ≤ X k (c M (k+1) B X (k+1) + c M² (k+2)! ψ(k+2) B^{k+2})`,
where `L` is the operator with coefficients frozen at `x`. Only the order `k + 1` is not
controlled by the hypothesis, and it enters linearly with a small coefficient. -/
theorem weighted_cross_le {U : Set (ℝ^n)} {x : ℝ^n} {C K M B θ : ℝ} {N k : ℕ} (hU : IsOpen U)
    (hxU : x ∈ U) (hv : ContDiffOn ℝ ∞ v U) (ha : ∀ y ∈ U, ∀ i j, ContDiffAt ℝ ∞ (a i j) (v y))
    (hf : ∀ y ∈ U, ∀ l i, ContDiffAt ℝ ∞ (f l i) (v y))
    (heq : ∀ y ∈ U, ∀ l, ∑ i, (∂[i] (flux a f v l i)) y = 0)
    (hab : ∀ i j m, ‖iteratedFDeriv ℝ m (a i j) (v x)‖ ≤ m.factorial * C * K ^ m)
    (hfb : ∀ l i m, ‖iteratedFDeriv ℝ m (f l i) (v x)‖ ≤ m.factorial * C * K ^ m)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hM : 0 ≤ M) (hB : 0 ≤ B) (hθ : 0 < θ) (hθB : θ ≤ M * B)
    (hKM : K * M ≤ 1 / 8)
    (hX : ∀ i, 1 ≤ i → i ≤ N →
      θ ^ i * familyNorm i v x ≤ i.factorial * (2 * M) * convolutionWeight i * B ^ i)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    θ ^ (2 * k + 2) * ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x *
        iteratedCoordinateNorm k (frozenOperator (fun i j ↦ a i j (v x)) (fun z ↦ v z l)) x ≤
      (θ ^ k * familyNorm k v x) *
        (structureConstant n I C K * M * (k + 1) * B * (θ ^ (k + 1) * familyNorm (k + 1) v x) +
          structureConstant n I C K * M ^ 2 *
            ((k + 2).factorial * convolutionWeight (k + 2) * B ^ (k + 2))) := by
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = B / θ := ⟨_, rfl⟩
  have hβ : 0 ≤ β := by rw [hβdef]; exact div_nonneg hB hθ.le
  have hβθ : β * θ = B := by rw [hβdef]; exact div_mul_cancel₀ B hθ.ne'
  have hc : (0 : ℝ) ≤ 2 * M := by positivity
  have hcK : 2 * M * K ≤ 1 / 2 := by linarith
  have hle (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hvx : ContDiffAt ℝ ∞ v x := hv.contDiffAt (hU.mem_nhds hxU)
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℝ, ∀ i, F i = familyNorm i v x := ⟨_, fun _ ↦ rfl⟩
  have hF0 (i : ℕ) : 0 ≤ F i := by rw [hFdef]; exact familyNorm_nonneg i v x
  -- the hypothesis in terms of `β`
  have hF (i : ℕ) (h1 : 1 ≤ i) (hN : i ≤ N) :
      F i ≤ i.factorial * (2 * M) * convolutionWeight i * β ^ i := by
    have hpos : 0 < θ ^ i := pow_pos hθ i
    have h := hX i h1 hN
    rw [hFdef, hβdef, div_pow, ← mul_div_assoc, le_div_iff₀ hpos]
    linarith
  -- bounds on the derivatives of the compositions
  obtain ⟨α, hαdef⟩ : ∃ α : ℕ → ℝ, ∀ r, α r = C * K * F r +
      r.factorial * convolutionWeight r * β ^ r * (2 * C * (2 * M * K) ^ 2) := ⟨_, fun _ ↦ rfl⟩
  have hα0 (r : ℕ) : 0 ≤ α r := by
    rw [hαdef]
    have h1 := (convolutionWeight_pos r).le
    have h2 := hF0 r
    positivity
  have hcomp {g : (I → ℝ) → ℝ} (hg : ContDiffAt ℝ ∞ g (v x))
      (hgb : ∀ m, ‖iteratedFDeriv ℝ m g (v x)‖ ≤ m.factorial * C * K ^ m) (r : ℕ)
      (hr1 : 1 ≤ r) (hrN : r ≤ N + 1) :
      iteratedCoordinateNorm r (fun y ↦ g (v y)) x ≤ α r := by
    rw [hαdef, hFdef]
    exact iteratedCoordinateNorm_comp_le_of_convolutionWeight (hg.of_le (hle r))
      (hvx.of_le (hle r)) (fun m _ ↦ hgb m) hC hK hc hβ hcK
      (fun j h1 hN ↦ by have h := hF j h1 hN; rwa [hFdef] at h) hr1 hrN
  have hcross := sum_iteratedCoordinateNorm_mul_frozenOperator_le (k := k) (α := α)
    (φ := α (k + 1)) hU hxU hv ha hf heq hα0 (hα0 (k + 1))
    (fun i j r hr ↦ hcomp (ha x hxU i j) (hab i j) (r + 1) (by omega) (by omega))
    (fun l i ↦ hcomp (hf x hxU l i) (hfb l i) (k + 1) (by omega) (by omega))
  simp only [← hFdef] at hcross
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hnI : (0 : ℝ) ≤ n * Fintype.card I := by positivity
  have harith := structure_sum_le (F := F) (α := α) (φ := α (k + 1)) (A₂ := (n : ℝ) ^ 2)
    (A₁ := n * Fintype.card I) hF0 hC hK hc hβ hcK hn2 hnI hF (fun r _ _ ↦ (hαdef r).le)
    (hαdef (k + 1)).le hk1 hkN
  have hXk : 0 ≤ θ ^ k * F k := mul_nonneg (pow_nonneg hθ.le k) (hF0 k)
  -- the cross term in terms of `β`
  have hmain : ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x *
      iteratedCoordinateNorm k (frozenOperator (fun i j ↦ a i j (v x)) (fun z ↦ v z l)) x ≤
        F k * (((n : ℝ) ^ 2 * (2 * k + 3) * (C * K * (2 * M) * (convolutionWeight 1 * β)) +
          n * Fintype.card I * (C * K)) * F (k + 1) +
          ((n : ℝ) ^ 2 * (2 * C * K * (2 * M) ^ 2) *
              ((k + 2).factorial * convolutionWeight (k + 2) * β ^ (k + 2)) +
            n * Fintype.card I * (2 * C * (2 * M * K) ^ 2) *
              ((k + 1).factorial * convolutionWeight (k + 1) * β ^ (k + 1)))) :=
    hcross.trans (mul_le_mul_of_nonneg_left harith (hF0 k))
  rw [← hFdef k, ← hFdef (k + 1)]
  -- multiply by the weight: `θ^{2k+2} = θᵏ θ^{k+2}` and `β θ = B`
  have hsplit : θ ^ (2 * k + 2) = θ ^ k * (θ ^ (k + 1) * θ) := by ring
  have hβpow (m : ℕ) : β ^ m * θ ^ m = B ^ m := by rw [← mul_pow, hβθ]
  have hψk : convolutionWeight (k + 1) ≤ 4 * convolutionWeight (k + 2) :=
    convolutionWeight_le_four_mul_succ (k + 1)
  have hfack : ((k + 1).factorial : ℝ) ≤ (k + 2).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  have hFk1 := hF0 (k + 1)
  have hψk2 := (convolutionWeight_pos (k + 2)).le
  have hψk1 := (convolutionWeight_pos (k + 1)).le
  have hθk1 : 0 ≤ θ ^ (k + 1) := pow_nonneg hθ.le _
  have hBk2 : 0 ≤ B ^ (k + 2) := pow_nonneg hB _
  have hBk1 : 0 ≤ B ^ (k + 1) := pow_nonneg hB _
  have hfac2 : (0 : ℝ) ≤ (k + 2).factorial := Nat.cast_nonneg _
  -- coefficient of the top order
  have htop : ((n : ℝ) ^ 2 * (2 * k + 3) * (C * K * (2 * M) * (convolutionWeight 1 * β)) +
      n * Fintype.card I * (C * K)) * θ ≤ structureConstant n I C K * M * (k + 1) * B :=
    top_coefficient_le hn2 hnI (mul_nonneg hC hK) hM hB (Nat.cast_nonneg k)
      (convolutionWeight_le_one 1) hβθ hθB
  -- the quadratic remainder
  have hrem : ((n : ℝ) ^ 2 * (2 * C * K * (2 * M) ^ 2) *
        ((k + 2).factorial * convolutionWeight (k + 2) * β ^ (k + 2)) +
      n * Fintype.card I * (2 * C * (2 * M * K) ^ 2) *
        ((k + 1).factorial * convolutionWeight (k + 1) * β ^ (k + 1))) * (θ ^ (k + 1) * θ) ≤
      structureConstant n I C K * M ^ 2 *
        ((k + 2).factorial * convolutionWeight (k + 2) * B ^ (k + 2)) := by
    have e1 : β ^ (k + 2) * (θ ^ (k + 1) * θ) = B ^ (k + 2) := by
      rw [← hβpow (k + 2)]; ring
    have e2 : β ^ (k + 1) * (θ ^ (k + 1) * θ) = B ^ (k + 1) * θ := by
      rw [← hβpow (k + 1)]; ring
    have h1 : B ^ (k + 1) * θ ≤ M * B ^ (k + 2) := by
      calc B ^ (k + 1) * θ ≤ B ^ (k + 1) * (M * B) := mul_le_mul_of_nonneg_left hθB hBk1
        _ = M * B ^ (k + 2) := by ring
    have h2 : ((k + 1).factorial : ℝ) * convolutionWeight (k + 1) ≤
        4 * ((k + 2).factorial * convolutionWeight (k + 2)) := by
      calc ((k + 1).factorial : ℝ) * convolutionWeight (k + 1)
          ≤ (k + 2).factorial * (4 * convolutionWeight (k + 2)) :=
            mul_le_mul hfack hψk hψk1 hfac2
        _ = _ := by ring
    exact remainder_le hn2 hnI hC hK (mul_nonneg hfac2 hψk2) h2 hBk2
      (mul_nonneg hBk1 hθ.le) h1 e1 e2 hKM
  calc θ ^ (2 * k + 2) * ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x *
        iteratedCoordinateNorm k (frozenOperator (fun i j ↦ a i j (v x)) (fun z ↦ v z l)) x
      ≤ θ ^ (2 * k + 2) * (F k * (((n : ℝ) ^ 2 * (2 * k + 3) *
          (C * K * (2 * M) * (convolutionWeight 1 * β)) +
          n * Fintype.card I * (C * K)) * F (k + 1) +
          ((n : ℝ) ^ 2 * (2 * C * K * (2 * M) ^ 2) *
              ((k + 2).factorial * convolutionWeight (k + 2) * β ^ (k + 2)) +
            n * Fintype.card I * (2 * C * (2 * M * K) ^ 2) *
              ((k + 1).factorial * convolutionWeight (k + 1) * β ^ (k + 1))))) :=
        mul_le_mul_of_nonneg_left hmain (pow_nonneg hθ.le _)
    _ = (θ ^ k * F k) * ((((n : ℝ) ^ 2 * (2 * k + 3) *
          (C * K * (2 * M) * (convolutionWeight 1 * β)) +
          n * Fintype.card I * (C * K)) * θ) * (θ ^ (k + 1) * F (k + 1)) +
          ((n : ℝ) ^ 2 * (2 * C * K * (2 * M) ^ 2) *
              ((k + 2).factorial * convolutionWeight (k + 2) * β ^ (k + 2)) +
            n * Fintype.card I * (2 * C * (2 * M * K) ^ 2) *
              ((k + 1).factorial * convolutionWeight (k + 1) * β ^ (k + 1))) *
            (θ ^ (k + 1) * θ)) := by rw [hsplit]; ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ hrem) hXk
        exact mul_le_mul_of_nonneg_right htop (mul_nonneg hθk1 hFk1)

end PDE.Elliptic.Regularity.Analytic
