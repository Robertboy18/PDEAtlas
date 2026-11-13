/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Ratios of sums of powers at infinity

For finitely many terms `A_k s ^ {d_k}` with a unique largest exponent `d_{k₀}` and `A_{k₀} > 0`,
the ratio of another sum of powers to `∑ A_k s ^ {d_k}` is governed by the term of exponent
`d_{k₀}` as `s → ∞`.

## Main results

* `tendsto_sum_mul_rpow_div_sum_mul_rpow`:
  `(∑ B_k s ^ {d_k}) / (∑ A_k s ^ {d_k}) → B_{k₀} / A_{k₀}` as `s → ∞`.
* `tendsto_sum_mul_rpow_div_sum_mul_rpow_zero`: `(∑ B_k s ^ {d'_k}) / (∑ A_k s ^ {d_k}) → 0`
  when every `d'_k` is below `d_{k₀}`.
-/

@[expose] public section

namespace PDE.Analysis

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- `s ^ (d - d₀) → 0` for `d < d₀`, and `= 1` for `d = d₀`. -/
private theorem tendsto_rpow_sub (d d₀ : ℝ) (hd : d < d₀) :
    Tendsto (fun s : ℝ ↦ s ^ (d - d₀)) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (y := d₀ - d) (by linarith)
  simpa only [neg_sub] using h

/-- The normalized sums: `∑ B_k s ^ (d_k - D)` tends to `∑ B_k [d_k = D]` when every `d_k ≤ D`
and the equal exponents are exactly `k₀`. -/
private theorem tendsto_sum_mul_rpow_sub {B d' : ι → ℝ} {D : ℝ} {k₀ : ι}
    (hd : ∀ k, k ≠ k₀ → d' k < D) (hk₀ : d' k₀ = D) :
    Tendsto (fun s : ℝ ↦ ∑ k, B k * s ^ (d' k - D)) atTop (𝓝 (B k₀)) := by
  classical
  have h : Tendsto (fun s : ℝ ↦ ∑ k, B k * s ^ (d' k - D)) atTop
      (𝓝 (∑ k, B k * if k = k₀ then 1 else 0)) := by
    refine tendsto_finsetSum _ fun k _ ↦ (tendsto_const_nhds (x := B k)).mul ?_
    by_cases hk : k = k₀
    · subst hk
      simp only [hk₀, sub_self, Real.rpow_zero, ite_true]
      exact tendsto_const_nhds
    · simp only [hk, ite_false]
      exact tendsto_rpow_sub _ _ (hd k hk)
  simpa [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] using h

/-- For `s > 0` a sum of powers factors as
`∑ C_k s ^ {e_k} = (∑ C_k s ^ {e_k - D}) s ^ D`. -/
private theorem sum_mul_rpow_eq {τ : Type*} [Fintype τ] (C e : τ → ℝ) (D : ℝ) {s : ℝ}
    (hs : 0 < s) : ∑ k, C k * s ^ e k = (∑ k, C k * s ^ (e k - D)) * s ^ D := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_assoc, ← Real.rpow_add hs, sub_add_cancel]

/-- **The ratio of two sums of powers** tends to the ratio of the coefficients of the unique largest
exponent: if `A_{k₀} > 0` and `d_k < d_{k₀}` for `k ≠ k₀`, then
`(∑ B_k s ^ {d_k}) / (∑ A_k s ^ {d_k}) → B_{k₀} / A_{k₀}` as `s → ∞`. -/
theorem tendsto_sum_mul_rpow_div_sum_mul_rpow {A B d : ι → ℝ} {k₀ : ι} (hk₀ : 0 < A k₀)
    (hd : ∀ k, k ≠ k₀ → d k < d k₀) :
    Tendsto (fun s : ℝ ↦ (∑ k, B k * s ^ d k) / ∑ k, A k * s ^ d k) atTop
      (𝓝 (B k₀ / A k₀)) := by
  have hB := tendsto_sum_mul_rpow_sub (B := B) (d' := d) hd rfl
  have hA := tendsto_sum_mul_rpow_sub (B := A) (d' := d) hd rfl
  refine (hB.div hA hk₀.ne').congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hpos : 0 < s ^ d k₀ := Real.rpow_pos_of_pos hs _
  rw [Pi.div_apply, sum_mul_rpow_eq B d (d k₀) hs, sum_mul_rpow_eq A d (d k₀) hs,
    mul_div_mul_right _ _ hpos.ne']

/-- **A sum of lower powers is negligible**: if `A_{k₀} > 0`, `d_k < d_{k₀}` for `k ≠ k₀` and
every `d'_k < d_{k₀}`, then `(∑ B_k s ^ {d'_k}) / (∑ A_k s ^ {d_k}) → 0`. -/
theorem tendsto_sum_mul_rpow_div_sum_mul_rpow_zero {κ : Type*} [Fintype κ] {A d : ι → ℝ}
    {B d' : κ → ℝ} {k₀ : ι} (hk₀ : 0 < A k₀) (hd : ∀ k, k ≠ k₀ → d k < d k₀)
    (hd' : ∀ k, d' k < d k₀) :
    Tendsto (fun s : ℝ ↦ (∑ k, B k * s ^ d' k) / ∑ k, A k * s ^ d k) atTop (𝓝 0) := by
  have hB : Tendsto (fun s : ℝ ↦ ∑ k, B k * s ^ (d' k - d k₀)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset κ) fun k _ ↦
      (tendsto_const_nhds (x := B k)).mul (tendsto_rpow_sub (d' k) (d k₀) (hd' k))
    simpa using this
  have hA' := tendsto_sum_mul_rpow_sub (B := A) (d' := d) hd rfl
  have h := hB.div hA' hk₀.ne'
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hpos : 0 < s ^ d k₀ := Real.rpow_pos_of_pos hs _
  rw [Pi.div_apply, sum_mul_rpow_eq B d' (d k₀) hs, sum_mul_rpow_eq A d (d k₀) hs,
    mul_div_mul_right _ _ hpos.ne']

end PDE.Analysis
