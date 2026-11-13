/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Bounds for all iterated derivatives of a smooth function

`IteratedDerivBoundOn f s B` says that `|f⁽ᵏ⁾ x| ≤ B k` for every order `k` and every `x ∈ s`.
For smooth functions on `ℝ` the bounds combine along sums, constant multiples and products, the
last by the Leibniz rule. Bounds of exponential type, `B k = ∑ₜ aₜ ρₜ ^ k`, are closed under
products: the Leibniz convolution of two such bounds is again of this form, with the products
of the amplitudes and the sums of the rates (`sum_choose_mul_expSum_mul_expSum`). Constants,
`cos (c x)`, `sin (c x)` and the powers `x ^ p` on a bounded set have bounds of this type.

These bounds feed the remainder terms of interpolatory quadrature rules, which need a bound for
one derivative of high order on the integration interval.

## Main results

* `IteratedDerivBoundOn.add`, `IteratedDerivBoundOn.const_mul`, `IteratedDerivBoundOn.mul`.
* `expSum`, `sum_choose_mul_expSum_mul_expSum`, `IteratedDerivBoundOn.mul_expSum`.
* `iteratedDerivBoundOn_const`, `iteratedDerivBoundOn_cos_mul`, `iteratedDerivBoundOn_sin_mul`,
  `iteratedDerivBoundOn_pow`.
-/

@[expose] public section

namespace PDE.Analysis

open Finset
open scoped ContDiff

/-- Every iterated derivative of `f` is bounded on `s`: `|f⁽ᵏ⁾ x| ≤ B k` for `x ∈ s`. -/
def IteratedDerivBoundOn (f : ℝ → ℝ) (s : Set ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ k, ∀ x ∈ s, |iteratedDeriv k f x| ≤ B k

namespace IteratedDerivBoundOn

variable {f g : ℝ → ℝ} {s t : Set ℝ} {B C : ℕ → ℝ}

/-- A bound on a set holds on every subset. -/
theorem mono_set (h : IteratedDerivBoundOn f s B) (hts : t ⊆ s) : IteratedDerivBoundOn f t B :=
  fun k x hx ↦ h k x (hts hx)

/-- A bound can be replaced by a larger one. -/
theorem mono (h : IteratedDerivBoundOn f s B) (hBC : ∀ k, B k ≤ C k) :
    IteratedDerivBoundOn f s C :=
  fun k x hx ↦ (h k x hx).trans (hBC k)

/-- Equal functions have the same bounds. -/
theorem congr (h : IteratedDerivBoundOn f s B) (hfg : f = g) : IteratedDerivBoundOn g s B :=
  hfg ▸ h

/-- Bounds add along sums of smooth functions. -/
theorem add (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfB : IteratedDerivBoundOn f s B)
    (hgC : IteratedDerivBoundOn g s C) :
    IteratedDerivBoundOn (fun x ↦ f x + g x) s (fun k ↦ B k + C k) := by
  intro k x hx
  rw [iteratedDeriv_fun_add (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (abs_add_le _ _).trans (add_le_add (hfB k x hx) (hgC k x hx))

/-- A constant factor multiplies the bounds by its absolute value. -/
theorem const_mul (hfB : IteratedDerivBoundOn f s B) (c : ℝ) :
    IteratedDerivBoundOn (fun x ↦ c * f x) s (fun k ↦ |c| * B k) := by
  intro k x hx
  rw [iteratedDeriv_const_mul_field, abs_mul]
  exact mul_le_mul_of_nonneg_left (hfB k x hx) (abs_nonneg c)

/-- The Leibniz rule for bounds: the bounds of a product are the binomial convolution of the
bounds of the factors. -/
theorem mul (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfB : IteratedDerivBoundOn f s B)
    (hgC : IteratedDerivBoundOn g s C) :
    IteratedDerivBoundOn (fun x ↦ f x * g x) s
      (fun n ↦ ∑ i ∈ range (n + 1), (n.choose i : ℝ) * B i * C (n - i)) := by
  intro n x hx
  rw [iteratedDeriv_fun_mul (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul, abs_mul, Nat.abs_cast, mul_assoc, mul_assoc]
  have hB : 0 ≤ B i := (abs_nonneg _).trans (hfB i x hx)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (hfB i x hx) (hgC (n - i) x hx) (abs_nonneg _) hB) (Nat.cast_nonneg _)

end IteratedDerivBoundOn

/-! ### Bounds of exponential type -/

/-- The bound `∑ₜ aₜ ρₜ ^ k` of exponential type with amplitudes `a` and rates `ρ`. -/
def expSum {ι : Type*} [Fintype ι] (a ρ : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ t, a t * ρ t ^ k

/-- The Leibniz convolution of two bounds of exponential type is of exponential type, with the
products of the amplitudes and the sums of the rates. -/
theorem sum_choose_mul_expSum_mul_expSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a ρ : ι → ℝ) (b σ : κ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) * expSum a ρ i * expSum b σ (n - i) =
      expSum (fun p : ι × κ ↦ a p.1 * b p.2) (fun p ↦ ρ p.1 + σ p.2) n := by
  calc ∑ i ∈ range (n + 1), (n.choose i : ℝ) * expSum a ρ i * expSum b σ (n - i)
      = ∑ i ∈ range (n + 1), ∑ t, ∑ u,
          (n.choose i : ℝ) * (a t * ρ t ^ i) * (b u * σ u ^ (n - i)) := by
        simp only [expSum, mul_sum, sum_mul]
        exact sum_congr rfl fun i _ ↦ sum_comm
    _ = ∑ t, ∑ u, ∑ i ∈ range (n + 1),
          (n.choose i : ℝ) * (a t * ρ t ^ i) * (b u * σ u ^ (n - i)) := by
        rw [sum_comm]
        exact sum_congr rfl fun t _ ↦ sum_comm
    _ = _ := by
        simp only [expSum, Fintype.sum_prod_type, add_pow, mul_sum]
        refine sum_congr rfl fun t _ ↦ sum_congr rfl fun u _ ↦ sum_congr rfl fun i _ ↦ ?_
        ring

/-- The product of two smooth functions with bounds of exponential type has a bound of
exponential type. -/
theorem IteratedDerivBoundOn.mul_expSum {ι κ : Type*} [Fintype ι] [Fintype κ] {f g : ℝ → ℝ}
    {s : Set ℝ} {a ρ : ι → ℝ} {b σ : κ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfB : IteratedDerivBoundOn f s (expSum a ρ)) (hgC : IteratedDerivBoundOn g s (expSum b σ)) :
    IteratedDerivBoundOn (fun x ↦ f x * g x) s
      (expSum (fun p : ι × κ ↦ a p.1 * b p.2) (fun p ↦ ρ p.1 + σ p.2)) := by
  refine (hfB.mul hf hg hgC).mono fun n ↦ ?_
  rw [sum_choose_mul_expSum_mul_expSum]

/-- A bound of exponential type increases with nonnegative amplitudes and rates. -/
theorem expSum_le_expSum {ι : Type*} [Fintype ι] {a a' ρ ρ' : ι → ℝ}
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ a' t) (hρ : ∀ t, 0 ≤ ρ t ∧ ρ t ≤ ρ' t) (k : ℕ) :
    expSum a ρ k ≤ expSum a' ρ' k := by
  refine sum_le_sum fun t _ ↦ ?_
  exact mul_le_mul (ha t).2 (pow_le_pow_left₀ (hρ t).1 (hρ t).2 k) (pow_nonneg (hρ t).1 k)
    ((ha t).1.trans (ha t).2)

/-! ### Bounds of a single exponential term -/

/-- The product of two smooth functions with bounds `a ρ ^ k` and `b σ ^ k` has the bound
`a b (ρ + σ) ^ k`. -/
theorem IteratedDerivBoundOn.mul_pow {f g : ℝ → ℝ} {s : Set ℝ} {a b ρ σ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfB : IteratedDerivBoundOn f s fun k ↦ a * ρ ^ k)
    (hgC : IteratedDerivBoundOn g s fun k ↦ b * σ ^ k) :
    IteratedDerivBoundOn (fun x ↦ f x * g x) s fun k ↦ a * b * (ρ + σ) ^ k := by
  refine (hfB.mul hf hg hgC).mono fun n ↦ le_of_eq ?_
  rw [add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- A bound `a ρ ^ k` with `ρ ≤ σ` gives the bound `a σ ^ k`. At any point of `s` the cases
`k = 0, 1` force `0 ≤ a`, and `0 ≤ ρ` unless `a = 0`. -/
theorem IteratedDerivBoundOn.mono_rate {f : ℝ → ℝ} {s : Set ℝ} {a ρ σ : ℝ}
    (h : IteratedDerivBoundOn f s fun k ↦ a * ρ ^ k) (hρσ : ρ ≤ σ) :
    IteratedDerivBoundOn f s fun k ↦ a * σ ^ k := by
  intro k x hx
  have ha : 0 ≤ a := by simpa using (abs_nonneg _).trans (h 0 x hx)
  rcases ha.eq_or_lt with rfl | ha
  · simpa using h k x hx
  have hρ : 0 ≤ ρ :=
    nonneg_of_mul_nonneg_right (by simpa using (abs_nonneg _).trans (h 1 x hx)) ha
  exact (h k x hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ hρσ k) ha.le)

/-- A bound `a ρ ^ k` with `a ≤ b` gives the bound `b ρ ^ k` for `ρ ≥ 0`. -/
theorem IteratedDerivBoundOn.mono_amplitude {f : ℝ → ℝ} {s : Set ℝ} {a b ρ : ℝ}
    (h : IteratedDerivBoundOn f s fun k ↦ a * ρ ^ k) (hab : a ≤ b) (hρ : 0 ≤ ρ) :
    IteratedDerivBoundOn f s fun k ↦ b * ρ ^ k :=
  h.mono fun k ↦ mul_le_mul_of_nonneg_right hab (pow_nonneg hρ k)

/-- Bounds with a common rate add along finite sums. -/
theorem IteratedDerivBoundOn.sum {ι : Type*} {t : Finset ι} {f : ι → ℝ → ℝ} {s : Set ℝ}
    {a : ι → ℝ} {ρ : ℝ} (hf : ∀ i ∈ t, ContDiff ℝ ∞ (f i))
    (h : ∀ i ∈ t, IteratedDerivBoundOn (f i) s fun k ↦ a i * ρ ^ k) :
    IteratedDerivBoundOn (fun x ↦ ∑ i ∈ t, f i x) s fun k ↦ (∑ i ∈ t, a i) * ρ ^ k := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro k x _
    simp
  | @insert i t hi ih =>
    have hf' : ∀ j ∈ t, ContDiff ℝ ∞ (f j) := fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    have h' := (h i (Finset.mem_insert_self i t)).add (hf i (Finset.mem_insert_self i t))
      (ContDiff.sum fun j hj ↦ hf' j hj) (ih hf' fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    exact h'.mono fun k ↦ le_of_eq (by ring)

/-! ### Elementary functions -/

/-- A constant has the bound `|c| 0 ^ k`: `|c|` at order zero and `0` beyond. -/
theorem iteratedDerivBoundOn_const (c : ℝ) (s : Set ℝ) :
    IteratedDerivBoundOn (fun _ ↦ c) s (fun k ↦ |c| * 0 ^ k) := by
  intro k x _
  rw [iteratedDeriv_const]
  rcases k with _ | k <;> simp

/-- `|d^k/dx^k cos (c x)| ≤ |c| ^ k`. -/
theorem iteratedDerivBoundOn_cos_mul (c : ℝ) (s : Set ℝ) :
    IteratedDerivBoundOn (fun x ↦ Real.cos (c * x)) s (fun k ↦ |c| ^ k) := by
  intro k x _
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos, abs_mul,
    abs_pow]
  refine mul_le_of_le_one_right (by positivity) ?_
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [← two_mul, Real.iteratedDeriv_even_cos]
    simpa [abs_mul] using Real.abs_cos_le_one (c * x)
  · rw [Real.iteratedDeriv_odd_cos]
    simpa [abs_mul] using Real.abs_sin_le_one (c * x)

/-- `|d^k/dx^k sin (c x)| ≤ |c| ^ k`. -/
theorem iteratedDerivBoundOn_sin_mul (c : ℝ) (s : Set ℝ) :
    IteratedDerivBoundOn (fun x ↦ Real.sin (c * x)) s (fun k ↦ |c| ^ k) := by
  intro k x _
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sin, abs_mul,
    abs_pow]
  refine mul_le_of_le_one_right (by positivity) ?_
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [← two_mul, Real.iteratedDeriv_even_sin]
    simpa [abs_mul] using Real.abs_sin_le_one (c * x)
  · rw [Real.iteratedDeriv_odd_sin]
    simpa [abs_mul] using Real.abs_cos_le_one (c * x)

/-- On a set where `|x| ≤ R`, `R > 0`, the power `x ^ p` has the bound `R ^ p (p / R) ^ k`. -/
theorem iteratedDerivBoundOn_pow {s : Set ℝ} {R : ℝ} (hR : 0 < R) (hs : ∀ x ∈ s, |x| ≤ R)
    (p : ℕ) : IteratedDerivBoundOn (fun x ↦ x ^ p) s (fun k ↦ R ^ p * (p / R) ^ k) := by
  intro k x hx
  rw [iteratedDeriv_pow, abs_mul, Nat.abs_cast, abs_pow]
  rcases le_or_gt k p with hkp | hkp
  · have hd : ((p.descFactorial k : ℕ) : ℝ) ≤ (p : ℝ) ^ k := by
      exact_mod_cast Nat.descFactorial_le_pow p k
    have hx' : |x| ^ (p - k) ≤ R ^ (p - k) := pow_le_pow_left₀ (abs_nonneg x) (hs x hx) _
    have hsplit : R ^ p * ((p : ℝ) / R) ^ k = (p : ℝ) ^ k * R ^ (p - k) := by
      rw [div_pow, ← pow_sub_mul_pow R hkp]
      field_simp
    change _ ≤ R ^ p * ((p : ℝ) / R) ^ k
    rw [hsplit]
    exact mul_le_mul hd hx' (by positivity) (by positivity)
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hkp]
    simp only [Nat.cast_zero, zero_mul]
    positivity

end PDE.Analysis
