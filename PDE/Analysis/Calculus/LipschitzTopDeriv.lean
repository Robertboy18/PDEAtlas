/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Functions with a locally Lipschitz top derivative

`LipschitzTopDeriv k f` says that a real function `f` has `k` continuous derivatives and that its
`k`-th derivative is locally Lipschitz: the local class `C^{k,1}`. The class contains every
`C^{k+1}` function and is closed under sums, differences, scalar multiples, products, finite sums
and the reflection `x ↦ -x`. Every derivative of order at most `k` is then locally Lipschitz, and
the derivative of a `C^{k+1,1}` function is `C^{k,1}`.

## Main definitions

* `LipschitzTopDeriv`: the local class `C^{k,1}` of real functions.

## Main results

* `LipschitzTopDeriv.of_contDiff`: a `C^{k+1}` function is `C^{k,1}`.
* `LipschitzTopDeriv.locallyLipschitz_iteratedDeriv`: every derivative of order at most `k` of a
  `C^{k,1}` function is locally Lipschitz.
* `LipschitzTopDeriv.deriv`: the derivative of a `C^{k+1,1}` function is `C^{k,1}`.
* `LipschitzTopDeriv.mul`: products of `C^{k,1}` functions are `C^{k,1}`.
* `LipschitzTopDeriv.sum`: finite sums of `C^{k,1}` functions are `C^{k,1}`.
* `LipschitzTopDeriv.comp_neg`: the reflection `x ↦ -x` preserves the class `C^{k,1}`.
-/

@[expose] public section

namespace PDE.Analysis

open scoped ContDiff

/-- The local class `C^{k,1}`: `k` continuous derivatives and a locally Lipschitz `k`-th
derivative. -/
structure LipschitzTopDeriv (k : ℕ) (f : ℝ → ℝ) : Prop where
  /-- The function has `k` continuous derivatives. -/
  contDiff : ContDiff ℝ k f
  /-- The `k`-th derivative is locally Lipschitz. -/
  locallyLipschitz : LocallyLipschitz (iteratedDeriv k f)

/-- A product of locally Lipschitz real functions is locally Lipschitz. -/
theorem locallyLipschitz_mul {α : Type*} [PseudoEMetricSpace α] {f g : α → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x ↦ f x * g x := by
  have hm : LocallyLipschitz fun p : ℝ × ℝ ↦ p.1 * p.2 :=
    ContDiff.locallyLipschitz (𝕂 := ℝ) (contDiff_fst.mul contDiff_snd)
  exact hm.comp (hf.prodMk hg)

/-- A finite sum of locally Lipschitz real functions is locally Lipschitz. -/
theorem locallyLipschitz_sum {α ι : Type*} [PseudoEMetricSpace α] (s : Finset ι)
    {f : ι → α → ℝ} (hf : ∀ i ∈ s, LocallyLipschitz (f i)) :
    LocallyLipschitz fun x ↦ ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocallyLipschitz.const (α := α) (0 : ℝ)
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- Lower iterated derivatives of a `C^k` function keep the remaining smoothness. -/
theorem contDiff_iteratedDeriv_of_add_le {k a b : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (h : b + a ≤ k) : ContDiff ℝ b (iteratedDeriv a f) := by
  rw [iteratedDeriv_eq_iterate]
  exact (hf.of_le (by exact_mod_cast h)).iterate_deriv' b a

namespace LipschitzTopDeriv

variable {k : ℕ} {f g : ℝ → ℝ}

/-- Every iterated derivative of order at most `k` of a `C^{k,1}` function is locally
Lipschitz. -/
theorem locallyLipschitz_iteratedDeriv (hf : LipschitzTopDeriv k f) {a : ℕ} (ha : a ≤ k) :
    LocallyLipschitz (iteratedDeriv a f) := by
  rcases ha.eq_or_lt with rfl | hlt
  · exact hf.locallyLipschitz
  · exact (contDiff_iteratedDeriv_of_add_le (b := 1) hf.contDiff (by omega)).locallyLipschitz

/-- A `C^{k+1}` function is `C^{k,1}`. -/
theorem of_contDiff (hf : ContDiff ℝ (k + 1) f) : LipschitzTopDeriv k f := by
  have hf' : ContDiff ℝ ((k + 1 : ℕ) : ℕ∞ω) f := by exact_mod_cast hf
  exact ⟨hf'.of_le (by exact_mod_cast Nat.le_succ k),
    (contDiff_iteratedDeriv_of_add_le (b := 1) (a := k) hf' (by omega)).locallyLipschitz⟩

/-- A `C^{k+1,1}` function is `C^{k,1}`. -/
theorem of_succ (hf : LipschitzTopDeriv (k + 1) f) : LipschitzTopDeriv k f :=
  of_contDiff hf.contDiff

/-- The derivative of a `C^{k+1,1}` function is `C^{k,1}`. -/
theorem deriv (hf : LipschitzTopDeriv (k + 1) f) : LipschitzTopDeriv k (_root_.deriv f) where
  contDiff := by
    have h := hf.contDiff
    rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by push_cast; rfl] at h
    exact h.deriv'
  locallyLipschitz := by
    rw [← iteratedDeriv_succ']
    exact hf.locallyLipschitz

/-- Constant functions are `C^{k,1}`. -/
theorem const (c : ℝ) : LipschitzTopDeriv k fun _ ↦ c :=
  of_contDiff contDiff_const

/-- Sums of `C^{k,1}` functions are `C^{k,1}`. -/
theorem add (hf : LipschitzTopDeriv k f) (hg : LipschitzTopDeriv k g) :
    LipschitzTopDeriv k fun x ↦ f x + g x where
  contDiff := hf.contDiff.add hg.contDiff
  locallyLipschitz := by
    have heq : iteratedDeriv k (fun x ↦ f x + g x) =
        fun x ↦ iteratedDeriv k f x + iteratedDeriv k g x := by
      funext x
      exact iteratedDeriv_fun_add hf.contDiff.contDiffAt hg.contDiff.contDiffAt
    rw [heq]
    exact hf.locallyLipschitz.add hg.locallyLipschitz

/-- Negatives of `C^{k,1}` functions are `C^{k,1}`. -/
theorem neg (hf : LipschitzTopDeriv k f) : LipschitzTopDeriv k fun x ↦ -f x where
  contDiff := hf.contDiff.neg
  locallyLipschitz := by
    have heq : iteratedDeriv k (fun x ↦ -f x) = fun x ↦ -iteratedDeriv k f x := by
      funext x
      exact iteratedDeriv_fun_neg k f x
    rw [heq]
    exact hf.locallyLipschitz.neg

/-- Differences of `C^{k,1}` functions are `C^{k,1}`. -/
theorem sub (hf : LipschitzTopDeriv k f) (hg : LipschitzTopDeriv k g) :
    LipschitzTopDeriv k fun x ↦ f x - g x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Constant multiples of `C^{k,1}` functions are `C^{k,1}`. -/
theorem const_mul (hf : LipschitzTopDeriv k f) (c : ℝ) :
    LipschitzTopDeriv k fun x ↦ c * f x where
  contDiff := contDiff_const.mul hf.contDiff
  locallyLipschitz := by
    have heq : iteratedDeriv k (fun x ↦ c * f x) = fun x ↦ c * iteratedDeriv k f x := by
      funext x
      exact iteratedDeriv_const_mul_field c f
    rw [heq]
    exact locallyLipschitz_mul (LocallyLipschitz.const c) hf.locallyLipschitz

/-- Reflection `x ↦ -x` preserves the class `C^{k,1}`. -/
theorem comp_neg (hf : LipschitzTopDeriv k f) : LipschitzTopDeriv k fun x ↦ f (-x) where
  contDiff := hf.contDiff.comp contDiff_neg
  locallyLipschitz := by
    have heq : iteratedDeriv k (fun x ↦ f (-x)) =
        fun x ↦ (-1 : ℝ) ^ k * iteratedDeriv k f (-x) := by
      funext x
      rw [iteratedDeriv_comp_neg, smul_eq_mul]
    rw [heq]
    exact locallyLipschitz_mul (LocallyLipschitz.const _)
      (hf.locallyLipschitz.comp LipschitzWith.id.neg.locallyLipschitz)

/-- Translation `x ↦ x + a` preserves the class `C^{k,1}`. -/
theorem comp_add_const (hf : LipschitzTopDeriv k f) (a : ℝ) :
    LipschitzTopDeriv k fun x ↦ f (x + a) where
  contDiff := hf.contDiff.comp (contDiff_id.add contDiff_const)
  locallyLipschitz := by
    rw [iteratedDeriv_comp_add_const]
    exact hf.locallyLipschitz.comp
      (ContDiff.locallyLipschitz (𝕂 := ℝ) (contDiff_id.add contDiff_const))

/-- The reflection `x ↦ a - x` preserves the class `C^{k,1}`. -/
theorem comp_const_sub (hf : LipschitzTopDeriv k f) (a : ℝ) :
    LipschitzTopDeriv k fun x ↦ f (a - x) := by
  simpa only [sub_eq_neg_add, add_comm] using (hf.comp_add_const a).comp_neg

/-- Products of `C^{k,1}` functions are `C^{k,1}`, by the Leibniz rule. -/
theorem mul (hf : LipschitzTopDeriv k f) (hg : LipschitzTopDeriv k g) :
    LipschitzTopDeriv k fun x ↦ f x * g x where
  contDiff := hf.contDiff.mul hg.contDiff
  locallyLipschitz := by
    have heq : iteratedDeriv k (fun x ↦ f x * g x) = fun x ↦
        ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (k - i) g x := by
      funext x
      exact iteratedDeriv_fun_mul hf.contDiff.contDiffAt hg.contDiff.contDiffAt
    rw [heq]
    refine locallyLipschitz_sum _ (fun i hi ↦ ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact locallyLipschitz_mul (locallyLipschitz_mul (LocallyLipschitz.const _)
      (hf.locallyLipschitz_iteratedDeriv hik))
        (hg.locallyLipschitz_iteratedDeriv (Nat.sub_le k i))

/-- Finite sums of `C^{k,1}` functions are `C^{k,1}`. -/
theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, LipschitzTopDeriv k (f i)) :
    LipschitzTopDeriv k fun x ↦ ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (k := k) 0
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

end LipschitzTopDeriv

end PDE.Analysis
