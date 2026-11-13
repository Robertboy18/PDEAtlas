/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Coefficient majorants on lower sets

Absolute coefficient bounds are preserved by sums, products and admissible
substitution. Working on a lower set of exponents permits induction in one
variable while keeping all degrees in the remaining variables.
-/

@[expose] public section

open scoped BigOperators

namespace MvPowerSeries

variable {σ τ ι : Type*}

/-- The coefficients of `f` in `s` are bounded in absolute value by those of `g`. -/
def IsMajorizedOn (f g : MvPowerSeries σ ℝ) (s : Set (σ →₀ ℕ)) : Prop :=
  ∀ a ∈ s, ‖coeff a f‖ ≤ coeff a g

namespace IsMajorizedOn

variable {s t : Set (σ →₀ ℕ)} {f f₁ f₂ g g₁ g₂ : MvPowerSeries σ ℝ}

/-- A majorant has nonnegative coefficients on the exponents being compared. -/
theorem nonneg (h : IsMajorizedOn f g s) {a : σ →₀ ℕ} (ha : a ∈ s) :
    0 ≤ coeff a g :=
  (norm_nonneg _).trans (h a ha)

/-- Coefficient majorization restricts to smaller sets. -/
theorem mono (h : IsMajorizedOn f g s) (ht : t ⊆ s) : IsMajorizedOn f g t :=
  fun a ha ↦ h a (ht ha)

/-- The zero series majorizes itself. -/
theorem zero (s : Set (σ →₀ ℕ)) : IsMajorizedOn 0 0 s := by
  intro a ha
  simp

/-- The constant series one majorizes itself. -/
theorem one (s : Set (σ →₀ ℕ)) : IsMajorizedOn 1 1 s := by
  classical
  intro a ha
  simp only [coeff_one]
  split_ifs <;> simp

/-- Adding majorized series adds their coefficient majorants. -/
protected theorem add (hf : IsMajorizedOn f₁ g₁ s) (hg : IsMajorizedOn f₂ g₂ s) :
    IsMajorizedOn (f₁ + f₂) (g₁ + g₂) s := by
  intro a ha
  simp only [map_add]
  exact (norm_add_le _ _).trans (add_le_add (hf a ha) (hg a ha))

/-- Products preserve majorization on lower sets of exponents. -/
protected theorem mul (hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s)
    (hf : IsMajorizedOn f₁ g₁ s) (hg : IsMajorizedOn f₂ g₂ s) :
    IsMajorizedOn (f₁ * f₂) (g₁ * g₂) s := by
  classical
  intro a ha
  rw [coeff_mul, coeff_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hp' : p.1 + p.2 = a := Finset.mem_antidiagonal.mp hp
  have h₁ : p.1 ∈ s := hs ha (hp' ▸ le_self_add)
  have h₂ : p.2 ∈ s := hs ha (hp' ▸ le_add_self)
  rw [norm_mul]
  exact mul_le_mul (hf p.1 h₁) (hg p.2 h₂) (norm_nonneg _) (hf.nonneg h₁)

/-- Natural powers preserve majorization on lower sets. -/
protected theorem pow (hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s)
    (h : IsMajorizedOn f g s) (n : ℕ) : IsMajorizedOn (f ^ n) (g ^ n) s := by
  induction n with
  | zero => simpa only [pow_zero] using one s
  | succ n ih => simpa only [pow_succ] using ih.mul hs h

/-- Finite sums preserve coefficient majorization. -/
protected theorem sum (u : Finset ι) {f g : ι → MvPowerSeries σ ℝ}
    (h : ∀ i ∈ u, IsMajorizedOn (f i) (g i) s) :
    IsMajorizedOn (∑ i ∈ u, f i) (∑ i ∈ u, g i) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using zero s
  | @insert i u hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- Finite products preserve majorization on lower sets. -/
protected theorem prod (hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s)
    (u : Finset ι) {f g : ι → MvPowerSeries σ ℝ}
    (h : ∀ i ∈ u, IsMajorizedOn (f i) (g i) s) :
    IsMajorizedOn (∏ i ∈ u, f i) (∏ i ∈ u, g i) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using one s
  | @insert i u hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul hs
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- Differentiation preserves majorization wherever the required next coefficients are bounded. -/
protected theorem pderiv (h : IsMajorizedOn f g s) (i : σ)
    (ht : ∀ a ∈ t, a + Finsupp.single i 1 ∈ s) :
    IsMajorizedOn (MvPowerSeries.pderiv i f) (MvPowerSeries.pderiv i g) t := by
  intro a ha
  have hn : (0 : ℝ) ≤ (a i : ℝ) + 1 := by positivity
  rw [coeff_pderiv, coeff_pderiv, norm_mul, Real.norm_of_nonneg hn]
  exact mul_le_mul_of_nonneg_right (h _ (ht a ha)) hn

/-- Admissible substitution preserves coefficient majorants on a lower set.
The coefficient series themselves are compared in every degree. -/
protected theorem subst {s : Set (τ →₀ ℕ)}
    (hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s)
    {a b : σ → MvPowerSeries τ ℝ} (ha : HasSubst a) (hb : HasSubst b)
    (h : ∀ i, IsMajorizedOn (a i) (b i) s)
    {f g : MvPowerSeries σ ℝ} (hfg : IsMajorizedOn f g Set.univ) :
    IsMajorizedOn (MvPowerSeries.subst a f) (MvPowerSeries.subst b g) s := by
  classical
  intro e he
  rw [coeff_subst ha, coeff_subst hb]
  let u := coeff_subst_finite ha f e
  let v := coeff_subst_finite hb g e
  let t := u.toFinset ∪ v.toFinset
  rw [finsum_eq_finsetSum_of_support_subset _
    (show Function.support _ ⊆ (t : Set (σ →₀ ℕ)) from
      fun d hd ↦ Finset.mem_union_left _ (u.mem_toFinset.mpr hd))]
  rw [finsum_eq_finsetSum_of_support_subset _
    (show Function.support _ ⊆ (t : Set (σ →₀ ℕ)) from
      fun d hd ↦ Finset.mem_union_right _ (v.mem_toFinset.mpr hd))]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hprod := (IsMajorizedOn.prod hs d.support
    (fun i _ ↦ (h i).pow hs (d i))) e he
  rw [smul_eq_mul, smul_eq_mul, norm_mul]
  exact mul_le_mul (hfg d (Set.mem_univ d)) hprod (norm_nonneg _)
    (hfg.nonneg (Set.mem_univ d))

end IsMajorizedOn

end MvPowerSeries
