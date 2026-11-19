/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounded Hölder functions on a set

`HolderSpace.IsBoundedHolderOn α s f A` states that `|f| ≤ A` on `s` and `|f x - f z| ≤ A ‖x - z‖^α`
for `x, z ∈ s`, with one constant for both. This is the form in which weighted estimates of products
are assembled: the class is closed under sums and products. A bounded function with bounded
derivative on a convex set is in the class: Mathlib's mean value inequality
`Convex.norm_image_sub_le_of_norm_fderiv_le` handles `‖x - z‖ ≤ 1`, and the bound on `|f|` handles
`‖x - z‖ > 1`. Functions vanishing at the origin with a singular derivative enter through
`HolderSpace.norm_sub_le_of_rpow_bounds`.

## Main definitions

* `IsBoundedHolderOn`: `|f| ≤ A` and `|f x - f z| ≤ A ‖x - z‖^α` on `s`.

## Main results

* `IsBoundedHolderOn.add`: the constant of `f + g` is `A + B`.
* `IsBoundedHolderOn.mul`: the constant of `f g` is `2 A B`.
* `IsBoundedHolderOn.finsetSum`: finite sums stay in the class.
* `IsBoundedHolderOn.of_norm_fderiv_le`: a bounded function with bounded derivative on a convex
  set is bounded and `α`-Hölder for `0 ≤ α ≤ 1`, with the constant `2 A`.
* `IsBoundedHolderOn.of_eq_zero`: a bound on the part of `s` inside `B(0, ρ + 1)` and the
  vanishing of `f` beyond `ρ` give a bound on `s` with twice the constant.
-/

@[expose] public section

noncomputable section

open Set Metric

namespace HolderSpace

variable {E : Type*} [NormedAddCommGroup E]

/-- **`f` is bounded and `α`-Hölder on `s` with the constant `A`**: `|f x| ≤ A` and
`|f x - f z| ≤ A ‖x - z‖^α` for `x, z ∈ s`. -/
structure IsBoundedHolderOn (α : ℝ) (s : Set E) (f : E → ℝ) (A : ℝ) : Prop where
  /-- The bound of the values. -/
  abs_le : ∀ x ∈ s, |f x| ≤ A
  /-- The Hölder bound. -/
  abs_sub_le : ∀ x ∈ s, ∀ z ∈ s, |f x - f z| ≤ A * ‖x - z‖ ^ α

namespace IsBoundedHolderOn

variable {α A B : ℝ} {s t : Set E} {f g : E → ℝ}

/-- If `s` contains a point, the constant `A` is nonnegative. -/
theorem nonneg (h : IsBoundedHolderOn α s f A) {x : E} (hx : x ∈ s) : 0 ≤ A :=
  (abs_nonneg _).trans (h.abs_le x hx)

/-- The constant may be enlarged: a bound with `A` holds with every `B ≥ A`. -/
theorem mono (h : IsBoundedHolderOn α s f A) (hAB : A ≤ B) : IsBoundedHolderOn α s f B :=
  ⟨fun x hx ↦ (h.abs_le x hx).trans hAB, fun x hx z hz ↦ (h.abs_sub_le x hx z hz).trans
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (norm_nonneg _) _))⟩

/-- A bound on `s` holds on every subset `t ⊆ s` with the same constant. -/
theorem mono_set (h : IsBoundedHolderOn α s f A) (hts : t ⊆ s) : IsBoundedHolderOn α t f A :=
  ⟨fun x hx ↦ h.abs_le x (hts hx), fun x hx z hz ↦ h.abs_sub_le x (hts hx) z (hts hz)⟩

/-- A bound for `f` on `s` holds for every `g` equal to `f` on `s`. -/
theorem congr (h : IsBoundedHolderOn α s f A) (hfg : EqOn f g s) : IsBoundedHolderOn α s g A :=
  ⟨fun x hx ↦ by rw [← hfg hx]; exact h.abs_le x hx, fun x hx z hz ↦ by
    rw [← hfg hx, ← hfg hz]; exact h.abs_sub_le x hx z hz⟩

/-- A constant is bounded and Hölder with its absolute value. -/
theorem const (k : ℝ) : IsBoundedHolderOn α s (fun _ ↦ k) |k| :=
  ⟨fun _ _ ↦ le_rfl, fun _ _ _ _ ↦ by
    simp only [sub_self, abs_zero]; exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg
      (norm_nonneg _) _)⟩

/-- The zero function is bounded and Hölder with the constant `0`. -/
theorem zero : IsBoundedHolderOn α s (fun _ ↦ (0 : ℝ)) 0 := by
  simpa using const (α := α) (s := s) (0 : ℝ)

/-- **Sums**: the constant of `f + g` is `A + B`. -/
theorem add (hf : IsBoundedHolderOn α s f A) (hg : IsBoundedHolderOn α s g B) :
    IsBoundedHolderOn α s (fun x ↦ f x + g x) (A + B) :=
  ⟨fun x hx ↦ (abs_add_le _ _).trans (add_le_add (hf.abs_le x hx) (hg.abs_le x hx)),
    fun x hx z hz ↦ by
      calc |f x + g x - (f z + g z)| = |(f x - f z) + (g x - g z)| := by ring_nf
        _ ≤ |f x - f z| + |g x - g z| := abs_add_le _ _
        _ ≤ A * ‖x - z‖ ^ α + B * ‖x - z‖ ^ α :=
            add_le_add (hf.abs_sub_le x hx z hz) (hg.abs_sub_le x hx z hz)
        _ = (A + B) * ‖x - z‖ ^ α := by ring⟩

/-- **Negation**: `-f` keeps the constant `A`. -/
theorem neg (hf : IsBoundedHolderOn α s f A) : IsBoundedHolderOn α s (fun x ↦ -f x) A :=
  ⟨fun x hx ↦ by rw [abs_neg]; exact hf.abs_le x hx, fun x hx z hz ↦ by
    rw [show -f x - -f z = -(f x - f z) by ring, abs_neg]; exact hf.abs_sub_le x hx z hz⟩

/-- **Differences**: the constant of `f - g` is `A + B`. -/
theorem sub (hf : IsBoundedHolderOn α s f A) (hg : IsBoundedHolderOn α s g B) :
    IsBoundedHolderOn α s (fun x ↦ f x - g x) (A + B) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- **Scalar multiples**: the constant of `k f` is `|k| A`. -/
theorem const_mul (hf : IsBoundedHolderOn α s f A) (k : ℝ) :
    IsBoundedHolderOn α s (fun x ↦ k * f x) (|k| * A) :=
  ⟨fun x hx ↦ by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf.abs_le x hx) (abs_nonneg _),
    fun x hx z hz ↦ by
      rw [← mul_sub, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hf.abs_sub_le x hx z hz) (abs_nonneg _)⟩

/-- **Products**: the constant of `f g` is `2 A B`. -/
theorem mul (hf : IsBoundedHolderOn α s f A) (hg : IsBoundedHolderOn α s g B) :
    IsBoundedHolderOn α s (fun x ↦ f x * g x) (2 * (A * B)) := by
  refine ⟨fun x hx ↦ ?_, fun x hx z hz ↦ ?_⟩
  · have hA := hf.nonneg hx
    have hB := hg.nonneg hx
    rw [abs_mul]
    calc |f x| * |g x| ≤ A * B :=
          mul_le_mul (hf.abs_le x hx) (hg.abs_le x hx) (abs_nonneg _) hA
      _ ≤ 2 * (A * B) := by nlinarith [mul_nonneg hA hB]
  · have hA := hf.nonneg hx
    have hB := hg.nonneg hx
    have hp : 0 ≤ ‖x - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have e : f x * g x - f z * g z = (f x - f z) * g z + f x * (g x - g z) := by ring
    calc |f x * g x - f z * g z| ≤ |f x - f z| * |g z| + |f x| * |g x - g z| := by
          rw [e]; exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
      _ ≤ A * ‖x - z‖ ^ α * B + A * (B * ‖x - z‖ ^ α) :=
          add_le_add (mul_le_mul (hf.abs_sub_le x hx z hz) (hg.abs_le z hz) (abs_nonneg _)
              (mul_nonneg hA hp))
            (mul_le_mul (hf.abs_le x hx) (hg.abs_sub_le x hx z hz) (abs_nonneg _) hA)
      _ = 2 * (A * B) * ‖x - z‖ ^ α := by ring

/-- **Finite sums**: the constant of `∑ i ∈ u, F i` is `∑ i ∈ u, C i`. -/
theorem finsetSum {ι : Type*} (u : Finset ι) {F : ι → E → ℝ} {C : ι → ℝ}
    (h : ∀ i ∈ u, IsBoundedHolderOn α s (F i) (C i)) :
    IsBoundedHolderOn α s (fun x ↦ ∑ i ∈ u, F i x) (∑ i ∈ u, C i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using (zero : IsBoundedHolderOn α s (fun _ ↦ (0 : ℝ)) 0)
  | insert a u ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a u)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-! ### Sources -/

variable [NormedSpace ℝ E] in
/-- **A bounded function with bounded derivative on a convex set** is bounded and `α`-Hölder
for `0 ≤ α ≤ 1`, with the constant `2 A`. -/
theorem of_norm_fderiv_le (hs : Convex ℝ s) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hA : 0 ≤ A)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hf : ∀ x ∈ s, |f x| ≤ A)
    (hf' : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ A) : IsBoundedHolderOn α s f (2 * A) := by
  refine ⟨fun x hx ↦ (hf x hx).trans (by linarith), fun x hx z hz ↦ ?_⟩
  rcases le_or_gt ‖x - z‖ 1 with h1 | h1
  · have hmv := hs.norm_image_sub_le_of_norm_fderiv_le hd hf' hz hx
    rw [Real.norm_eq_abs] at hmv
    calc |f x - f z| ≤ A * ‖x - z‖ := hmv
      _ ≤ A * ‖x - z‖ ^ α := mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one (norm_nonneg _)
          h1
          hα1) hA
      _ ≤ 2 * A * ‖x - z‖ ^ α := by
          have := Real.rpow_nonneg (norm_nonneg (x - z)) α
          nlinarith
  · have hp : 1 ≤ ‖x - z‖ ^ α := Real.one_le_rpow h1.le hα0
    calc |f x - f z| ≤ |f x| + |f z| := abs_sub _ _
      _ ≤ 2 * A := by linarith [hf x hx, hf z hz]
      _ ≤ 2 * A * ‖x - z‖ ^ α := le_mul_of_one_le_right (by linarith) hp

/-- **Gluing**: if `f` vanishes at the points of `s` with `‖x‖ ≥ ρ` and is bounded and Hölder on
the part of `s` inside `B(0, ρ + 1)`, then it is bounded and Hölder on `s` with twice the
constant. -/
theorem of_eq_zero (hα : 0 ≤ α) (hA : 0 ≤ A) {ρ : ℝ}
    (h : IsBoundedHolderOn α (s ∩ ball 0 (ρ + 1)) f A) (h0 : ∀ x ∈ s, ρ ≤ ‖x‖ → f x = 0) :
    IsBoundedHolderOn α s f (2 * A) := by
  have hval : ∀ x ∈ s, |f x| ≤ A := by
    intro x hx
    by_cases hxρ : ρ ≤ ‖x‖
    · rw [h0 x hx hxρ, abs_zero]; exact hA
    · exact h.abs_le x ⟨hx, by rw [mem_ball_zero_iff]; linarith⟩
  refine ⟨fun x hx ↦ (hval x hx).trans (by linarith), fun x hx z hz ↦ ?_⟩
  rcases le_or_gt 1 ‖x - z‖ with h1 | h1
  · calc |f x - f z| ≤ |f x| + |f z| := abs_sub _ _
      _ ≤ 2 * A := by linarith [hval x hx, hval z hz]
      _ ≤ 2 * A * ‖x - z‖ ^ α := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow h1 hα)
  · by_cases hx' : ρ ≤ ‖x‖
    · by_cases hz' : ρ ≤ ‖z‖
      · rw [h0 x hx hx', h0 z hz hz', sub_self, abs_zero]
        exact mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
      · have hxb : ‖x‖ < ρ + 1 := by
          have := norm_sub_norm_le x z; push Not at hz'; linarith
        refine (h.abs_sub_le x ⟨hx, mem_ball_zero_iff.2 hxb⟩ z
          ⟨hz, mem_ball_zero_iff.2 (by push Not at hz'; linarith)⟩).trans ?_
        have := Real.rpow_nonneg (norm_nonneg (x - z)) α
        nlinarith
    · have hzb : ‖z‖ < ρ + 1 := by
        have := norm_sub_norm_le z x; rw [norm_sub_rev] at this; push Not at hx'; linarith
      refine (h.abs_sub_le x ⟨hx, mem_ball_zero_iff.2 (by push Not at hx'; linarith)⟩ z
        ⟨hz, mem_ball_zero_iff.2 hzb⟩).trans ?_
      have := Real.rpow_nonneg (norm_nonneg (x - z)) α
      nlinarith

end IsBoundedHolderOn

end HolderSpace
