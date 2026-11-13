/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Algebra.Field.Periodic

/-!
# Maxima of periodic functions of two variables from their values on a mesh

A doubly periodic function `f` of `(β, θ)` with second partial derivatives bounded by `a`, `b`,
`c` (`∂_β²`, `∂_β ∂_θ`, `∂_θ²`) and values at most `m` at every node `(j h₁, n h₂)` of a mesh
is at most `m + a h₁² / 8 + b h₁ h₂ / 4 + c h₂² / 8` everywhere (`le_of_forall_mesh_le`): it
attains its maximum, both partial derivatives vanish there, and the nearest node is at most
`h₁ / 2` and `h₂ / 2` away in the two variables. The second-order Taylor bound in one variable
(`abs_sub_sub_mul_le`) and the first-order bound (`abs_sub_le_mul_abs`) are the one-variable
steps, applied first in `β` and then in `θ`. Only the bounds of the second derivatives enter, so
the mesh error is quadratic in the mesh width.
-/

@[expose] public section

namespace PDE.Analysis

open Set

/-- A derivative bounded by `K` makes the function `K`-Lipschitz. -/
theorem abs_sub_le_mul_abs {g g' : ℝ → ℝ} {K : ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hK : ∀ t, |g' t| ≤ K) (x d : ℝ) : |g (x + d) - g x| ≤ K * |d| := by
  have h := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (C := K) (fun t _ ↦ (hg t).hasDerivWithinAt) (fun t _ ↦ by
      rw [Real.norm_eq_abs]
      exact hK t) (mem_univ x) (mem_univ (x + d))
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using h

private theorem abs_sub_sub_mul_le_of_nonneg {g g' g'' : ℝ → ℝ} {K : ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (hK : ∀ t, |g'' t| ≤ K) (x : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    |g (x + d) - g x - g' x * d| ≤ K * d ^ 2 / 2 := by
  set f : ℝ → ℝ := fun t ↦ g t - g x - g' x * (t - x)
  set B : ℝ → ℝ := fun t ↦ K * (t - x) ^ 2 / 2
  have hf' : ∀ t, HasDerivAt f (g' t - g' x) t := by
    intro t
    have := ((hg t).sub_const (g x)).fun_sub (((hasDerivAt_id' t).sub_const x).const_mul (g' x))
    convert this using 1
    ring
  have hB : ∀ t, HasDerivAt B (K * (t - x)) t := by
    intro t
    have := ((((hasDerivAt_id' t).sub_const x).pow 2).const_mul K).div_const 2
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  have hbound : ∀ t ∈ Ico x (x + d), ‖g' t - g' x‖ ≤ K * (t - x) := by
    intro t ht
    have h := abs_sub_le_mul_abs hg' hK x (t - x)
    rw [add_sub_cancel, abs_of_nonneg (sub_nonneg.mpr ht.1)] at h
    simpa only [Real.norm_eq_abs] using h
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := x) (b := x + d)
    (f := f) (f' := fun t ↦ g' t - g' x) (B := B) (B' := fun t ↦ K * (t - x))
    (fun t _ ↦ (hf' t).continuousAt.continuousWithinAt) (fun t _ ↦ (hf' t).hasDerivWithinAt)
    (by simp [f, B]) hB hbound (x := x + d) ⟨by linarith, le_rfl⟩
  simpa only [f, B, Real.norm_eq_abs, add_sub_cancel_left] using hmain

/-- The second-order Taylor bound: `|g (x + d) - g x - g' x d| ≤ K d² / 2` when `|g''| ≤ K`. -/
theorem abs_sub_sub_mul_le {g g' g'' : ℝ → ℝ} {K : ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t) (hK : ∀ t, |g'' t| ≤ K) (x d : ℝ) :
    |g (x + d) - g x - g' x * d| ≤ K * d ^ 2 / 2 := by
  rcases le_total 0 d with hd | hd
  · exact abs_sub_sub_mul_le_of_nonneg hg hg' hK x hd
  · -- reflect: `G t = g (-t)`
    have hG : ∀ t, HasDerivAt (fun s ↦ g (-s)) (-g' (-t)) t := fun t ↦ by
      have := (hg (-t)).comp t (hasDerivAt_neg t)
      rw [Function.comp_def] at this
      exact this.congr_deriv (by ring)
    have hG' : ∀ t, HasDerivAt (fun s ↦ -g' (-s)) (g'' (-t)) t := fun t ↦ by
      have := ((hg' (-t)).comp t (hasDerivAt_neg t)).fun_neg
      rw [Function.comp_def] at this
      exact this.congr_deriv (by ring)
    have h := abs_sub_sub_mul_le_of_nonneg hG hG' (fun t ↦ hK (-t)) (-x) (neg_nonneg.mpr hd)
    simp only [neg_neg, ← neg_add] at h
    convert h using 2 <;> ring

/-- Values on a mesh bound a doubly periodic function with bounded second partial derivatives:
`f ≤ m + a h₁² / 8 + b h₁ h₂ / 4 + c h₂² / 8` if `f ≤ m` at the nodes `(j h₁, n h₂)`. The
functions `fβ`, `fθ` are the partial derivatives, `fββ`, `fβθ` (the `β`-derivative of `fθ`)
and `fθθ` the second ones. -/
theorem le_of_forall_mesh_le {f fβ fθ fββ fβθ fθθ : ℝ → ℝ → ℝ} {a b c p q : ℝ}
    (hcont : Continuous (Function.uncurry f))
    (hβ : ∀ β θ, HasDerivAt (fun t ↦ f t θ) (fβ β θ) β)
    (hθ : ∀ β θ, HasDerivAt (fun t ↦ f β t) (fθ β θ) θ)
    (hββ : ∀ β θ, HasDerivAt (fun t ↦ fβ t θ) (fββ β θ) β)
    (hθβ : ∀ β θ, HasDerivAt (fun t ↦ fθ t θ) (fβθ β θ) β)
    (hθθ : ∀ β θ, HasDerivAt (fun t ↦ fθ β t) (fθθ β θ) θ)
    (ha : ∀ β θ, |fββ β θ| ≤ a) (hb : ∀ β θ, |fβθ β θ| ≤ b) (hc : ∀ β θ, |fθθ β θ| ≤ c)
    (hp : 0 < p) (hq : 0 < q) (hpβ : ∀ β θ, f (β + p) θ = f β θ)
    (hpθ : ∀ β θ, f β (θ + q) = f β θ) {h₁ h₂ m : ℝ} (h₁0 : 0 < h₁) (h₂0 : 0 < h₂)
    (hnode : ∀ j n : ℤ, f (j * h₁) (n * h₂) ≤ m) (β θ : ℝ) :
    f β θ ≤ m + a * h₁ ^ 2 / 8 + b * h₁ * h₂ / 4 + c * h₂ ^ 2 / 8 := by
  -- the maximum on a period cell is a global maximum
  set K : Set (ℝ × ℝ) := Icc 0 p ×ˢ Icc 0 q
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨z, hzK, hz⟩ := hK.exists_isMaxOn ⟨(0, 0), ⟨⟨le_rfl, hp.le⟩, ⟨le_rfl, hq.le⟩⟩⟩
    hcont.continuousOn
  have hglob : ∀ x y, f x y ≤ f z.1 z.2 := by
    intro x y
    obtain ⟨x', hx', hxe⟩ := Function.Periodic.exists_mem_Ico₀ (f := fun t ↦ f t y)
      (fun t ↦ hpβ t y) hp x
    obtain ⟨y', hy', hye⟩ := Function.Periodic.exists_mem_Ico₀ (f := fun t ↦ f x' t)
      (fun t ↦ hpθ x' t) hq y
    have hmem : (x', y') ∈ K := ⟨Ico_subset_Icc_self hx', Ico_subset_Icc_self hy'⟩
    have := hz hmem
    simp only at this hxe hye
    rw [hxe, hye]
    exact this
  -- the partial derivatives vanish at the maximum
  have hzβ : fβ z.1 z.2 = 0 :=
    IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall fun t ↦ hglob t z.2)
      (hβ z.1 z.2)
  have hzθ : fθ z.1 z.2 = 0 :=
    IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall fun t ↦ hglob z.1 t)
      (hθ z.1 z.2)
  -- the nearest node
  set j := round (z.1 / h₁)
  set n := round (z.2 / h₂)
  set d₁ := (j : ℝ) * h₁ - z.1
  set d₂ := (n : ℝ) * h₂ - z.2
  have hd₁ : |d₁| ≤ h₁ / 2 := by
    have h := abs_sub_round (z.1 / h₁)
    rw [abs_sub_comm] at h
    have : d₁ = h₁ * ((j : ℝ) - z.1 / h₁) := by
      simp only [d₁]
      field_simp
    rw [this, abs_mul, abs_of_pos h₁0]
    nlinarith
  have hd₂ : |d₂| ≤ h₂ / 2 := by
    have h := abs_sub_round (z.2 / h₂)
    rw [abs_sub_comm] at h
    have : d₂ = h₂ * ((n : ℝ) - z.2 / h₂) := by
      simp only [d₂]
      field_simp
    rw [this, abs_mul, abs_of_pos h₂0]
    nlinarith
  -- Taylor in `β`, then in `θ`
  have t1 := abs_sub_sub_mul_le (hβ · z.2) (hββ · z.2) (ha · z.2) z.1 d₁
  rw [hzβ, zero_mul, sub_zero] at t1
  have t2 := abs_sub_sub_mul_le (hθ (z.1 + d₁) ·) (hθθ (z.1 + d₁) ·) (hc (z.1 + d₁) ·) z.2 d₂
  have t3 := abs_sub_le_mul_abs (hθβ · z.2) (hb · z.2) z.1 d₁
  rw [hzθ, sub_zero] at t3
  have hnode' := hnode j n
  have e1 : (j : ℝ) * h₁ = z.1 + d₁ := by simp only [d₁]; ring
  have e2 : (n : ℝ) * h₂ = z.2 + d₂ := by simp only [d₂]; ring
  rw [e1, e2] at hnode'
  have hab : |fθ (z.1 + d₁) z.2 * d₂| ≤ b * |d₁| * |d₂| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right t3 (abs_nonneg _)
  have h0b : 0 ≤ b := (abs_nonneg _).trans (hb 0 0)
  have h0a : 0 ≤ a := (abs_nonneg _).trans (ha 0 0)
  have h0c : 0 ≤ c := (abs_nonneg _).trans (hc 0 0)
  have hsq₁ : d₁ ^ 2 ≤ h₁ ^ 2 / 4 := by
    have := sq_le_sq' (abs_le.mp hd₁).1 (abs_le.mp hd₁).2
    linarith
  have hsq₂ : d₂ ^ 2 ≤ h₂ ^ 2 / 4 := by
    have := sq_le_sq' (abs_le.mp hd₂).1 (abs_le.mp hd₂).2
    linarith
  have hprod : |d₁| * |d₂| ≤ h₁ / 2 * (h₂ / 2) :=
    mul_le_mul hd₁ hd₂ (abs_nonneg _) (by linarith)
  have hmax : f z.1 z.2 ≤ m + a * h₁ ^ 2 / 8 + b * h₁ * h₂ / 4 + c * h₂ ^ 2 / 8 := by
    have := abs_le.mp t1
    have := abs_le.mp t2
    have := abs_le.mp hab
    have : b * (|d₁| * |d₂|) ≤ b * (h₁ / 2 * (h₂ / 2)) := mul_le_mul_of_nonneg_left hprod h0b
    have : a * d₁ ^ 2 ≤ a * (h₁ ^ 2 / 4) := mul_le_mul_of_nonneg_left hsq₁ h0a
    have : c * d₂ ^ 2 ≤ c * (h₂ ^ 2 / 4) := mul_le_mul_of_nonneg_left hsq₂ h0c
    nlinarith
  exact (hglob β θ).trans hmax

end PDE.Analysis
