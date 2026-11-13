/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import PDE.Analysis.Scalar.LogPowerOptimization

/-!
# Increments along coordinate paths

Mean value bounds through coordinate partial derivatives along paths made of segments parallel
to the axes. In the open quadrant of the plane, two points outside the square `(0, ρ)²` are
joined by two coordinate segments that stay outside it, so only bounds of `|∂₀ f|, |∂₁ f|`
outside the square are needed. Two elementary bounds handle distant pairs.

These are steps of the Hölder estimates at large distance in Chen and Hou, Supplementary
material I, Section 8.8: the distance comparison in (8.67) and the Lipschitz bound of the
velocity, (8.68) and the case after it. The far-field Hölder product estimate is (8.63) in
Section 8.7.1.

## Main results

* `abs_sub_le_of_partialDeriv_le_coordinateLine`: along a coordinate segment the increment is at
  most the length times a bound of the partial derivative in that direction.
* `abs_sub_le_of_partialDeriv_le_offSquare`: `|f(x) - f(z)| ≤ A₀ |x₀ - z₀| + A₁ |x₁ - z₁|` for
  points outside the square, with bounds `A₀, A₁` of `|∂₀ f|, |∂₁ f|` outside the square only.
* `norm_le_div_sub_mul_norm_sub`: `|z| ≤ b/(b - a) |x - z|` when `|x| ≤ a < b ≤ |z|`.
* `abs_sub_div_norm_le`: `|f(x) - f(z)|/|x - z| ≤ |f(x)|/|x - z| + (3/2) |f(z)|/|z|` when
  `|x| ≤ |x - z|/2`.
* `abs_sub_le_of_separated`: the Lipschitz bound at distance at least `ρ` from derivative bounds
  outside the square `(0, ρ/(2√2))²` and value bounds.
* `abs_sub_div_sqrt_le_sqrt_mul`: `|δf|/|x - z|^{1/2} ≤ √(A B)` from `|δf| ≤ A` and
  `|δf| ≤ B |x - z|`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Supplementary material I (in the
  same PDF), Section 8.7.1, (8.63), and Section 8.8, (8.67)-(8.68).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set

variable {n : ℕ}

/-- **Mean value along a coordinate segment**: if `f` is differentiable along the segment of the
coordinate line through `a` in direction `i` between the parameters `s` and `t`, with
`|∂ᵢ f| ≤ A` there, then `|f(line t) - f(line s)| ≤ A |t - s|`. -/
theorem abs_sub_le_of_partialDeriv_le_coordinateLine {f : ℝ^n → ℝ} (i : Fin n) (a : ℝ^n)
    {s t A : ℝ} (hf : ∀ u ∈ uIcc s t, DifferentiableAt ℝ f (coordinateLine i a u))
    (hA : ∀ u ∈ uIcc s t, |(∂[i] f) (coordinateLine i a u)| ≤ A) :
    |f (coordinateLine i a t) - f (coordinateLine i a s)| ≤ A * |t - s| := by
  have hd : ∀ u ∈ uIcc s t, HasDerivWithinAt (f ∘ coordinateLine i a)
      ((∂[i] f) (coordinateLine i a u)) (uIcc s t) u := fun u hu ↦
    (HasFDerivAt.comp_hasDerivAt (x := u) (hf u hu).hasFDerivAt
      (hasDerivAt_coordinateLine i a u)).hasDerivWithinAt
  have h := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun u hu ↦ by rw [Real.norm_eq_abs]; exact hA u hu) left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs] using h

/-- The coordinate line through `x` in direction `i` keeps every coordinate `k ≠ i` of `x`. -/
private theorem coordinateLine_apply_ne {i k : Fin n} (hik : k ≠ i) (x : ℝ^n) (s : ℝ) :
    coordinateLine i x s k = x k := by
  simp [coordinateLine, hik]

/-- The points outside the open corner square `(0, ρ)²` of the open quadrant. -/
private def OffSquare (ρ : ℝ) (y : ℝ^2) : Prop :=
  0 < y 0 ∧ 0 < y 1 ∧ (ρ ≤ y 0 ∨ ρ ≤ y 1)

/-- A point of `[[a, b]]` is positive when `a` and `b` are positive. -/
private theorem pos_of_mem_uIcc {a b u : ℝ} (ha : 0 < a) (hb : 0 < b) (hu : u ∈ uIcc a b) :
    0 < u :=
  lt_of_lt_of_le (lt_min ha hb) (mem_uIcc.1 hu |>.elim (fun h ↦ (min_le_left a b).trans h.1)
    fun h ↦ (min_le_right a b).trans h.1)

/-- A point of `[[a, b]]` is at least `ρ` when `a` and `b` are at least `ρ`. -/
private theorem le_of_mem_uIcc {ρ a b u : ℝ} (ha : ρ ≤ a) (hb : ρ ≤ b) (hu : u ∈ uIcc a b) :
    ρ ≤ u :=
  (le_min ha hb).trans (mem_uIcc.1 hu |>.elim (fun h ↦ (min_le_left a b).trans h.1)
    fun h ↦ (min_le_right a b).trans h.1)

/-- One leg in direction `i` of the two-leg path, from the point `a` to the point that agrees
with `a` except in coordinate `i`, where it takes the value `t`. -/
private theorem abs_leg_le {f : ℝ^2 → ℝ} {ρ A : ℝ} (i : Fin 2)
    (hf : ∀ y, OffSquare ρ y → DifferentiableAt ℝ f y)
    (hA : ∀ y, OffSquare ρ y → |(∂[i] f) y| ≤ A) (a : ℝ^2) (t : ℝ)
    (hleg : ∀ u ∈ uIcc (a i) t, OffSquare ρ (coordinateLine i a u)) :
    |f (coordinateLine i a t) - f a| ≤ A * |t - a i| := by
  have h := abs_sub_le_of_partialDeriv_le_coordinateLine i a (s := a i) (t := t)
    (fun u hu ↦ hf _ (hleg u hu)) (fun u hu ↦ hA _ (hleg u hu))
  rwa [coordinateLine_self] at h

/-- **Two coordinate legs outside a corner square**, Supplement I (8.68): let `f` be
differentiable at the points of the open quadrant outside the square `(0, ρ)²`, with
`|∂₀ f| ≤ A₀` and `|∂₁ f| ≤ A₁` there. For two points `x`, `z` of the open quadrant outside the
square, `|f(x) - f(z)| ≤ A₀ |x₀ - z₀| + A₁ |x₁ - z₁|`: the path through `(x₀, z₁)` (if `x₀ ≥ ρ`)
or through `(z₀, x₁)` (otherwise) stays outside the square. -/
theorem abs_sub_le_of_partialDeriv_le_offSquare {f : ℝ^2 → ℝ} {ρ A₀ A₁ : ℝ}
    (hf : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → (ρ ≤ y 0 ∨ ρ ≤ y 1) → DifferentiableAt ℝ f y)
    (h₀ : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → (ρ ≤ y 0 ∨ ρ ≤ y 1) →
      |(∂[(0 : Fin 2)] f) y| ≤ A₀)
    (h₁ : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → (ρ ≤ y 0 ∨ ρ ≤ y 1) →
      |(∂[(1 : Fin 2)] f) y| ≤ A₁)
    {x z : ℝ^2} (hx0 : 0 < x 0) (hx1 : 0 < x 1) (hz0 : 0 < z 0) (hz1 : 0 < z 1)
    (hx : ρ ≤ x 0 ∨ ρ ≤ x 1) (hz : ρ ≤ z 0 ∨ ρ ≤ z 1) :
    |f x - f z| ≤ A₀ * |x 0 - z 0| + A₁ * |x 1 - z 1| := by
  have hf' : ∀ y, OffSquare ρ y → DifferentiableAt ℝ f y := fun y hy ↦ hf y hy.1 hy.2.1 hy.2.2
  have h₀' : ∀ y, OffSquare ρ y → |(∂[(0 : Fin 2)] f) y| ≤ A₀ :=
    fun y hy ↦ h₀ y hy.1 hy.2.1 hy.2.2
  have h₁' : ∀ y, OffSquare ρ y → |(∂[(1 : Fin 2)] f) y| ≤ A₁ :=
    fun y hy ↦ h₁ y hy.1 hy.2.1 hy.2.2
  have l0 : ∀ (a : ℝ^2) (s : ℝ), coordinateLine 0 a s 0 = s := fun a s ↦
    coordinateLine_apply_same 0 a s
  have l1 : ∀ (a : ℝ^2) (s : ℝ), coordinateLine 1 a s 1 = s := fun a s ↦
    coordinateLine_apply_same 1 a s
  have l01 : ∀ (a : ℝ^2) (s : ℝ), coordinateLine 0 a s 1 = a 1 := fun a s ↦
    coordinateLine_apply_ne (by decide) a s
  have l10 : ∀ (a : ℝ^2) (s : ℝ), coordinateLine 1 a s 0 = a 0 := fun a s ↦
    coordinateLine_apply_ne (by decide) a s
  rcases hx with hρx | hρx
  · -- the path `x → (x₀, z₁) → z`
    set w := coordinateLine 1 x (z 1)
    have hw0 : w 0 = x 0 := l10 x (z 1)
    have hw1 : w 1 = z 1 := l1 x (z 1)
    have hzw : coordinateLine 0 w (z 0) = z := by
      ext k; fin_cases k
      · exact l0 w (z 0)
      · simpa [hw1] using l01 w (z 0)
    have e₁ := abs_leg_le 1 hf' h₁' x (z 1) fun u hu ↦ by
      refine ⟨?_, ?_, Or.inl ?_⟩
      · rw [l10]; exact hx0
      · rw [l1]; exact pos_of_mem_uIcc hx1 hz1 hu
      · rw [l10]; exact hρx
    have e₀ := abs_leg_le 0 hf' h₀' w (z 0) fun u hu ↦ by
      rw [hw0] at hu
      refine ⟨?_, ?_, ?_⟩
      · rw [l0]; exact pos_of_mem_uIcc hx0 hz0 hu
      · rw [l01, hw1]; exact hz1
      · rcases hz with hρz | hρz
        · exact Or.inl (by rw [l0]; exact le_of_mem_uIcc hρx hρz hu)
        · exact Or.inr (by rw [l01, hw1]; exact hρz)
    rw [hzw, hw0] at e₀
    calc |f x - f z| = |(f w - f x) + (f z - f w)| * 1 := by
          rw [mul_one, ← abs_neg]; congr 1; ring
      _ ≤ |f w - f x| + |f z - f w| := by rw [mul_one]; exact abs_add_le _ _
      _ ≤ A₁ * |z 1 - x 1| + A₀ * |z 0 - x 0| := add_le_add e₁ e₀
      _ = A₀ * |x 0 - z 0| + A₁ * |x 1 - z 1| := by
          rw [abs_sub_comm (z 1), abs_sub_comm (z 0)]; ring
  · -- the path `x → (z₀, x₁) → z`
    set w := coordinateLine 0 x (z 0)
    have hw0 : w 0 = z 0 := l0 x (z 0)
    have hw1 : w 1 = x 1 := l01 x (z 0)
    have hzw : coordinateLine 1 w (z 1) = z := by
      ext k; fin_cases k
      · simpa [hw0] using l10 w (z 1)
      · exact l1 w (z 1)
    have e₀ := abs_leg_le 0 hf' h₀' x (z 0) fun u hu ↦ by
      refine ⟨?_, ?_, Or.inr ?_⟩
      · rw [l0]; exact pos_of_mem_uIcc hx0 hz0 hu
      · rw [l01]; exact hx1
      · rw [l01]; exact hρx
    have e₁ := abs_leg_le 1 hf' h₁' w (z 1) fun u hu ↦ by
      rw [hw1] at hu
      refine ⟨?_, ?_, ?_⟩
      · rw [l10, hw0]; exact hz0
      · rw [l1]; exact pos_of_mem_uIcc hx1 hz1 hu
      · rcases hz with hρz | hρz
        · exact Or.inl (by rw [l10, hw0]; exact hρz)
        · exact Or.inr (by rw [l1]; exact le_of_mem_uIcc hρx hρz hu)
    rw [hzw, hw1] at e₁
    calc |f x - f z| = |(f w - f x) + (f z - f w)| := by
          rw [← abs_neg]; congr 1; ring
      _ ≤ |f w - f x| + |f z - f w| := abs_add_le _ _
      _ ≤ A₀ * |z 0 - x 0| + A₁ * |z 1 - x 1| := add_le_add e₀ e₁
      _ = A₀ * |x 0 - z 0| + A₁ * |x 1 - z 1| := by rw [abs_sub_comm (z 1), abs_sub_comm (z 0)]

section Distant

variable {E : Type*} [NormedAddCommGroup E]

/-- **The far point is comparable with the distance**, Supplement I (8.67): if `|x| ≤ a < b ≤ |z|`
then `|z| ≤ b/(b - a) |x - z|`. -/
theorem norm_le_div_sub_mul_norm_sub {x z : E} {a b : ℝ} (hx : ‖x‖ ≤ a) (hab : a < b)
    (hz : b ≤ ‖z‖) : ‖z‖ ≤ b / (b - a) * ‖x - z‖ := by
  have hba : 0 < b - a := by linarith
  have h₁ : ‖z‖ - ‖x‖ ≤ ‖x - z‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le z x
  have hb : 0 < b := (norm_nonneg x).trans_lt (hx.trans_lt hab)
  rw [div_mul_eq_mul_div, le_div_iff₀ hba]
  -- `|z| (b - a) ≤ |z| (b - a) + a (|z| - b) ≤ b (|z| - |x|) ≤ b |x - z|`
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have h₃ : b * ‖x‖ ≤ ‖z‖ * a := by
    calc b * ‖x‖ ≤ b * a := mul_le_mul_of_nonneg_left hx hb.le
      _ ≤ ‖z‖ * a := mul_le_mul_of_nonneg_right hz ha
  have h₂ : ‖z‖ * (b - a) ≤ b * (‖z‖ - ‖x‖) := by nlinarith
  nlinarith

/-- **A near point and a distant point**, Supplement I, Section 8.8: if `|x| ≤ |x - z|/2` and
`z ≠ 0` then `|f(x) - f(z)| / |x - z| ≤ |f(x)|/|x - z| + (3/2) |f(z)|/|z|`, since
`|z| ≤ (3/2) |x - z|`. -/
theorem abs_sub_div_norm_le {F : Type*} [NormedAddCommGroup F] (f : E → F) {x z : E}
    (hxz : ‖x‖ ≤ ‖x - z‖ / 2) (hz : z ≠ 0) :
    ‖f x - f z‖ / ‖x - z‖ ≤ ‖f x‖ / ‖x - z‖ + 3 / 2 * (‖f z‖ / ‖z‖) := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hz' : ‖z‖ ≤ 3 / 2 * ‖x - z‖ := by
    have := norm_sub_norm_le z x
    rw [norm_sub_rev z x] at this
    linarith
  have hd : 0 < ‖x - z‖ := by linarith
  have h₁ : ‖f z‖ / ‖x - z‖ ≤ 3 / 2 * (‖f z‖ / ‖z‖) := by
    rw [div_le_iff₀ hd, mul_comm (3 / 2 : ℝ), mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hzn]
    nlinarith [norm_nonneg (f z)]
  calc ‖f x - f z‖ / ‖x - z‖ ≤ (‖f x‖ + ‖f z‖) / ‖x - z‖ :=
        div_le_div_of_nonneg_right (norm_sub_le _ _) hd.le
    _ = ‖f x‖ / ‖x - z‖ + ‖f z‖ / ‖x - z‖ := add_div _ _ _
    _ ≤ _ := add_le_add le_rfl h₁

/-- **A Hölder quotient from a value bound and a Lipschitz bound**, Supplement I (8.63): if
`|f(x) - f(z)| ≤ A` and `|f(x) - f(z)| ≤ B |x - z|` with `A, B ≥ 0`, then
`|f(x) - f(z)| / |x - z|^{1/2} ≤ √(A B)`: the first bound wins at large distance, the second at
small distance. -/
theorem abs_sub_div_sqrt_le_sqrt_mul {F : Type*} [NormedAddCommGroup F] {f : E → F} {x z : E}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h₁ : ‖f x - f z‖ ≤ A) (h₂ : ‖f x - f z‖ ≤ B * ‖x - z‖) :
    ‖f x - f z‖ / √‖x - z‖ ≤ √(A * B) := by
  rcases eq_or_lt_of_le (norm_nonneg (x - z)) with hd | hd
  · rw [← hd, Real.sqrt_zero, div_zero]; exact Real.sqrt_nonneg _
  have hs : 0 < √‖x - z‖ := Real.sqrt_pos.2 hd
  refine (le_min (div_le_div_of_nonneg_right h₁ hs.le) ?_).trans
    (min_div_sqrt_mul_sqrt_le hA hB hd)
  rw [div_le_iff₀ hs, mul_assoc, Real.mul_self_sqrt hd.le]
  exact h₂

end Distant

/-- `|h₁| + |h₂| ≤ √2 |h|` in the plane. -/
theorem abs_add_abs_le_sqrt_two_mul_norm (h : ℝ^2) : |h 0| + |h 1| ≤ √2 * ‖h‖ := by
  have hsq : (|h 0| + |h 1|) ^ 2 ≤ (√2 * ‖h‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), EuclideanSpace.norm_eq, Fin.sum_univ_two,
      Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|h 0| - |h 1|)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 hsq

/-- **The Lipschitz bound at large distance**, Supplement I (8.68): let `f` be differentiable at
the points of the open quadrant outside the square `(0, ρ/(2√2))²` with `|∂ᵢ f| ≤ A` there, let
`|f| ≤ B` on the quadrant within `|y| ≤ ρ/2` and `|f(y)| ≤ V |y|` for `|y| ≥ ρ/2`. Then
`|f(x) - f(z)| ≤ max(√2 A, B/ρ + (3/2) V) |x - z|` for points of the open quadrant with
`|x - z| ≥ ρ > 0`: either both points lie outside the square (two coordinate legs), or one of
them lies in it and the other is far (`abs_sub_div_norm_le`). -/
theorem abs_sub_le_of_separated {f : ℝ^2 → ℝ} {ρ A B V : ℝ} (hρ : 0 < ρ)
    (hf : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → (ρ / (2 * √2) ≤ y 0 ∨ ρ / (2 * √2) ≤ y 1) →
      DifferentiableAt ℝ f y)
    (hA : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → (ρ / (2 * √2) ≤ y 0 ∨ ρ / (2 * √2) ≤ y 1) →
      ∀ i : Fin 2, |(∂[i] f) y| ≤ A)
    (hB : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → ‖y‖ ≤ ρ / 2 → |f y| ≤ B)
    (hV : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → ρ / 2 ≤ ‖y‖ → |f y| ≤ V * ‖y‖)
    {x z : ℝ^2} (hx0 : 0 < x 0) (hx1 : 0 < x 1) (hz0 : 0 < z 0) (hz1 : 0 < z 1)
    (hxz : ρ ≤ ‖x - z‖) :
    |f x - f z| ≤ max (√2 * A) (B / ρ + 3 / 2 * V) * ‖x - z‖ := by
  set s := ρ / (2 * √2) with hs_def
  have h2 : (0 : ℝ) < √2 := by positivity
  have hd : 0 < ‖x - z‖ := hρ.trans_le hxz
  -- points in the open square are within `ρ/2` of the origin
  have hsq : ∀ y : ℝ^2, 0 < y 0 → 0 < y 1 → y 0 < s → y 1 < s → ‖y‖ ≤ ρ / 2 := by
    intro y hy0 hy1 hys0 hys1
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_left (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
    have e₀ := pow_le_pow_left₀ hy0.le hys0.le 2
    have e₁ := pow_le_pow_left₀ hy1.le hys1.le 2
    have hs2 : s ^ 2 = ρ ^ 2 / 8 := by
      rw [hs_def, div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
    nlinarith
  -- one point near the origin, the other far from it
  have hnear : ∀ p q : ℝ^2, 0 < q 0 → 0 < q 1 → |f p| ≤ B → ‖p‖ ≤ ρ / 2 →
      ρ ≤ ‖p - q‖ → |f p - f q| ≤ (B / ρ + 3 / 2 * V) * ‖p - q‖ := by
    intro p q hq0 hq1 hfp hp hpq
    have hdq : 0 < ‖p - q‖ := hρ.trans_le hpq
    have hp' : ‖p‖ ≤ ‖p - q‖ / 2 := hp.trans (by linarith)
    have hq : ρ / 2 ≤ ‖q‖ := by
      have := norm_sub_le p q
      linarith
    have hqn : 0 < ‖q‖ := lt_of_lt_of_le (by positivity) hq
    have hqne : q ≠ 0 := norm_pos_iff.1 hqn
    have h := abs_sub_div_norm_le f hp' hqne
    simp only [Real.norm_eq_abs] at h
    have hB0 : 0 ≤ B := (abs_nonneg _).trans hfp
    have h₁ : |f p| / ‖p - q‖ ≤ B / ρ := div_le_div₀ hB0 hfp hρ hpq
    have h₂ : |f q| / ‖q‖ ≤ V := by
      rw [div_le_iff₀ hqn]; exact hV q hq0 hq1 hq
    have h₃ : |f p - f q| / ‖p - q‖ ≤ B / ρ + 3 / 2 * V := by linarith
    rwa [div_le_iff₀ hdq] at h₃
  by_cases hxs : x 0 < s ∧ x 1 < s
  · have hxn := hsq x hx0 hx1 hxs.1 hxs.2
    exact (hnear x z hz0 hz1 (hB x hx0 hx1 hxn) hxn hxz).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hd.le)
  by_cases hzs : z 0 < s ∧ z 1 < s
  · have hzn := hsq z hz0 hz1 hzs.1 hzs.2
    have h := hnear z x hx0 hx1 (hB z hz0 hz1 hzn) hzn (by rwa [norm_sub_rev])
    rw [abs_sub_comm, norm_sub_rev] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd.le)
  -- both points lie outside the square
  have hx : s ≤ x 0 ∨ s ≤ x 1 := by
    by_contra hc; push Not at hc; exact hxs hc
  have hz : s ≤ z 0 ∨ s ≤ z 1 := by
    by_contra hc; push Not at hc; exact hzs hc
  have h := abs_sub_le_of_partialDeriv_le_offSquare (f := f) (ρ := s) (A₀ := A) (A₁ := A)
    hf (fun y h0 h1 hy ↦ hA y h0 h1 hy 0) (fun y h0 h1 hy ↦ hA y h0 h1 hy 1) hx0 hx1 hz0 hz1 hx hz
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA x hx0 hx1 hx 0)
  have hn := abs_add_abs_le_sqrt_two_mul_norm (x - z)
  simp only [PiLp.sub_apply] at hn
  calc |f x - f z| ≤ A * |x 0 - z 0| + A * |x 1 - z 1| := h
    _ = A * (|x 0 - z 0| + |x 1 - z 1|) := by ring
    _ ≤ A * (√2 * ‖x - z‖) := mul_le_mul_of_nonneg_left hn hA0
    _ = √2 * A * ‖x - z‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hd.le

end PDE.Analysis
