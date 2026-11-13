/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.DirectionalQuotient
public import PDE.Analysis.Calculus.CoordinatePaths

/-!
# Increments along the rectangular paths of a rectangle

Let `x`, `z` be two points of the plane and `f` a function differentiable on the closed rectangle
with corners `x` and `z`, with `|∂₀ f| ≤ A₀` and `|∂₁ f| ≤ A₁` there. The path `x → (z₀, x₁) → z`
stays in the rectangle, and the mean value inequality on its two legs
(`abs_sub_le_of_partialDeriv_le_coordinateLine`, from Mathlib's
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) gives
`|f(x) - f(z)| ≤ A₀ |x₀ - z₀| + A₁ |x₁ - z₁|`. With the weight `1` the term
`δ(f, p, q) |p_i - q_i|^α` of a leg from `p` to `q` is at most `|f(p) - f(q)|`, so the same bound
holds for the rectangular path estimate `δ_□(f, 1, x, z, x - z)` of Chen and Hou (5.41).

These give the increments of explicit coefficients that shrink with the distance of the two points,
which bounds on the two endpoint cells alone do not give.

## Main results

* `abs_sub_le_of_partialDeriv_le_rectangle`: `|f(x) - f(z)| ≤ A₀ |x₀ - z₀| + A₁ |x₁ - z₁|`.
* `boxBound_one_le_of_partialDeriv_le_rectangle`:
  `δ_□(f, 1, x, z, x - z) ≤ A₀ |x₀ - z₀| + A₁ |x₁ - z₁|`.
* `holderQuotient_le_of_abs_sub_le`: on a coordinate segment, a Lipschitz bound `A |pᵢ - qᵢ|`
  gives the Hölder quotient bound `A |pᵢ - qᵢ|^{1 - α}`.
* `mul_add_le_of_mul_sqrt_le`: a factor `G` with `G √aₗ ≤ Kₗ` times `D₀ a₀ + D₁ a₁` is at most
  `D₀ K₀ √a₀ + D₁ K₁ √a₁`, the form in which a singular gap weight `gⱼ(h)` multiplies an
  increment that shrinks with `|h|`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.4.1, (5.40)-(5.42).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open PDE (coordinateLine)
open Set

namespace HolderSpace

open PDE.Analysis

/-- The line through `x` in the direction `0` passes through `(s, x₁)` at the parameter `s`. -/
private theorem coordinateLine_zero (x : ℝ^2) (s : ℝ) :
    coordinateLine 0 x s = !₂[s, x 1] := by
  ext k; fin_cases k <;> simp [coordinateLine]

/-- The line through `x` in the direction `1` passes through `(x₀, s)` at the parameter `s`. -/
private theorem coordinateLine_one (x : ℝ^2) (s : ℝ) :
    coordinateLine 1 x s = !₂[x 0, s] := by
  ext k; fin_cases k <;> simp [coordinateLine]

/-- **Two legs in a rectangle**: if `f` is differentiable on the closed rectangle with corners
`x` and `z`, with `|∂₀ f| ≤ A₀` and `|∂₁ f| ≤ A₁` there, then
`|f(x) - f(z)| ≤ A₀ |x₀ - z₀| + A₁ |x₁ - z₁|`, along the path through `(z₀, x₁)`. The bound
`|f(x) - f(z₀, x₁)| + |f(z₀, x₁) - f(z)|` of the path itself is the first conclusion. -/
theorem abs_path_le_of_partialDeriv_le_rectangle {f : ℝ^2 → ℝ} {x z : ℝ^2} {A₀ A₁ : ℝ}
    (hf : ∀ y : ℝ^2, y 0 ∈ uIcc (x 0) (z 0) → y 1 ∈ uIcc (x 1) (z 1) → DifferentiableAt ℝ f y)
    (h₀ : ∀ y : ℝ^2, y 0 ∈ uIcc (x 0) (z 0) → y 1 ∈ uIcc (x 1) (z 1) →
      |(∂[(0 : Fin 2)] f) y| ≤ A₀)
    (h₁ : ∀ y : ℝ^2, y 0 ∈ uIcc (x 0) (z 0) → y 1 ∈ uIcc (x 1) (z 1) →
      |(∂[(1 : Fin 2)] f) y| ≤ A₁) :
    |f x - f !₂[z 0, x 1]| + |f !₂[z 0, x 1] - f z| ≤ A₀ * |x 0 - z 0| + A₁ * |x 1 - z 1| := by
  have e₀ := abs_sub_le_of_partialDeriv_le_coordinateLine (f := f) 0 x (s := x 0) (t := z 0)
    (fun u hu ↦ hf _ (by rw [coordinateLine_zero]; simpa using hu)
      (by rw [coordinateLine_zero]; simp))
    (fun u hu ↦ h₀ _ (by rw [coordinateLine_zero]; simpa using hu)
      (by rw [coordinateLine_zero]; simp))
  have e₁ := abs_sub_le_of_partialDeriv_le_coordinateLine (f := f) 1 !₂[z 0, x 1] (s := x 1)
    (t := z 1)
    (fun u hu ↦ hf _ (by rw [coordinateLine_one]; simp)
      (by rw [coordinateLine_one]; simpa using hu))
    (fun u hu ↦ h₁ _ (by rw [coordinateLine_one]; simp)
      (by rw [coordinateLine_one]; simpa using hu))
  rw [PDE.coordinateLine_self, coordinateLine_zero] at e₀
  rw [coordinateLine_one, coordinateLine_one] at e₁
  have hz : !₂[(!₂[z 0, x 1] : ℝ^2) 0, z 1] = z := by ext k; fin_cases k <;> simp
  have hw : !₂[(!₂[z 0, x 1] : ℝ^2) 0, x 1] = !₂[z 0, x 1] := by ext k; fin_cases k <;> simp
  rw [hz, hw] at e₁
  rw [abs_sub_comm (f x), abs_sub_comm (f !₂[z 0, x 1]) (f z), abs_sub_comm (x 0),
    abs_sub_comm (x 1)]
  exact add_le_add e₀ e₁

/-- **The increment in a rectangle**: under the hypotheses of
`abs_path_le_of_partialDeriv_le_rectangle`, `|f(x) - f(z)| ≤ A₀ |x₀ - z₀| + A₁ |x₁ - z₁|`. -/
theorem abs_sub_le_of_partialDeriv_le_rectangle {f : ℝ^2 → ℝ} {x z : ℝ^2} {A₀ A₁ : ℝ}
    (hf : ∀ y : ℝ^2, y 0 ∈ uIcc (x 0) (z 0) → y 1 ∈ uIcc (x 1) (z 1) → DifferentiableAt ℝ f y)
    (h₀ : ∀ y : ℝ^2, y 0 ∈ uIcc (x 0) (z 0) → y 1 ∈ uIcc (x 1) (z 1) →
      |(∂[(0 : Fin 2)] f) y| ≤ A₀)
    (h₁ : ∀ y : ℝ^2, y 0 ∈ uIcc (x 0) (z 0) → y 1 ∈ uIcc (x 1) (z 1) →
      |(∂[(1 : Fin 2)] f) y| ≤ A₁) :
    |f x - f z| ≤ A₀ * |x 0 - z 0| + A₁ * |x 1 - z 1| :=
  (abs_sub_le _ _ _).trans
    (abs_path_le_of_partialDeriv_le_rectangle hf h₀ h₁)

/-- A Hölder quotient times the `α`-th power of the coordinate distance of a leg is at most the
difference: `δ(f, p, q) |p_i - q_i|^α ≤ |f p - f q|` when `p` and `q` differ only in coordinate
`i`. -/
private theorem holderQuotient_mul_rpow_le {α : ℝ} {f : ℝ^2 → ℝ} {i : Fin 2} {p q : ℝ^2}
    (h : ∀ j ≠ i, p j = q j) : holderQuotient α f p q * |p i - q i| ^ α ≤ |f p - f q| := by
  rw [holderQuotient, dist_eq_dist_apply h, Real.dist_eq]
  rcases eq_or_ne (|p i - q i| ^ α) 0 with h0 | h0
  · rw [h0, mul_zero]; exact abs_nonneg _
  · rw [div_mul_cancel₀ _ h0]

/-- **The rectangular path estimate in a rectangle**: under the hypotheses of
`abs_path_le_of_partialDeriv_le_rectangle`, `δ_□(f, 1, x, z, x - z) ≤ A₀ |x₀ - z₀| +
A₁ |x₁ - z₁|` for every exponent `α`. -/
theorem boxBound_one_le_of_partialDeriv_le_rectangle {α : ℝ} {f : ℝ^2 → ℝ} {x z : ℝ^2}
    {A₀ A₁ : ℝ}
    (hf : ∀ y : ℝ^2, y 0 ∈ uIcc (x 0) (z 0) → y 1 ∈ uIcc (x 1) (z 1) → DifferentiableAt ℝ f y)
    (h₀ : ∀ y : ℝ^2, y 0 ∈ uIcc (x 0) (z 0) → y 1 ∈ uIcc (x 1) (z 1) →
      |(∂[(0 : Fin 2)] f) y| ≤ A₀)
    (h₁ : ∀ y : ℝ^2, y 0 ∈ uIcc (x 0) (z 0) → y 1 ∈ uIcc (x 1) (z 1) →
      |(∂[(1 : Fin 2)] f) y| ≤ A₁) :
    boxBound α f 1 x z (x - z) ≤ A₀ * |x 0 - z 0| + A₁ * |x 1 - z 1| := by
  refine (min_le_left _ _).trans (le_trans ?_ (abs_path_le_of_partialDeriv_le_rectangle hf h₀ h₁))
  simp only [productQuotient_one, PiLp.sub_apply]
  refine add_le_add ?_ ?_
  · have := holderQuotient_mul_rpow_le (α := α) (f := f) (i := 0) (p := x) (q := !₂[z 0, x 1])
      (by intro j hj; fin_cases j <;> simp_all)
    simpa using this
  · have := holderQuotient_mul_rpow_le (α := α) (f := f) (i := 1) (p := !₂[z 0, x 1]) (q := z)
      (by intro j hj; fin_cases j <;> simp_all)
    simpa using this

/-- **The Hölder quotient on a coordinate segment**: if `p` and `q` differ only in coordinate `i`
and `|f p - f q| ≤ A |pᵢ - qᵢ|` with `A ≥ 0`, then `δ(f, p, q) ≤ A |pᵢ - qᵢ|^{1 - α}`. -/
theorem holderQuotient_le_of_abs_sub_le {α : ℝ} {f : ℝ^2 → ℝ} {i : Fin 2} {p q : ℝ^2}
    (h : ∀ j ≠ i, p j = q j) {A : ℝ} (hA : 0 ≤ A) (hf : |f p - f q| ≤ A * |p i - q i|) :
    holderQuotient α f p q ≤ A * |p i - q i| ^ (1 - α) := by
  rw [holderQuotient, dist_eq_dist_apply h, Real.dist_eq]
  rcases eq_or_lt_of_le (abs_nonneg (p i - q i)) with h0 | hpos
  · rw [← h0] at hf ⊢
    have : |f p - f q| = 0 := le_antisymm (by simpa using hf) (abs_nonneg _)
    rw [this, zero_div]
    exact mul_nonneg hA (Real.rpow_nonneg le_rfl _)
  · rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _), mul_assoc, ← Real.rpow_add hpos,
      sub_add_cancel, Real.rpow_one]
    exact hf

/-- **A weight against an increment that shrinks with the distance**: for `Dₗ ≥ 0`, `aₗ ≥ 0`
and `G √aₗ ≤ Kₗ`, `G (D₀ a₀ + D₁ a₁) ≤ D₀ K₀ √a₀ + D₁ K₁ √a₁`. -/
theorem mul_add_le_of_mul_sqrt_le {G D₀ D₁ a₀ a₁ K₀ K₁ : ℝ} (hD₀ : 0 ≤ D₀)
    (hD₁ : 0 ≤ D₁) (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hK₀ : G * √a₀ ≤ K₀) (hK₁ : G * √a₁ ≤ K₁) :
    G * (D₀ * a₀ + D₁ * a₁) ≤ D₀ * K₀ * √a₀ + D₁ * K₁ * √a₁ := by
  have s₀ := Real.sqrt_nonneg a₀
  have s₁ := Real.sqrt_nonneg a₁
  have e : D₀ * (G * √a₀) * √a₀ + D₁ * (G * √a₁) * √a₁ =
      G * (D₀ * (√a₀ * √a₀) + D₁ * (√a₁ * √a₁)) := by ring
  calc G * (D₀ * a₀ + D₁ * a₁) = D₀ * (G * √a₀) * √a₀ + D₁ * (G * √a₁) * √a₁ := by
        rw [e, Real.mul_self_sqrt ha₀, Real.mul_self_sqrt ha₁]
    _ ≤ D₀ * K₀ * √a₀ + D₁ * K₁ * √a₁ := by gcongr

end HolderSpace
