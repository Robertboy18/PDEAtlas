/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import PDE.Analysis.Calculus.EvenTaylor

/-!
# Symmetrized values of holomorphic functions on a rectangle

Let `F` be holomorphic near the closed rectangle `Q_x = [-x₁, x₁] × [-x₂, x₂]` of the complex
plane, `x = x₁ + i x₂` with `x₁, x₂ ≥ 0`. The four reflections `±x, ±x̄` of `x` give the even
combination `S = F(x) + F(-x) + F(x̄) + F(-x̄)` and the odd combination
`D = F(x) + F(-x) - F(x̄) - F(-x̄)`. Taylor expansion along the segments `[-x, x]`, `[-x̄, x̄]`
and along horizontal and vertical lines in `Q_x` bounds them by the second and fourth complex
derivatives on `Q_x`, through constants `M₂ ≥ ‖F''‖` and `M₄ ≥ ‖F⁽⁴⁾‖` on `Q_x`.

The real and imaginary parts of `F` are the harmonic functions of Lemma B.2 of Chen and Hou,
where `G₁ = Re S - 4 Re F(0)` and `G₂ = Re D`; the statements here are that lemma in holomorphic
form, with the bounds `M₂ ≥ ‖F''‖` and `M₄ ≥ ‖F⁽⁴⁾‖`.

The fourth-order bound for `S` is `|x|⁴ M₄ / 6`, with the remainder taken along the two diagonals
of `Q_x`; (B.4) has `(x₁⁴ + 6 x₁² x₂² + x₂⁴) / 6` in place of `|x|⁴ / 6`.

Derivatives are explicit functions: `F₁, …, F₄` with `HasDerivAt Fₖ (Fₖ₊₁ z) z` on `Q_x`.

## Main results

* `norm_add_neg_add_conj_add_neg_conj_sub_le`: `‖S - 4 F(0)‖ ≤ 2 |x|² M₂`.
* `norm_add_neg_add_conj_add_neg_conj_sub_sub_le`:
  `‖S - 4 F(0) - 2 (x₁² - x₂²) F''(0)‖ ≤ |x|⁴ M₄ / 6`.
* `norm_sub_neg_add_conj_sub_neg_conj_le`: `‖F'(x) - F'(-x) + F'(x̄) - F'(-x̄)‖ ≤ 4 x₁ M₂`, the
  bound for the `x₁`-derivative of `S`.
* `norm_sub_neg_sub_conj_add_neg_conj_le`: `‖F'(x) - F'(-x) - F'(x̄) + F'(-x̄)‖ ≤ 4 x₂ M₂`, the
  bound for the `x₂`-derivative of `S` divided by `i`.
* `norm_sub_neg_add_conj_sub_neg_conj_sub_le`:
  `‖F'(x) - F'(-x) + F'(x̄) - F'(-x̄) - 4 x₁ F''(0)‖ ≤ (2 x₁³ / 3 + 2 x₁ x₂²) M₄`.
* `norm_add_neg_sub_conj_sub_neg_conj_le`: `‖D‖ ≤ 4 x₁ x₂ M₂`.
* `norm_add_neg_sub_conj_sub_neg_conj_sub_le`: `‖D - 4 i x₁ x₂ F''(0)‖ ≤ (2/3) x₁ x₂ |x|² M₄`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix B.1,
  Lemma B.2, (B.2)-(B.8). <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Set Complex
open scoped ComplexConjugate

namespace PDE.Analysis

variable {F F₁ F₂ F₃ F₄ : ℂ → ℂ} {x : ℂ} {M₂ M₄ : ℝ}

/-- The derivative of a holomorphic function along a real affine line `s ↦ c + s v`. -/
theorem hasDerivAt_comp_affineLine {G G' : ℂ → ℂ} (c v : ℂ) {t : ℝ}
    (h : HasDerivAt G (G' (c + t * v)) (c + t * v)) :
    HasDerivAt (fun s : ℝ ↦ G (c + s * v)) (G' (c + t * v) * v) t := by
  have hl : HasDerivAt (fun w : ℂ ↦ c + w * v) v (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const v).const_add c
  exact (h.comp (t : ℂ) hl).comp_ofReal

/-- Points `t x` and `t x̄` with `t ∈ [-1, 1]` lie in the rectangle `Q_x`. -/
theorem smul_mem_rectangle {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hx₁ : 0 ≤ x.re) (hx₂ : 0 ≤ x.im)
    {w : ℂ} (hw : w = x ∨ w = conj x) :
    (t : ℂ) * w ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im := by
  have hab : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have hre : |t * x.re| ≤ x.re := by
    rw [abs_mul, abs_of_nonneg hx₁]; exact mul_le_of_le_one_left hx₁ hab
  have him : |t * x.im| ≤ x.im := by
    rw [abs_mul, abs_of_nonneg hx₂]; exact mul_le_of_le_one_left hx₂ hab
  rcases hw with hw | hw <;> rw [hw]
  · have hr : ((t : ℂ) * x).re = t * x.re := by simp
    have hi : ((t : ℂ) * x).im = t * x.im := by simp
    rw [mem_reProdIm, hr, hi]
    exact ⟨abs_le.mp hre, abs_le.mp him⟩
  · have hr : ((t : ℂ) * conj x).re = t * x.re := by simp
    have hi : ((t : ℂ) * conj x).im = -(t * x.im) := by simp
    rw [mem_reProdIm, hr, hi]
    exact ⟨abs_le.mp hre, ⟨by linarith [(abs_le.mp him).2], by linarith [(abs_le.mp him).1]⟩⟩

/-- Differentiating `G` along the diagonal `t ↦ t w`, `t ∈ [-1, 1]`, inside `R`. -/
private theorem hasDerivAt_comp_mul_of_mem {w : ℂ} {R : Set ℂ}
    (hmem : ∀ t ∈ Icc (-1 : ℝ) 1, (t : ℂ) * w ∈ R) {H H' : ℂ → ℂ}
    (hH : ∀ z ∈ R, HasDerivAt H (H' z) z) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (fun s : ℝ ↦ H (s * w)) (H' (t * w) * w) t := by
  simpa using hasDerivAt_comp_affineLine (G := H) (G' := H') 0 w (t := t)
    (by simpa using hH _ (hmem t ht))

/-- Restriction of the even second-order bound to one diagonal `[-w, w]` of the rectangle. -/
private theorem norm_diagonal_sub_le {w : ℂ} {M : ℝ} {G G₁ G₂ : ℂ → ℂ} {R : Set ℂ}
    (hmem : ∀ t ∈ Icc (-1 : ℝ) 1, (t : ℂ) * w ∈ R)
    (hG : ∀ z ∈ R, HasDerivAt G (G₁ z) z) (hG₁ : ∀ z ∈ R, HasDerivAt G₁ (G₂ z) z)
    (hM : ∀ z ∈ R, ‖G₂ z‖ ≤ M) :
    ‖G w + G (-w) - 2 * G 0‖ ≤ ‖w‖ ^ 2 * M := by
  have h := PDE.Analysis.Calculus.norm_add_neg_sub_two_smul_le (E := ℂ) (x := 1) (M := ‖w‖ ^ 2 * M)
    zero_le_one (f := fun s : ℝ ↦ G (s * w)) (f₁ := fun s : ℝ ↦ G₁ (s * w) * w)
    (f₂ := fun s : ℝ ↦ G₂ (s * w) * w * w)
    (by simpa using fun t ↦ hasDerivAt_comp_mul_of_mem hmem hG (t := t))
    (fun t ht ↦ by
      simpa using (hasDerivAt_comp_mul_of_mem hmem hG₁ (by simpa using ht)).mul_const w)
    (fun t ht ↦ by
      rw [norm_mul, norm_mul, mul_assoc, ← sq, mul_comm]
      exact mul_le_mul_of_nonneg_left (hM _ (hmem t (by simpa using ht))) (by positivity))
  simpa [two_smul, two_mul] using h

/-- Fourth-order version of `norm_diagonal_sub_le`. -/
private theorem norm_diagonal_sub_sub_le {w : ℂ} {M : ℝ} {G G₁ G₂ G₃ G₄ : ℂ → ℂ} {R : Set ℂ}
    (hmem : ∀ t ∈ Icc (-1 : ℝ) 1, (t : ℂ) * w ∈ R)
    (hG : ∀ z ∈ R, HasDerivAt G (G₁ z) z) (hG₁ : ∀ z ∈ R, HasDerivAt G₁ (G₂ z) z)
    (hG₂ : ∀ z ∈ R, HasDerivAt G₂ (G₃ z) z) (hG₃ : ∀ z ∈ R, HasDerivAt G₃ (G₄ z) z)
    (hM : ∀ z ∈ R, ‖G₄ z‖ ≤ M) :
    ‖G w + G (-w) - 2 * G 0 - w ^ 2 * G₂ 0‖ ≤ ‖w‖ ^ 4 / 12 * M := by
  have h := PDE.Analysis.Calculus.norm_add_neg_sub_two_smul_sub_sq_smul_le (E := ℂ) (x := 1)
    (M := ‖w‖ ^ 4 * M) zero_le_one (f := fun s : ℝ ↦ G (s * w))
    (f₁ := fun s : ℝ ↦ w * G₁ (s * w)) (f₂ := fun s : ℝ ↦ w ^ 2 * G₂ (s * w))
    (f₃ := fun s : ℝ ↦ w ^ 3 * G₃ (s * w)) (f₄ := fun s : ℝ ↦ w ^ 4 * G₄ (s * w))
    (fun t ht ↦ (hasDerivAt_comp_mul_of_mem hmem hG (by simpa using ht)).congr_deriv (by ring))
    (fun t ht ↦ ((hasDerivAt_comp_mul_of_mem hmem hG₁ (by simpa using ht)).const_mul
      w).congr_deriv (by ring))
    (fun t ht ↦ ((hasDerivAt_comp_mul_of_mem hmem hG₂ (by simpa using ht)).const_mul
      (w ^ 2)).congr_deriv (by ring))
    (fun t ht ↦ ((hasDerivAt_comp_mul_of_mem hmem hG₃ (by simpa using ht)).const_mul
      (w ^ 3)).congr_deriv (by ring))
    (fun t ht ↦ by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hM _ (hmem t (by simpa using ht))) (by positivity))
  refine (?_ : _ ≤ 1 ^ 4 / 12 * (‖w‖ ^ 4 * M)).trans_eq (by ring)
  simpa [two_smul, two_mul] using h

variable (hx₁ : 0 ≤ x.re) (hx₂ : 0 ≤ x.im)
include hx₁ hx₂

/-- **Even symmetrization, second order** (Chen–Hou II, Lemma B.2, first estimate of (B.3),
holomorphic form): `‖F(x) + F(-x) + F(x̄) + F(-x̄) - 4F(0)‖ ≤ 2|x|² M₂`. -/
theorem norm_add_neg_add_conj_add_neg_conj_sub_le
    (hF : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F (F₁ z) z)
    (hF₁ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₁ (F₂ z) z)
    (hM₂ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, ‖F₂ z‖ ≤ M₂) :
    ‖F x + F (-x) + F (conj x) + F (-conj x) - 4 * F 0‖ ≤ 2 * ‖x‖ ^ 2 * M₂ := by
  have h₁ := norm_diagonal_sub_le (w := x)
    (fun t ht ↦ smul_mem_rectangle ht hx₁ hx₂ (Or.inl rfl)) hF hF₁ hM₂
  have h₂ := norm_diagonal_sub_le (w := conj x)
    (fun t ht ↦ smul_mem_rectangle ht hx₁ hx₂ (Or.inr rfl)) hF hF₁ hM₂
  rw [Complex.norm_conj] at h₂
  calc _ = ‖(F x + F (-x) - 2 * F 0) + (F (conj x) + F (-conj x) - 2 * F 0)‖ := by
        congr 1; ring
    _ ≤ ‖F x + F (-x) - 2 * F 0‖ + ‖F (conj x) + F (-conj x) - 2 * F 0‖ := norm_add_le _ _
    _ ≤ ‖x‖ ^ 2 * M₂ + ‖x‖ ^ 2 * M₂ := add_le_add h₁ h₂
    _ = 2 * ‖x‖ ^ 2 * M₂ := by ring

/-- **Even symmetrization, fourth order** (Chen–Hou II, Lemma B.2, (B.4), holomorphic form):
`‖F(x) + F(-x) + F(x̄) + F(-x̄) - 4F(0) - 2(x₁² - x₂²)F''(0)‖ ≤ |x|⁴ M₄ / 6`. -/
theorem norm_add_neg_add_conj_add_neg_conj_sub_sub_le
    (hF : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F (F₁ z) z)
    (hF₁ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₁ (F₂ z) z)
    (hF₂ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₂ (F₃ z) z)
    (hF₃ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₃ (F₄ z) z)
    (hM₄ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, ‖F₄ z‖ ≤ M₄) :
    ‖F x + F (-x) + F (conj x) + F (-conj x) - 4 * F 0 -
        2 * ((x.re ^ 2 - x.im ^ 2 : ℝ) : ℂ) * F₂ 0‖ ≤ ‖x‖ ^ 4 / 6 * M₄ := by
  have h₁ := norm_diagonal_sub_sub_le (w := x)
    (fun t ht ↦ smul_mem_rectangle ht hx₁ hx₂ (Or.inl rfl)) hF hF₁ hF₂ hF₃ hM₄
  have h₂ := norm_diagonal_sub_sub_le (w := conj x)
    (fun t ht ↦ smul_mem_rectangle ht hx₁ hx₂ (Or.inr rfl)) hF hF₁ hF₂ hF₃ hM₄
  rw [Complex.norm_conj] at h₂
  have hsq : x ^ 2 + conj x ^ 2 = 2 * ((x.re ^ 2 - x.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [sq] <;> ring
  calc _ = ‖(F x + F (-x) - 2 * F 0 - x ^ 2 * F₂ 0) +
        (F (conj x) + F (-conj x) - 2 * F 0 - conj x ^ 2 * F₂ 0)‖ := by
        rw [← hsq]; congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ ‖x‖ ^ 4 / 12 * M₄ + ‖x‖ ^ 4 / 12 * M₄ := add_le_add h₁ h₂
    _ = ‖x‖ ^ 4 / 6 * M₄ := by ring

omit hx₁ hx₂ in
/-- A horizontal difference `F₁(s + i y) - F₁(-s + i y)` for `|y| ≤ x₂`, `0 ≤ s ≤ x₁`. -/
private theorem norm_horizontal_sub_le {G G' : ℂ → ℂ} {M : ℝ} {s y : ℝ} (hs : 0 ≤ s)
    (hsx : s ≤ x.re) (hy : |y| ≤ x.im)
    (hG : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt G (G' z) z)
    (hM : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, ‖G' z‖ ≤ M) :
    ‖G (s + y * I) - G (-s + y * I)‖ ≤ 2 * s * M := by
  have hmem : ∀ t ∈ Icc (-s) s, ((y : ℂ) * I + t * 1) ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im := by
    intro t ht
    have hr : ((y : ℂ) * I + t * 1).re = t := by simp
    have hi : ((y : ℂ) * I + t * 1).im = y := by simp
    rw [mem_reProdIm, hr, hi]
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, abs_le.mp hy⟩
  have hd : ∀ t ∈ Icc (-s) s, HasDerivWithinAt (fun r : ℝ ↦ G ((y : ℂ) * I + r * 1))
      (G' ((y : ℂ) * I + t * 1) * 1) (Icc (-s) s) t :=
    fun t ht ↦ (hasDerivAt_comp_affineLine (G := G) (G' := G') _ 1 (hG _ (hmem t ht)))
      |>.hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd (C := M)
    (fun t ht ↦ by simpa using hM _ (hmem t (Ico_subset_Icc_self ht))) s
    (right_mem_Icc.mpr (by linarith))
  have e1 : (y : ℂ) * I + (s : ℝ) * 1 = s + y * I := by ring
  have e2 : (y : ℂ) * I + ((-s : ℝ) : ℂ) * 1 = -s + y * I := by push_cast; ring
  rw [e1, e2] at h
  calc _ ≤ M * (s - -s) := h
    _ = 2 * s * M := by ring

omit hx₁ hx₂ in
/-- A vertical difference `F₁(r + i y) - F₁(r - i y)` for `|r| ≤ x₁`, `0 ≤ y ≤ x₂`. -/
private theorem norm_vertical_sub_le {G G' : ℂ → ℂ} {M : ℝ} {r y : ℝ} (hy : 0 ≤ y)
    (hyx : y ≤ x.im) (hr : |r| ≤ x.re)
    (hG : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt G (G' z) z)
    (hM : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, ‖G' z‖ ≤ M) :
    ‖G (r + y * I) - G (r - y * I)‖ ≤ 2 * y * M := by
  have hmem : ∀ t ∈ Icc (-y) y, ((r : ℂ) + t * I) ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im := by
    intro t ht
    have hr' : ((r : ℂ) + t * I).re = r := by simp
    have hi : ((r : ℂ) + t * I).im = t := by simp
    rw [mem_reProdIm, hr', hi]
    exact ⟨abs_le.mp hr, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hd : ∀ t ∈ Icc (-y) y, HasDerivWithinAt (fun s : ℝ ↦ G ((r : ℂ) + s * I))
      (G' ((r : ℂ) + t * I) * I) (Icc (-y) y) t :=
    fun t ht ↦ (hasDerivAt_comp_affineLine (G := G) (G' := G') _ I (hG _ (hmem t ht)))
      |>.hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd (C := M)
    (fun t ht ↦ by simpa using hM _ (hmem t (Ico_subset_Icc_self ht))) y
    (right_mem_Icc.mpr (by linarith))
  have e2 : (r : ℂ) + ((-y : ℝ) : ℂ) * I = r - y * I := by push_cast; ring
  rw [e2] at h
  calc _ ≤ M * (y - -y) := h
    _ = 2 * y * M := by ring

/-- **The `x₁`-derivative of the even symmetrization** (Chen–Hou II, Lemma B.2, second estimate
of (B.3), holomorphic form): `‖F'(x) - F'(-x) + F'(x̄) - F'(-x̄)‖ ≤ 4 x₁ M₂`. -/
theorem norm_sub_neg_add_conj_sub_neg_conj_le
    (hF₁ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₁ (F₂ z) z)
    (hM₂ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, ‖F₂ z‖ ≤ M₂) :
    ‖F₁ x - F₁ (-x) + F₁ (conj x) - F₁ (-conj x)‖ ≤ 4 * x.re * M₂ := by
  have h₁ := norm_horizontal_sub_le (x := x) (s := x.re) (y := x.im) hx₁ le_rfl
    (by rw [abs_of_nonneg hx₂]) hF₁ hM₂
  have h₂ := norm_horizontal_sub_le (x := x) (s := x.re) (y := -x.im) hx₁ le_rfl
    (by rw [abs_neg, abs_of_nonneg hx₂]) hF₁ hM₂
  have e₁ : (x.re : ℂ) + x.im * I = x := (re_add_im x)
  have e₂ : -(x.re : ℂ) + x.im * I = -conj x := by
    apply Complex.ext <;> simp
  have e₃ : (x.re : ℂ) + ((-x.im : ℝ) : ℂ) * I = conj x := by
    apply Complex.ext <;> simp
  have e₄ : -(x.re : ℂ) + ((-x.im : ℝ) : ℂ) * I = -x := by
    apply Complex.ext <;> simp
  rw [e₁, e₂] at h₁
  rw [e₃, e₄] at h₂
  calc _ = ‖(F₁ x - F₁ (-conj x)) + (F₁ (conj x) - F₁ (-x))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ 2 * x.re * M₂ + 2 * x.re * M₂ := add_le_add h₁ h₂
    _ = 4 * x.re * M₂ := by ring

/-- **The `x₂`-derivative of the even symmetrization** (Chen–Hou II, Lemma B.2, second estimate
of (B.3), holomorphic form): `‖F'(x) - F'(-x) - F'(x̄) + F'(-x̄)‖ ≤ 4 x₂ M₂`. -/
theorem norm_sub_neg_sub_conj_add_neg_conj_le
    (hF₁ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₁ (F₂ z) z)
    (hM₂ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, ‖F₂ z‖ ≤ M₂) :
    ‖F₁ x - F₁ (-x) - F₁ (conj x) + F₁ (-conj x)‖ ≤ 4 * x.im * M₂ := by
  have h₁ := norm_vertical_sub_le (x := x) (r := x.re) (y := x.im) hx₂ le_rfl
    (by rw [abs_of_nonneg hx₁]) hF₁ hM₂
  have h₂ := norm_vertical_sub_le (x := x) (r := -x.re) (y := x.im) hx₂ le_rfl
    (by rw [abs_neg, abs_of_nonneg hx₁]) hF₁ hM₂
  have e₁ : (x.re : ℂ) + x.im * I = x := (re_add_im x)
  have e₂ : (x.re : ℂ) - x.im * I = conj x := by
    apply Complex.ext <;> simp
  have e₃ : ((-x.re : ℝ) : ℂ) + x.im * I = -conj x := by
    apply Complex.ext <;> simp
  have e₄ : ((-x.re : ℝ) : ℂ) - x.im * I = -x := by
    apply Complex.ext <;> simp
  rw [e₁, e₂] at h₁
  rw [e₃, e₄] at h₂
  calc _ = ‖(F₁ x - F₁ (conj x)) + (F₁ (-conj x) - F₁ (-x))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ 2 * x.im * M₂ + 2 * x.im * M₂ := add_le_add h₁ h₂
    _ = 4 * x.im * M₂ := by ring

omit hx₁ hx₂ in
/-- A rectangle `Q_w` with `0 ≤ w ≤ x` coordinatewise lies in `Q_x`. -/
theorem reProdIm_subset_reProdIm {w : ℂ} (hw₁ : w.re ≤ x.re) (hw₂ : w.im ≤ x.im) :
    Icc (-w.re) w.re ×ℂ Icc (-w.im) w.im ⊆ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im := by
  intro z hz
  simp only [mem_reProdIm, mem_Icc] at hz ⊢
  exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ⟨by linarith [hz.2.1], by
    linarith [hz.2.2]⟩⟩

omit hx₁ hx₂ in
/-- Membership in a centred closed rectangle through absolute values. -/
theorem mem_reProdIm_Icc_neg_iff {a b : ℝ} {z : ℂ} :
    z ∈ Icc (-a) a ×ℂ Icc (-b) b ↔ |z.re| ≤ a ∧ |z.im| ≤ b := by
  rw [mem_reProdIm, mem_Icc, mem_Icc, abs_le, abs_le]

omit hx₁ hx₂ in
/-- The real and imaginary parts of `a + b i` are `a` and `b`. -/
private theorem re_add_im_mul_I (a b : ℝ) : ((a : ℂ) + b * I).re = a ∧ ((a : ℂ) + b * I).im = b :=
  ⟨by simp, by simp⟩

/-- **The `x₁`-derivative of the even symmetrization, fourth order** (Chen–Hou II, Lemma B.2,
first estimate of (B.6), holomorphic form):
`‖F'(x) - F'(-x) + F'(x̄) - F'(-x̄) - 4 x₁ F''(0)‖ ≤ (2x₁³/3 + 2 x₁ x₂²) M₄`. -/
theorem norm_sub_neg_add_conj_sub_neg_conj_sub_le
    (hF₁ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₁ (F₂ z) z)
    (hF₂ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₂ (F₃ z) z)
    (hF₃ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₃ (F₄ z) z)
    (hM₄ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, ‖F₄ z‖ ≤ M₄) :
    ‖F₁ x - F₁ (-x) + F₁ (conj x) - F₁ (-conj x) - 4 * x.re * F₂ 0‖ ≤
      (2 / 3 * x.re ^ 3 + 2 * x.re * x.im ^ 2) * M₄ := by
  set R := Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im
  let cp : ℂ := x.im * I
  let cm : ℂ := -(x.im * I)
  let Ψ : ℝ → ℂ := fun s ↦ F₁ (cp + s * 1) - F₁ (cp + s * (-1)) + F₁ (cm + s * 1) -
    F₁ (cm + s * (-1)) - 4 * s * F₂ 0
  have hmemR {s : ℝ} (hs : s ∈ Icc 0 x.re) {v c : ℂ} (hc : c = cp ∨ c = cm)
      (hv : v = 1 ∨ v = -1) : c + s * v ∈ R := by
    have hs' : |s| ≤ x.re := by rw [abs_of_nonneg hs.1]; exact hs.2
    have hy : |x.im| ≤ x.im := (abs_of_nonneg hx₂).le
    rw [mem_reProdIm_Icc_neg_iff]
    rcases hc with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [cp, cm, hs', hy]
  -- the four horizontal segments through `w = s + i x₂` and its reflections
  have he (s : ℝ) : cp + (s : ℂ) * 1 = (s : ℂ) + x.im * I ∧
      cp + (s : ℂ) * (-1) = -conj ((s : ℂ) + x.im * I) ∧
      cm + (s : ℂ) * 1 = conj ((s : ℂ) + x.im * I) ∧
      cm + (s : ℂ) * (-1) = -((s : ℂ) + x.im * I) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Complex.ext <;> simp [cp, cm]
  have hderiv (s : ℝ) (hs : s ∈ Icc 0 x.re) :
      HasDerivAt Ψ (F₂ ((s : ℂ) + x.im * I) + F₂ (-((s : ℂ) + x.im * I)) +
        F₂ (conj ((s : ℂ) + x.im * I)) + F₂ (-conj ((s : ℂ) + x.im * I)) - 4 * F₂ 0) s := by
    have hd {c v : ℂ} (hc : c = cp ∨ c = cm) (hv : v = 1 ∨ v = -1) :=
      hasDerivAt_comp_affineLine (G := F₁) (G' := F₂) c v (hF₁ _ (hmemR hs hc hv))
    have h5 : HasDerivAt (fun r : ℝ ↦ 4 * (r : ℂ) * F₂ 0) (4 * F₂ 0) s := by
      simpa using (((hasDerivAt_id (s : ℂ)).const_mul (4 : ℂ)).mul_const (F₂ 0)).comp_ofReal
    refine (((((hd (.inl rfl) (.inl rfl)).sub (hd (.inl rfl) (.inr rfl))).add
      (hd (.inr rfl) (.inl rfl))).sub (hd (.inr rfl) (.inr rfl))).sub h5).congr_deriv ?_
    obtain ⟨e1, e2, e3, e4⟩ := he s
    rw [e1, e2, e3, e4]
    ring
  have hbound (s : ℝ) (hs : s ∈ Icc 0 x.re) :
      ‖F₂ ((s : ℂ) + x.im * I) + F₂ (-((s : ℂ) + x.im * I)) + F₂ (conj ((s : ℂ) + x.im * I)) +
        F₂ (-conj ((s : ℂ) + x.im * I)) - 4 * F₂ 0‖ ≤ (2 * s ^ 2 + 2 * x.im ^ 2) * M₄ := by
    obtain ⟨hr, hi⟩ := re_add_im_mul_I s x.im
    have hsub : Icc (-((s : ℂ) + x.im * I).re) ((s : ℂ) + x.im * I).re ×ℂ
        Icc (-((s : ℂ) + x.im * I).im) ((s : ℂ) + x.im * I).im ⊆ R :=
      reProdIm_subset_reProdIm (by rw [hr]; exact hs.2) (by rw [hi])
    have h := norm_add_neg_add_conj_add_neg_conj_sub_le (F := F₂) (F₁ := F₃) (F₂ := F₄)
      (x := (s : ℂ) + x.im * I) (M₂ := M₄) (by rw [hr]; exact hs.1) (by rw [hi]; exact hx₂)
      (fun z hz ↦ hF₂ z (hsub hz)) (fun z hz ↦ hF₃ z (hsub hz)) (fun z hz ↦ hM₄ z (hsub hz))
    have hn : ‖(s : ℂ) + x.im * I‖ ^ 2 = s ^ 2 + x.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hr, hi]; ring
    rw [hn] at h
    linarith
  have hB (s : ℝ) : HasDerivAt (fun r : ℝ ↦ (2 / 3 * r ^ 3 + 2 * r * x.im ^ 2) * M₄)
      ((2 * s ^ 2 + 2 * x.im ^ 2) * M₄) s :=
    ((((hasDerivAt_pow 3 s).const_mul _).add (((hasDerivAt_id' s).const_mul _).mul_const
      _)).mul_const M₄).congr_deriv (by ring)
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := Ψ)
    (fun s hs ↦ (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hderiv s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (by simp [Ψ]) hB
    (fun s hs ↦ hbound s (Ico_subset_Icc_self hs)) (right_mem_Icc.mpr hx₁)
  obtain ⟨e1, e2, e3, e4⟩ := he x.re
  simp only [Ψ, e1, e2, e3, e4, re_add_im] at h
  calc _ = ‖F₁ x - F₁ (-conj x) + F₁ (conj x) - F₁ (-x) - 4 * x.re * F₂ 0‖ := by
        congr 1; ring
    _ ≤ _ := h

omit hx₂ in
/-- For `t ∈ [0, x₂]`, the point `w = x₁ + i t` lies in the closed quadrant and `Q_w ⊆ Q_x`. -/
private theorem vertical_point_facts {t : ℝ} (ht : t ∈ Icc 0 x.im) :
    0 ≤ ((x.re : ℂ) + t * I).re ∧ 0 ≤ ((x.re : ℂ) + t * I).im ∧
      Icc (-((x.re : ℂ) + t * I).re) ((x.re : ℂ) + t * I).re ×ℂ
        Icc (-((x.re : ℂ) + t * I).im) ((x.re : ℂ) + t * I).im ⊆
          Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im := by
  obtain ⟨hr, hi⟩ := re_add_im_mul_I x.re t
  refine ⟨by rw [hr]; exact hx₁, by rw [hi]; exact ht.1, ?_⟩
  apply reProdIm_subset_reProdIm <;> simp [hr, hi, ht.2]

omit hx₂ in
/-- The derivative of the odd combination `F(w) + F(-w) - F(w̄) - F(-w̄)` along the vertical
segment `w = x₁ + i t`, `t ∈ [0, x₂]`. -/
private theorem hasDerivAt_vertical_combination
    (hF : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F (F₁ z) z)
    {t : ℝ} (ht : t ∈ Icc 0 x.im) :
    HasDerivAt (fun t : ℝ ↦ F (x.re + t * I) + F (-x.re + t * (-I)) - F (x.re + t * (-I)) -
        F (-x.re + t * I))
      (I * (F₁ ((x.re : ℂ) + t * I) - F₁ (-((x.re : ℂ) + t * I)) +
        F₁ (conj ((x.re : ℂ) + t * I)) - F₁ (-conj ((x.re : ℂ) + t * I)))) t := by
  have hmem {c v : ℂ} (hc : c = x.re ∨ c = -x.re) (hv : v = I ∨ v = -I) :
      c + t * v ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im := by
    have ht' : |t| ≤ x.im := by rw [abs_of_nonneg ht.1]; exact ht.2
    have hr : |x.re| ≤ x.re := (abs_of_nonneg hx₁).le
    rw [mem_reProdIm_Icc_neg_iff]
    rcases hc with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [ht', hr]
  have hd {c v : ℂ} (hc : c = x.re ∨ c = -x.re) (hv : v = I ∨ v = -I) :=
    hasDerivAt_comp_affineLine (G := F) (G' := F₁) c v (hF _ (hmem hc hv))
  refine ((((hd (.inl rfl) (.inl rfl)).add (hd (.inr rfl) (.inr rfl))).sub
    (hd (.inl rfl) (.inr rfl))).sub (hd (.inr rfl) (.inl rfl))).congr_deriv ?_
  have e2 : -(x.re : ℂ) + t * (-I) = -((x.re : ℂ) + t * I) := by ring
  have e3 : (x.re : ℂ) + t * (-I) = conj ((x.re : ℂ) + t * I) := by
    apply Complex.ext <;> simp
  have e4 : -(x.re : ℂ) + t * I = -conj ((x.re : ℂ) + t * I) := by
    apply Complex.ext <;> simp
  rw [e2, e3, e4]
  ring

omit hx₁ hx₂ in
/-- The ends `t = x₂` of the four vertical segments. -/
private theorem vertical_endpoints :
    (x.re : ℂ) + (x.im : ℂ) * I = x ∧ -(x.re : ℂ) + (x.im : ℂ) * (-I) = -x ∧
      (x.re : ℂ) + (x.im : ℂ) * (-I) = conj x ∧ -(x.re : ℂ) + (x.im : ℂ) * I = -conj x := by
  refine ⟨re_add_im x, ?_, ?_, ?_⟩ <;> apply Complex.ext <;> simp

/-- **Odd symmetrization, second order** (Chen–Hou II, Lemma B.2, first estimate of (B.7),
holomorphic form): `‖F(x) + F(-x) - F(x̄) - F(-x̄)‖ ≤ 4 x₁ x₂ M₂`. -/
theorem norm_add_neg_sub_conj_sub_neg_conj_le
    (hF : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F (F₁ z) z)
    (hF₁ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₁ (F₂ z) z)
    (hM₂ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, ‖F₂ z‖ ≤ M₂) :
    ‖F x + F (-x) - F (conj x) - F (-conj x)‖ ≤ 4 * x.re * x.im * M₂ := by
  have h := PDE.Analysis.Calculus.norm_le_of_norm_deriv_le_pow (c := 4 * x.re * M₂) 0 hx₂
    (by simp) (fun t ht ↦ hasDerivAt_vertical_combination hx₁ hF ht) fun t ht ↦ by
      obtain ⟨h0, h0', hsub⟩ := vertical_point_facts hx₁ ht
      have h := norm_sub_neg_add_conj_sub_neg_conj_le (F₁ := F₁) (F₂ := F₂) (M₂ := M₂) h0 h0'
        (fun z hz ↦ hF₁ z (hsub hz)) (fun z hz ↦ hM₂ z (hsub hz))
      rw [norm_mul, Complex.norm_I, one_mul, pow_zero, mul_one]
      simpa only [(re_add_im_mul_I x.re t).1] using h
  obtain ⟨e1, e2, e3, e4⟩ := vertical_endpoints (x := x)
  simp only [e1, e2, e3, e4] at h
  exact h.trans_eq (by push_cast; ring)

/-- **Odd symmetrization, fourth order** (Chen–Hou II, Lemma B.2, (B.8), holomorphic form):
`‖F(x) + F(-x) - F(x̄) - F(-x̄) - 4 i x₁ x₂ F''(0)‖ ≤ (2/3) x₁ x₂ |x|² M₄`. -/
theorem norm_add_neg_sub_conj_sub_neg_conj_sub_le
    (hF : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F (F₁ z) z)
    (hF₁ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₁ (F₂ z) z)
    (hF₂ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₂ (F₃ z) z)
    (hF₃ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, HasDerivAt F₃ (F₄ z) z)
    (hM₄ : ∀ z ∈ Icc (-x.re) x.re ×ℂ Icc (-x.im) x.im, ‖F₄ z‖ ≤ M₄) :
    ‖F x + F (-x) - F (conj x) - F (-conj x) - 4 * I * x.re * x.im * F₂ 0‖ ≤
      2 / 3 * x.re * x.im * ‖x‖ ^ 2 * M₄ := by
  let E : ℝ → ℂ := fun t ↦ F (x.re + t * I) + F (-x.re + t * (-I)) - F (x.re + t * (-I)) -
    F (-x.re + t * I) - 4 * I * x.re * t * F₂ 0
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 x.im) :
      HasDerivAt E (I * (F₁ ((x.re : ℂ) + t * I) - F₁ (-((x.re : ℂ) + t * I)) +
        F₁ (conj ((x.re : ℂ) + t * I)) - F₁ (-conj ((x.re : ℂ) + t * I)) -
          4 * ((x.re : ℂ) + t * I).re * F₂ 0)) t := by
    have h5 : HasDerivAt (fun r : ℝ ↦ 4 * I * x.re * (r : ℂ) * F₂ 0)
        (4 * I * x.re * F₂ 0) t := by
      simpa using (((hasDerivAt_id (t : ℂ)).const_mul (4 * I * x.re : ℂ)).mul_const
        (F₂ 0)).comp_ofReal
    refine ((hasDerivAt_vertical_combination hx₁ hF ht).sub h5).congr_deriv ?_
    rw [(re_add_im_mul_I x.re t).1]
    ring
  have hbound (t : ℝ) (ht : t ∈ Icc 0 x.im) :
      ‖I * (F₁ ((x.re : ℂ) + t * I) - F₁ (-((x.re : ℂ) + t * I)) +
        F₁ (conj ((x.re : ℂ) + t * I)) - F₁ (-conj ((x.re : ℂ) + t * I)) -
          4 * ((x.re : ℂ) + t * I).re * F₂ 0)‖ ≤
          (2 / 3 * x.re ^ 3 + 2 * x.re * t ^ 2) * M₄ := by
    obtain ⟨h0, h0', hsub⟩ := vertical_point_facts hx₁ ht
    have h := norm_sub_neg_add_conj_sub_neg_conj_sub_le (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
      (F₄ := F₄) (M₄ := M₄) h0 h0' (fun z hz ↦ hF₁ z (hsub hz)) (fun z hz ↦ hF₂ z (hsub hz))
      (fun z hz ↦ hF₃ z (hsub hz)) (fun z hz ↦ hM₄ z (hsub hz))
    obtain ⟨hr, hi⟩ := re_add_im_mul_I x.re t
    rw [hr, hi] at h
    rwa [norm_mul, Complex.norm_I, one_mul, hr]
  have hB (t : ℝ) : HasDerivAt (fun r : ℝ ↦ (2 / 3 * x.re ^ 3 * r + 2 / 3 * x.re * r ^ 3) * M₄)
      ((2 / 3 * x.re ^ 3 + 2 * x.re * t ^ 2) * M₄) t :=
    ((((hasDerivAt_id' t).const_mul _).add ((hasDerivAt_pow 3 t).const_mul _)).mul_const
      M₄).congr_deriv (by ring)
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := E)
    (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (by simp [E]) hB
    (fun t ht ↦ hbound t (Ico_subset_Icc_self ht)) (right_mem_Icc.mpr hx₂)
  obtain ⟨e1, e2, e3, e4⟩ := vertical_endpoints (x := x)
  simp only [E, e1, e2, e3, e4] at h
  have hn : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  exact h.trans_eq (by rw [hn]; ring)

end PDE.Analysis
