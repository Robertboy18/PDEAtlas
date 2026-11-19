/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarHessian
public import PDE.Analysis.Complex.RectangleSymmetrization
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.Analysis.Complex.PlanarRealPart

/-!
# Symmetrized Biot–Savart kernels on the quadrant

For a density `W` odd in both coordinates, an integral `∫_{ℝ²} k(x - y) W(y) dy` over the plane
equals `∫_{ℝ²₊₊} kₛ(x, y) W(y) dy` over the closed quadrant, with the symmetrized kernel

`kₛ(x, y) = k(x - y) - k(x₀ + y₀, x₁ - y₁) - k(x₀ - y₀, x₁ + y₁) + k(x + y)`

of Chen and Hou I, (3.2). For the velocity-gradient kernels `K₁ = hessianKernel 0 1` and
`K₂ = hessianKernel 0 0` we prove the bounds of Part I, Appendix C.3.1, (C.13) and (C.14), and
of Part II, Appendix B.1, in terms of

`Den(x, y) = Σᵢ max(yᵢ - xᵢ, 0)²`,

the squared distance from `y` to the box `Q_x = [-x₀, x₀] × [-x₁, x₁]` (for `x, y` in the
closed quadrant). With `w = y₀ + i y₁` and `F(z) = 1/(2(w + z)²)`, the kernels are
`K₁ₛ(x, y) = -Im(F(x) + F(-x) + F(x̄) + F(-x̄))` and
`K₂ₛ(x, y) = Re(F(x) + F(-x) - F(x̄) - F(-x̄))`,
and `|F''| = 3/|w + z|⁴ ≤ 3/Den²`, `|F⁽⁴⁾| = 60/|w + z|⁶ ≤ 60/Den³` on `Q_x`; the rectangle
lemmas of `PDE.Analysis.Complex.RectangleSymmetrization` then give the bounds below for
`Den(x, y) > 0`, where `∂²_{y₀} K₁(y) = ∂_{y₀}∂_{y₁} K₂(y) = 12 y₀ y₁ (y₀² - y₁²)/|y|⁸`.

## Main definitions

* `symmetrizedKernel`: the odd-odd symmetrization `kₛ` of a planar convolution kernel.
* `boxDistSq`: `Den(x, y) = Σᵢ max(yᵢ - xᵢ, 0)²`.

## Main results

* `abs_symmetrizedKernel_zero_one_sub_le`: `|K₁ₛ - 4 K₁(y)| ≤ 6 |x|²/Den²`.
* `abs_partialDeriv_symmetrizedKernel_zero_one_le`: `|∂_{xᵢ} K₁ₛ| ≤ 12 xᵢ/Den²`.
* `abs_symmetrizedKernel_zero_one_sub_sub_le`:
  `|K₁ₛ - 4 K₁(y) - 2(x₀² - x₁²) ∂²_{y₀} K₁(y)| ≤ 10 |x|⁴/Den³`, and the same bound with `10√2`
  (`abs_symmetrizedKernel_zero_one_sub_sub_le_sqrt_two`).
* `abs_symmetrizedKernel_zero_zero_le`: `|K₂ₛ| ≤ 12 x₀ x₁/Den²`.
* `abs_partialDeriv_symmetrizedKernel_zero_zero_le`: `|∂_{xᵢ} K₂ₛ| ≤ 12 x_{1-i}/Den²`.
* `abs_symmetrizedKernel_zero_zero_sub_le`:
  `|K₂ₛ - 4 x₀ x₁ ∂_{y₀}∂_{y₁} K₂(y)| ≤ 40 x₀ x₁ |x|²/Den³`.
* `boxDistSq_pos`, `sq_div_four_le_boxDistSq`: for `|y| ≥ 2|x|` and `y ≠ 0` the box distance is
  positive, and `Den(x, y) ≥ |y|²/4`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3, (3.2), and
  Appendix C.3.1, (C.13)-(C.14).
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix B.1.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Set Complex PotentialTheory.Planar
open scoped ComplexConjugate
open PDE.Analysis (orthonormalBasisOneI_repr_symm_single_zero
  orthonormalBasisOneI_repr_symm_single_one)

namespace GreenFunction

/-- The odd-odd symmetrization of a planar convolution kernel, Chen–Hou I, (3.2):
`kₛ(x, y) = k(x - y) - k(x - R₀ y) - k(x - R₁ y) + k(x + y)`, where `Rᵢ` reflects the `i`-th
coordinate. -/
def symmetrizedKernel (k : ℝ^2 → ℝ) (x y : ℝ^2) : ℝ :=
  k (x - y) - k (x - PDE.Common.coordinateReflection 0 y) -
    k (x - PDE.Common.coordinateReflection 1 y) + k (x + y)

/-- `Den(x, y) = Σᵢ max(yᵢ - xᵢ, 0)²` of Chen–Hou I, (C.13): for `x, y` in the closed quadrant
it is the squared distance from `y` to the box `[-x₀, x₀] × [-x₁, x₁]`. -/
def boxDistSq (x y : ℝ^2) : ℝ := max (y 0 - x 0) 0 ^ 2 + max (y 1 - x 1) 0 ^ 2

section ComplexForm

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)

/-- `1/(2(-u)²) = 1/(2u²)`. -/
private theorem half_inv_sq_neg (u : ℂ) : 1 / (2 * (-u) ^ 2) = 1 / (2 * u ^ 2) := by
  rw [neg_sq]

/-- `1/(2 (conj u)²) = conj (1/(2u²))`. -/
private theorem half_inv_sq_conj (u : ℂ) : 1 / (2 * (conj u) ^ 2) = conj (1 / (2 * u ^ 2)) := by
  simp only [map_div₀, map_one, map_mul, map_pow, map_ofNat]

/-- The complex form of `K₁ₛ`. -/
theorem symmetrizedKernel_zero_one_eq (x y : ℝ^2) :
    symmetrizedKernel (hessianKernel 0 1) x y =
      -(1 / (2 * (𝔠 y + 𝔠 x) ^ 2) + 1 / (2 * (𝔠 y + -𝔠 x) ^ 2) +
        1 / (2 * (𝔠 y + conj (𝔠 x)) ^ 2) + 1 / (2 * (𝔠 y + -conj (𝔠 x)) ^ 2)).im := by
  unfold symmetrizedKernel
  simp only [hessianKernel_zero_one_eq_neg_im, map_sub, map_add,
    orthonormalBasisOneI_repr_symm_coordinateReflection_zero,
    orthonormalBasisOneI_repr_symm_coordinateReflection_one]
  have e1 : 1 / (2 * (𝔠 x - 𝔠 y) ^ 2) = 1 / (2 * (𝔠 y + -𝔠 x) ^ 2) := by
    rw [← half_inv_sq_neg]; ring_nf
  have e2 : 1 / (2 * (𝔠 x - -conj (𝔠 y)) ^ 2) = conj (1 / (2 * (𝔠 y + conj (𝔠 x)) ^ 2)) := by
    rw [← half_inv_sq_conj]; congr 2; rw [map_add, Complex.conj_conj]; ring
  have e3 : 1 / (2 * (𝔠 x - conj (𝔠 y)) ^ 2) = conj (1 / (2 * (𝔠 y + -conj (𝔠 x)) ^ 2)) := by
    rw [← half_inv_sq_conj]; congr 2; rw [map_add, map_neg, Complex.conj_conj]; ring
  have e4 : 1 / (2 * (𝔠 x + 𝔠 y) ^ 2) = 1 / (2 * (𝔠 y + 𝔠 x) ^ 2) := by ring_nf
  rw [e1, e2, e3, e4, conj_im, conj_im]
  simp only [add_im]
  ring

/-- The complex form of `K₂ₛ`. -/
theorem symmetrizedKernel_zero_zero_eq (x y : ℝ^2) :
    symmetrizedKernel (hessianKernel 0 0) x y =
      (1 / (2 * (𝔠 y + 𝔠 x) ^ 2) + 1 / (2 * (𝔠 y + -𝔠 x) ^ 2) -
        1 / (2 * (𝔠 y + conj (𝔠 x)) ^ 2) - 1 / (2 * (𝔠 y + -conj (𝔠 x)) ^ 2)).re := by
  unfold symmetrizedKernel
  simp only [hessianKernel_zero_zero_eq_re, map_sub, map_add,
    orthonormalBasisOneI_repr_symm_coordinateReflection_zero,
    orthonormalBasisOneI_repr_symm_coordinateReflection_one]
  have e1 : 1 / (2 * (𝔠 x - 𝔠 y) ^ 2) = 1 / (2 * (𝔠 y + -𝔠 x) ^ 2) := by
    rw [← half_inv_sq_neg]; ring_nf
  have e2 : 1 / (2 * (𝔠 x - -conj (𝔠 y)) ^ 2) = conj (1 / (2 * (𝔠 y + conj (𝔠 x)) ^ 2)) := by
    rw [← half_inv_sq_conj]; congr 2; rw [map_add, Complex.conj_conj]; ring
  have e3 : 1 / (2 * (𝔠 x - conj (𝔠 y)) ^ 2) = conj (1 / (2 * (𝔠 y + -conj (𝔠 x)) ^ 2)) := by
    rw [← half_inv_sq_conj]; congr 2; rw [map_add, map_neg, Complex.conj_conj]; ring
  have e4 : 1 / (2 * (𝔠 x + 𝔠 y) ^ 2) = 1 / (2 * (𝔠 y + 𝔠 x) ^ 2) := by ring_nf
  rw [e1, e2, e3, e4, conj_re, conj_re]
  simp only [add_re, sub_re]
  ring

/-- `K₁(y) = -Im(1/(2w²))` at the centre of the box. -/
private theorem hessianKernel_zero_one_eq_neg_im_add_zero (y : ℝ^2) :
    hessianKernel 0 1 y = -(1 / (2 * (𝔠 y + 0) ^ 2)).im := by
  rw [add_zero, hessianKernel_zero_one_eq_neg_im]

/-- Points of the box `Q_x` stay at squared distance at least `Den(x, y)` from `-y`. -/
theorem boxDistSq_le_normSq_add {x y : ℝ^2} {z : ℂ}
    (hz : z ∈ Icc (-(𝔠 x).re) (𝔠 x).re ×ℂ Icc (-(𝔠 x).im) (𝔠 x).im) :
    boxDistSq x y ≤ ‖𝔠 y + z‖ ^ 2 := by
  rw [mem_reProdIm, orthonormalBasisOneI_repr_symm_re, orthonormalBasisOneI_repr_symm_im, mem_Icc,
    mem_Icc] at hz
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, add_re, add_im,
    orthonormalBasisOneI_repr_symm_re, orthonormalBasisOneI_repr_symm_im, boxDistSq]
  have h₀ : max (y 0 - x 0) 0 ^ 2 ≤ (y 0 + z.re) * (y 0 + z.re) := by
    rcases le_total (y 0 - x 0) 0 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have h₁ : max (y 1 - x 1) 0 ^ 2 ≤ (y 1 + z.im) * (y 1 + z.im) := by
    rcases le_total (y 1 - x 1) 0 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  linarith

/-- For `c + z ≠ 0`, `u ↦ a (c + u)^m` has derivative `a m (c + z)^(m - 1)` at `z`. -/
theorem hasDerivAt_const_mul_add_zpow (a c : ℂ) (m : ℤ) {z : ℂ} (hz : c + z ≠ 0) :
    HasDerivAt (fun u ↦ a * (c + u) ^ m) (a * m * (c + z) ^ (m - 1)) z := by
  have h := ((hasDerivAt_zpow m (c + z) (Or.inl hz)).comp z
    ((hasDerivAt_id z).const_add c)).const_mul a
  simpa [mul_assoc] using h

/-- `1/(2u²) = (1/2) u^(-2)`. -/
private theorem half_inv_sq_eq_zpow (u : ℂ) : 1 / (2 * u ^ 2) = 1 / 2 * u ^ (-2 : ℤ) := by
  rw [zpow_neg, zpow_ofNat]; ring

/-- The derivative chain of `F(z) = 1/(2(c + z)²)` away from `-c`. -/
private theorem hasDerivAt_chain {c z : ℂ} (hz : c + z ≠ 0) :
    HasDerivAt (fun u ↦ 1 / (2 * (c + u) ^ 2)) (-1 * (c + z) ^ (-3 : ℤ)) z ∧
    HasDerivAt (fun u ↦ -1 * (c + u) ^ (-3 : ℤ)) (3 * (c + z) ^ (-4 : ℤ)) z ∧
    HasDerivAt (fun u ↦ 3 * (c + u) ^ (-4 : ℤ)) (-12 * (c + z) ^ (-5 : ℤ)) z ∧
    HasDerivAt (fun u ↦ -12 * (c + u) ^ (-5 : ℤ)) (60 * (c + z) ^ (-6 : ℤ)) z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hasDerivAt_const_mul_add_zpow (1 / 2) c (-2) hz
    simp only [half_inv_sq_eq_zpow]
    convert h using 2 <;> norm_num
  · convert hasDerivAt_const_mul_add_zpow (-1) c (-3) hz using 2 <;> norm_num
  · convert hasDerivAt_const_mul_add_zpow 3 c (-4) hz using 2 <;> norm_num
  · convert hasDerivAt_const_mul_add_zpow (-12) c (-5) hz using 2 <;> norm_num

/-- `‖a (c + z)^(-n)‖ ≤ |a| / D^(n/2)` when `‖c + z‖² ≥ D > 0`. -/
private theorem norm_mul_zpow_le {a c z : ℂ} {D : ℝ} (hD : 0 < D) (hz : D ≤ ‖c + z‖ ^ 2)
    (n : ℕ) : ‖a * (c + z) ^ (-(2 * n : ℤ))‖ ≤ ‖a‖ / D ^ n := by
  have hpos : 0 < ‖c + z‖ ^ 2 := lt_of_lt_of_le hD hz
  rw [norm_mul, norm_zpow, zpow_neg, show (2 * n : ℤ) = ((2 * n : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, pow_mul, div_eq_mul_inv]
  gcongr

/-- `-Im (3 w⁻⁴) = 12 y₀ y₁ (y₀² - y₁²) / |y|⁸`, the value of
`∂²_{y₀} K₁(y) = ∂_{y₀}∂_{y₁} K₂(y)`. -/
private theorem neg_im_three_mul_zpow (y : ℝ^2) :
    -(3 * (𝔠 y + 0) ^ (-4 : ℤ)).im = 12 * y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2) / ‖y‖ ^ 8 := by
  rw [add_zero, zpow_neg, zpow_ofNat, mul_im, inv_re, inv_im,
    ← LinearIsometryEquiv.norm_map Complex.orthonormalBasisOneI.repr.symm y,
    show ‖𝔠 y‖ ^ 8 = (‖𝔠 y‖ ^ 2) ^ 4 by ring, ← Complex.normSq_eq_norm_sq]
  have hre : (𝔠 y).re = y 0 := orthonormalBasisOneI_repr_symm_re y
  have him : (𝔠 y).im = y 1 := orthonormalBasisOneI_repr_symm_im y
  set w := 𝔠 y
  have h4im : (w ^ 4).im = 4 * w.re * w.im * (w.re ^ 2 - w.im ^ 2) := by
    simp [pow_succ, pow_zero]; ring
  have hns : Complex.normSq (w ^ 4) = Complex.normSq w ^ 4 := by simp [map_pow]
  rw [h4im, hns, hre, him]
  simp only [re_ofNat, im_ofNat, zero_mul, add_zero]
  rw [Complex.normSq_apply, hre, him]
  by_cases h0 : y 0 * y 0 + y 1 * y 1 = 0
  · have ha : y 0 = 0 := by nlinarith
    have hb : y 1 = 0 := by nlinarith
    simp [ha, hb]
  · field_simp
    ring

/-- `-Im S - 4(-Im E) - 2r(-Im G) = -Im(S - 4E - 2rG)` for real `r`. -/
private theorem im_combination (S E G : ℂ) (r : ℝ) :
    -S.im - 4 * -E.im - 2 * r * -G.im = -(S - 4 * E - 2 * (r : ℂ) * G).im := by
  simp only [sub_im, mul_im, mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im]; ring

/-- `Re D - 4ab(-Im G) = Re(D - 4iabG)` for real `a` and `b`. -/
private theorem re_combination (D G : ℂ) (a b : ℝ) :
    D.re - 4 * a * b * -G.im = (D - 4 * I * a * b * G).re := by
  simp only [sub_re, mul_re, mul_im, re_ofNat, im_ofNat, I_re, I_im, ofReal_re, ofReal_im]; ring

variable {x y : ℝ^2}

/-- For `x` in the closed quadrant, `𝔠 x` has nonnegative real and imaginary parts. -/
private theorem rect_nonneg (hx₀ : 0 ≤ x 0) (hx₁ : 0 ≤ x 1) :
    0 ≤ (𝔠 x).re ∧ 0 ≤ (𝔠 x).im :=
  ⟨by rw [orthonormalBasisOneI_repr_symm_re]; exact hx₀,
    by rw [orthonormalBasisOneI_repr_symm_im]; exact hx₁⟩

/-- If `Den(x, y) > 0`, then `𝔠 y + z ≠ 0` for every `z` in the box `Q_x`. -/
private theorem ne_zero_of_mem_rect (hD : 0 < boxDistSq x y) {z : ℂ}
    (hz : z ∈ Icc (-(𝔠 x).re) (𝔠 x).re ×ℂ Icc (-(𝔠 x).im) (𝔠 x).im) : 𝔠 y + z ≠ 0 := by
  intro h
  have := boxDistSq_le_normSq_add (x := x) (y := y) hz
  rw [h, norm_zero] at this
  linarith [sq_nonneg (0 : ℝ)]

/-- **Chen–Hou I, (C.13), first bound**: `|K₁ₛ(x, y) - 4 K₁(y)| ≤ 6 |x|² / Den²` for `x` in the
closed quadrant and `Den(x, y) > 0`. -/
theorem abs_symmetrizedKernel_zero_one_sub_le (hx₀ : 0 ≤ x 0) (hx₁ : 0 ≤ x 1)
    (hD : 0 < boxDistSq x y) :
    |symmetrizedKernel (hessianKernel 0 1) x y - 4 * hessianKernel 0 1 y| ≤
      6 * ‖x‖ ^ 2 / boxDistSq x y ^ 2 := by
  obtain ⟨h0, h1⟩ := rect_nonneg hx₀ hx₁
  have hchain := fun z hz ↦ hasDerivAt_chain (c := 𝔠 y) (ne_zero_of_mem_rect hD (z := z) hz)
  have h := PDE.Analysis.norm_add_neg_add_conj_add_neg_conj_sub_le
    (F := fun u ↦ 1 / (2 * (𝔠 y + u) ^ 2)) (F₁ := fun u ↦ -1 * (𝔠 y + u) ^ (-3 : ℤ))
    (F₂ := fun u ↦ 3 * (𝔠 y + u) ^ (-4 : ℤ)) (M₂ := 3 / boxDistSq x y ^ 2) h0 h1
    (fun z hz ↦ (hchain z hz).1) (fun z hz ↦ (hchain z hz).2.1)
    (fun z hz ↦ by
      have := norm_mul_zpow_le (a := 3) hD (boxDistSq_le_normSq_add hz) 2
      simpa using this)
  rw [symmetrizedKernel_zero_one_eq, hessianKernel_zero_one_eq_neg_im_add_zero,
    LinearIsometryEquiv.norm_map] at *
  calc _ = |(1 / (2 * (𝔠 y + 𝔠 x) ^ 2) + 1 / (2 * (𝔠 y + -𝔠 x) ^ 2) +
        1 / (2 * (𝔠 y + conj (𝔠 x)) ^ 2) + 1 / (2 * (𝔠 y + -conj (𝔠 x)) ^ 2) -
          4 * (1 / (2 * (𝔠 y + 0) ^ 2))).im| := by
        rw [← abs_neg]; congr 1; simp only [sub_im, mul_im, re_ofNat, im_ofNat]; ring
    _ ≤ _ := Complex.abs_im_le_norm _
    _ ≤ 2 * ‖x‖ ^ 2 * (3 / boxDistSq x y ^ 2) := h
    _ = 6 * ‖x‖ ^ 2 / boxDistSq x y ^ 2 := by ring

/-- The four rectangle hypotheses of the kernel `F(z) = 1/(2(w + z)²)` on `Q_x`. -/
private theorem rect_hyps (hD : 0 < boxDistSq x y) :
    let R := Icc (-(𝔠 x).re) (𝔠 x).re ×ℂ Icc (-(𝔠 x).im) (𝔠 x).im
    (∀ z ∈ R, HasDerivAt (fun u ↦ 1 / (2 * (𝔠 y + u) ^ 2)) (-1 * (𝔠 y + z) ^ (-3 : ℤ)) z) ∧
    (∀ z ∈ R, HasDerivAt (fun u ↦ -1 * (𝔠 y + u) ^ (-3 : ℤ)) (3 * (𝔠 y + z) ^ (-4 : ℤ)) z) ∧
    (∀ z ∈ R, HasDerivAt (fun u ↦ 3 * (𝔠 y + u) ^ (-4 : ℤ)) (-12 * (𝔠 y + z) ^ (-5 : ℤ)) z) ∧
    (∀ z ∈ R, HasDerivAt (fun u ↦ -12 * (𝔠 y + u) ^ (-5 : ℤ)) (60 * (𝔠 y + z) ^ (-6 : ℤ)) z) ∧
    (∀ z ∈ R, ‖3 * (𝔠 y + z) ^ (-4 : ℤ)‖ ≤ 3 / boxDistSq x y ^ 2) ∧
    (∀ z ∈ R, ‖60 * (𝔠 y + z) ^ (-6 : ℤ)‖ ≤ 60 / boxDistSq x y ^ 3) := by
  intro R
  have hchain := fun z (hz : z ∈ R) ↦
    hasDerivAt_chain (c := 𝔠 y) (ne_zero_of_mem_rect hD (z := z) hz)
  refine ⟨fun z hz ↦ (hchain z hz).1, fun z hz ↦ (hchain z hz).2.1,
    fun z hz ↦ (hchain z hz).2.2.1, fun z hz ↦ (hchain z hz).2.2.2, fun z hz ↦ ?_,
    fun z hz ↦ ?_⟩
  · simpa using norm_mul_zpow_le (a := 3) hD (boxDistSq_le_normSq_add hz) 2
  · simpa using norm_mul_zpow_le (a := 60) hD (boxDistSq_le_normSq_add hz) 3

/-- **Chen–Hou I, (C.13), third bound**, with the constant `10`:
`|K₁ₛ(x, y) - 4 K₁(y) - 2(x₀² - x₁²) ∂²_{y₀}K₁(y)| ≤ 10 |x|⁴ / Den³`, where
`∂²_{y₀}K₁(y) = 12 y₀ y₁ (y₀² - y₁²) / |y|⁸`. -/
theorem abs_symmetrizedKernel_zero_one_sub_sub_le (hx₀ : 0 ≤ x 0) (hx₁ : 0 ≤ x 1)
    (hD : 0 < boxDistSq x y) :
    |symmetrizedKernel (hessianKernel 0 1) x y - 4 * hessianKernel 0 1 y -
        2 * (x 0 ^ 2 - x 1 ^ 2) * (12 * y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2) / ‖y‖ ^ 8)| ≤
      10 * ‖x‖ ^ 4 / boxDistSq x y ^ 3 := by
  obtain ⟨h0, h1⟩ := rect_nonneg hx₀ hx₁
  obtain ⟨hF, hF₁, hF₂, hF₃, -, hM₄⟩ := rect_hyps (x := x) (y := y) hD
  have h := PDE.Analysis.norm_add_neg_add_conj_add_neg_conj_sub_sub_le
    (F := fun u ↦ 1 / (2 * (𝔠 y + u) ^ 2)) (F₁ := fun u ↦ -1 * (𝔠 y + u) ^ (-3 : ℤ))
    (F₂ := fun u ↦ 3 * (𝔠 y + u) ^ (-4 : ℤ)) (F₃ := fun u ↦ -12 * (𝔠 y + u) ^ (-5 : ℤ))
    (F₄ := fun u ↦ 60 * (𝔠 y + u) ^ (-6 : ℤ)) (M₄ := 60 / boxDistSq x y ^ 3) h0 h1
    hF hF₁ hF₂ hF₃ hM₄
  rw [← neg_im_three_mul_zpow, symmetrizedKernel_zero_one_eq,
    hessianKernel_zero_one_eq_neg_im_add_zero, ← orthonormalBasisOneI_repr_symm_re x,
    ← orthonormalBasisOneI_repr_symm_im x]
  rw [LinearIsometryEquiv.norm_map] at h
  rw [im_combination, abs_neg]
  calc _ ≤ _ := Complex.abs_im_le_norm _
    _ ≤ ‖x‖ ^ 4 / 6 * (60 / boxDistSq x y ^ 3) := h
    _ = 10 * ‖x‖ ^ 4 / boxDistSq x y ^ 3 := by ring

/-- **Chen–Hou I, (C.13), third bound**, with the constant `10√2`. -/
theorem abs_symmetrizedKernel_zero_one_sub_sub_le_sqrt_two (hx₀ : 0 ≤ x 0) (hx₁ : 0 ≤ x 1)
    (hD : 0 < boxDistSq x y) :
    |symmetrizedKernel (hessianKernel 0 1) x y - 4 * hessianKernel 0 1 y -
        2 * (x 0 ^ 2 - x 1 ^ 2) * (12 * y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2) / ‖y‖ ^ 8)| ≤
      10 * Real.sqrt 2 * ‖x‖ ^ 4 / boxDistSq x y ^ 3 := by
  refine (abs_symmetrizedKernel_zero_one_sub_sub_le hx₀ hx₁ hD).trans ?_
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hpos : 0 ≤ ‖x‖ ^ 4 / boxDistSq x y ^ 3 := by positivity
  calc 10 * ‖x‖ ^ 4 / boxDistSq x y ^ 3 = 10 * (‖x‖ ^ 4 / boxDistSq x y ^ 3) := by ring
    _ ≤ 10 * Real.sqrt 2 * (‖x‖ ^ 4 / boxDistSq x y ^ 3) := by nlinarith
    _ = _ := by ring

/-- **Chen–Hou I, (C.14), first bound**: `|K₂ₛ(x, y)| ≤ 12 x₀ x₁ / Den²`. -/
theorem abs_symmetrizedKernel_zero_zero_le (hx₀ : 0 ≤ x 0) (hx₁ : 0 ≤ x 1)
    (hD : 0 < boxDistSq x y) :
    |symmetrizedKernel (hessianKernel 0 0) x y| ≤ 12 * x 0 * x 1 / boxDistSq x y ^ 2 := by
  obtain ⟨h0, h1⟩ := rect_nonneg hx₀ hx₁
  obtain ⟨hF, hF₁, -, -, hM₂, -⟩ := rect_hyps (x := x) (y := y) hD
  have h := PDE.Analysis.norm_add_neg_sub_conj_sub_neg_conj_le
    (F := fun u ↦ 1 / (2 * (𝔠 y + u) ^ 2)) (F₁ := fun u ↦ -1 * (𝔠 y + u) ^ (-3 : ℤ))
    (F₂ := fun u ↦ 3 * (𝔠 y + u) ^ (-4 : ℤ)) (M₂ := 3 / boxDistSq x y ^ 2) h0 h1 hF hF₁ hM₂
  rw [symmetrizedKernel_zero_zero_eq]
  rw [orthonormalBasisOneI_repr_symm_re, orthonormalBasisOneI_repr_symm_im] at h
  calc _ ≤ _ := Complex.abs_re_le_norm _
    _ ≤ 4 * x 0 * x 1 * (3 / boxDistSq x y ^ 2) := h
    _ = 12 * x 0 * x 1 / boxDistSq x y ^ 2 := by ring

/-- **Chen–Hou I, (C.14), third bound**:
`|K₂ₛ(x, y) - 4 x₀ x₁ ∂_{y₀}∂_{y₁}K₂(y)| ≤ 40 x₀ x₁ |x|² / Den³`, where
`∂_{y₀}∂_{y₁}K₂(y) = 12 y₀ y₁ (y₀² - y₁²) / |y|⁸`. -/
theorem abs_symmetrizedKernel_zero_zero_sub_le (hx₀ : 0 ≤ x 0) (hx₁ : 0 ≤ x 1)
    (hD : 0 < boxDistSq x y) :
    |symmetrizedKernel (hessianKernel 0 0) x y -
        4 * x 0 * x 1 * (12 * y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2) / ‖y‖ ^ 8)| ≤
      40 * x 0 * x 1 * ‖x‖ ^ 2 / boxDistSq x y ^ 3 := by
  obtain ⟨h0, h1⟩ := rect_nonneg hx₀ hx₁
  obtain ⟨hF, hF₁, hF₂, hF₃, -, hM₄⟩ := rect_hyps (x := x) (y := y) hD
  have h := PDE.Analysis.norm_add_neg_sub_conj_sub_neg_conj_sub_le
    (F := fun u ↦ 1 / (2 * (𝔠 y + u) ^ 2)) (F₁ := fun u ↦ -1 * (𝔠 y + u) ^ (-3 : ℤ))
    (F₂ := fun u ↦ 3 * (𝔠 y + u) ^ (-4 : ℤ)) (F₃ := fun u ↦ -12 * (𝔠 y + u) ^ (-5 : ℤ))
    (F₄ := fun u ↦ 60 * (𝔠 y + u) ^ (-6 : ℤ)) (M₄ := 60 / boxDistSq x y ^ 3) h0 h1
    hF hF₁ hF₂ hF₃ hM₄
  rw [← neg_im_three_mul_zpow, symmetrizedKernel_zero_zero_eq,
    ← orthonormalBasisOneI_repr_symm_re x, ← orthonormalBasisOneI_repr_symm_im x]
  rw [LinearIsometryEquiv.norm_map] at h
  rw [re_combination]
  calc _ ≤ _ := Complex.abs_re_le_norm _
    _ ≤ 2 / 3 * (𝔠 x).re * (𝔠 x).im * ‖x‖ ^ 2 * (60 / boxDistSq x y ^ 3) := h
    _ = 40 * (𝔠 x).re * (𝔠 x).im * ‖x‖ ^ 2 / boxDistSq x y ^ 3 := by ring

/-- Line derivatives of `F` at the four reflections of a moving point `X + t v`. -/
private theorem hasDerivAt_four_points {F F₁ : ℂ → ℂ} {X : ℂ} (v : ℂ)
    (h₁ : HasDerivAt F (F₁ X) X) (h₂ : HasDerivAt F (F₁ (-X)) (-X))
    (h₃ : HasDerivAt F (F₁ (conj X)) (conj X)) (h₄ : HasDerivAt F (F₁ (-conj X)) (-conj X)) :
    HasDerivAt (fun t : ℝ ↦ F (X + t * v)) (F₁ X * v) 0 ∧
    HasDerivAt (fun t : ℝ ↦ F (-(X + t * v))) (F₁ (-X) * -v) 0 ∧
    HasDerivAt (fun t : ℝ ↦ F (conj (X + t * v))) (F₁ (conj X) * conj v) 0 ∧
    HasDerivAt (fun t : ℝ ↦ F (-conj (X + t * v))) (F₁ (-conj X) * -conj v) 0 := by
  have line (c w : ℂ) (h : HasDerivAt F (F₁ c) c) :
      HasDerivAt (fun t : ℝ ↦ F (c + t * w)) (F₁ c * w) 0 := by
    have := PDE.Analysis.hasDerivAt_comp_affineLine (G := F) (G' := F₁) c w (t := 0)
      (by simpa using h)
    simpa using this
  refine ⟨line X v h₁, ?_, ?_, ?_⟩
  · have := line (-X) (-v) h₂
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only; congr 1; ring
  · have := line (conj X) (conj v) h₃
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [map_add, map_mul, conj_ofReal]
  · have := line (-conj X) (-conj v) h₄
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [map_add, map_mul, conj_ofReal]; congr 1; ring

/-- `𝔠 (x + t eᵢ) = 𝔠 x + t 𝔠 eᵢ` for the unit vector `eᵢ`. -/
private theorem cx_add_smul_single (x : ℝ^2) (i : Fin 2) (t : ℝ) :
    𝔠 (x + t • EuclideanSpace.single i (1 : ℝ)) =
      𝔠 x + (t : ℂ) * 𝔠 (EuclideanSpace.single i (1 : ℝ)) := by
  rw [map_add, map_smul, Complex.real_smul]

/-- Under `Den(x, y) > 0` the four arguments of the symmetrized kernel are off the pole. -/
private theorem symmetrizedKernel_args_ne_zero (hx₀ : 0 ≤ x 0) (hx₁ : 0 ≤ x 1)
    (hD : 0 < boxDistSq x y) :
    x - y ≠ 0 ∧ x - PDE.Common.coordinateReflection 0 y ≠ 0 ∧
      x - PDE.Common.coordinateReflection 1 y ≠ 0 ∧ x + y ≠ 0 := by
  have hD0 : ∀ a b : ℝ, y 0 = a → y 1 = b → a ≤ x 0 → b ≤ x 1 → False := by
    intro a b ha hb hax hbx
    have h0 : max (y 0 - x 0) 0 = 0 := max_eq_right (by linarith)
    have h1 : max (y 1 - x 1) 0 = 0 := max_eq_right (by linarith)
    unfold boxDistSq at hD
    rw [h0, h1] at hD
    norm_num at hD
  have c0 (v : ℝ^2) (h : v = 0) : v 0 = 0 := by rw [h]; rfl
  have c1 (v : ℝ^2) (h : v = 0) : v 1 = 0 := by rw [h]; rfl
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · have e0 := c0 _ h; have e1 := c1 _ h
    simp only [PiLp.sub_apply] at e0 e1
    exact hD0 (x 0) (x 1) (by linarith) (by linarith) le_rfl le_rfl
  · have e0 := c0 _ h; have e1 := c1 _ h
    simp only [PiLp.sub_apply, PDE.Common.coordinateReflection_apply_same,
      PDE.Common.coordinateReflection_apply_of_ne (0 : Fin 2) 1 (by decide) y] at e0 e1
    exact hD0 (-x 0) (x 1) (by linarith) (by linarith) (by linarith) le_rfl
  · have e0 := c0 _ h; have e1 := c1 _ h
    simp only [PiLp.sub_apply, PDE.Common.coordinateReflection_apply_same,
      PDE.Common.coordinateReflection_apply_of_ne (1 : Fin 2) 0 (by decide) y] at e0 e1
    exact hD0 (x 0) (-x 1) (by linarith) (by linarith) le_rfl (by linarith)
  · have e0 := c0 _ h; have e1 := c1 _ h
    simp only [PiLp.add_apply] at e0 e1
    exact hD0 (-x 0) (-x 1) (by linarith) (by linarith) (by linarith) (by linarith)

/-- Differentiability of a symmetrized Hessian kernel in its first argument. -/
private theorem differentiableAt_symmetrizedKernel (a b : Fin 2) (hx₀ : 0 ≤ x 0)
    (hx₁ : 0 ≤ x 1) (hD : 0 < boxDistSq x y) :
    DifferentiableAt ℝ (fun x' ↦ symmetrizedKernel (hessianKernel a b) x' y) x := by
  obtain ⟨h1, h2, h3, h4⟩ := symmetrizedKernel_args_ne_zero hx₀ hx₁ hD
  have d (c : ℝ^2) (hc : x - c ≠ 0) :
      DifferentiableAt ℝ (fun x' : ℝ^2 ↦ hessianKernel a b (x' - c)) x :=
    ((contDiffAt_hessianKernel a b hc (n := 1)).differentiableAt one_ne_zero).comp x
      (differentiableAt_id.sub_const c)
  have d' : DifferentiableAt ℝ (fun x' : ℝ^2 ↦ hessianKernel a b (x' + y)) x := by
    have := d (-y) (by simpa using h4)
    simpa using this
  unfold symmetrizedKernel
  exact (((d y h1).sub (d _ h2)).sub (d _ h3)).add d'

/-- The partial derivative of a function along `eᵢ` through a line derivative. -/
private theorem partialDeriv_eq_of_hasDerivAt {f : ℝ^2 → ℝ} {i : Fin 2} {d : ℝ}
    (hf : DifferentiableAt ℝ f x)
    (h : HasDerivAt (fun t : ℝ ↦ f (x + t • EuclideanSpace.single i (1 : ℝ))) d 0) :
    (PDE.partialDeriv i f) x = d := by
  unfold PDE.partialDeriv
  rw [← hf.lineDeriv_eq_fderiv]
  exact HasLineDerivAt.lineDeriv h

/-- If `Re X ≥ 0` and `Im X ≥ 0`, then `X`, `-X`, `conj X` and `-conj X` lie in the box `[-Re X, Re
X] × [-Im X, Im X]`. -/
private theorem mem_rect_four {X : ℂ} (h0 : 0 ≤ X.re) (h1 : 0 ≤ X.im) :
    X ∈ Icc (-X.re) X.re ×ℂ Icc (-X.im) X.im ∧ -X ∈ Icc (-X.re) X.re ×ℂ Icc (-X.im) X.im ∧
    conj X ∈ Icc (-X.re) X.re ×ℂ Icc (-X.im) X.im ∧
    -conj X ∈ Icc (-X.re) X.re ×ℂ Icc (-X.im) X.im := by
  simp only [PDE.Analysis.mem_reProdIm_Icc_neg_iff, neg_re, neg_im, conj_re, conj_im, abs_neg,
    abs_of_nonneg h0, abs_of_nonneg h1, le_refl, and_self]

/-- **Chen–Hou I, (C.13), second bound**: `|∂_{xᵢ} K₁ₛ(x, y)| ≤ 12 xᵢ / Den²`. -/
theorem abs_partialDeriv_symmetrizedKernel_zero_one_le (i : Fin 2) (hx₀ : 0 ≤ x 0)
    (hx₁ : 0 ≤ x 1) (hD : 0 < boxDistSq x y) :
    |(PDE.partialDeriv i (fun x' ↦ symmetrizedKernel (hessianKernel 0 1) x' y)) x| ≤
      12 * x i / boxDistSq x y ^ 2 := by
  obtain ⟨h0, h1⟩ := rect_nonneg hx₀ hx₁
  obtain ⟨hF, hF₁, -, -, hM₂, -⟩ := rect_hyps (x := x) (y := y) hD
  obtain ⟨m1, m2, m3, m4⟩ := mem_rect_four h0 h1
  set v := 𝔠 (EuclideanSpace.single i (1 : ℝ))
  obtain ⟨d1, d2, d3, d4⟩ := hasDerivAt_four_points (F := fun u ↦ 1 / (2 * (𝔠 y + u) ^ 2))
    (F₁ := fun u ↦ -1 * (𝔠 y + u) ^ (-3 : ℤ)) (X := 𝔠 x) v (hF _ m1) (hF _ m2) (hF _ m3)
    (hF _ m4)
  have hline : HasDerivAt
      (fun t : ℝ ↦ symmetrizedKernel (hessianKernel 0 1) (x + t • EuclideanSpace.single i 1) y)
      (-((-1 * (𝔠 y + 𝔠 x) ^ (-3 : ℤ)) * v + (-1 * (𝔠 y + -𝔠 x) ^ (-3 : ℤ)) * -v +
        (-1 * (𝔠 y + conj (𝔠 x)) ^ (-3 : ℤ)) * conj v +
        (-1 * (𝔠 y + -conj (𝔠 x)) ^ (-3 : ℤ)) * -conj v).im) 0 := by
    have h := (((d1.add d2).add d3).add d4)
    have h' := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h).neg
    refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [Pi.neg_apply, Pi.add_apply, Function.comp_apply, Complex.imCLM_apply]
    rw [symmetrizedKernel_zero_one_eq, cx_add_smul_single]
  rw [partialDeriv_eq_of_hasDerivAt (differentiableAt_symmetrizedKernel 0 1 hx₀ hx₁ hD) hline,
    abs_neg]
  fin_cases i
  · have hb := PDE.Analysis.norm_sub_neg_add_conj_sub_neg_conj_le h0 h1 hF₁ hM₂
    simp only [v, Fin.zero_eta, Fin.isValue, orthonormalBasisOneI_repr_symm_single_zero, map_one,
      mul_one, mul_neg] at hb ⊢
    rw [orthonormalBasisOneI_repr_symm_re] at hb
    calc _ ≤ _ := Complex.abs_im_le_norm _
      _ = _ := by congr 1
      _ ≤ 4 * x 0 * (3 / boxDistSq x y ^ 2) := hb
      _ = _ := by simp; ring
  · have hb := PDE.Analysis.norm_sub_neg_sub_conj_add_neg_conj_le h0 h1 hF₁ hM₂
    simp only [v, Fin.mk_one, Fin.isValue, orthonormalBasisOneI_repr_symm_single_one, conj_I,
      mul_neg, neg_neg] at hb ⊢
    rw [orthonormalBasisOneI_repr_symm_im] at hb
    calc _ ≤ _ := Complex.abs_im_le_norm _
      _ = ‖I * ((-1 * (𝔠 y + 𝔠 x) ^ (-3 : ℤ)) - (-1 * (𝔠 y + -𝔠 x) ^ (-3 : ℤ)) -
          (-1 * (𝔠 y + conj (𝔠 x)) ^ (-3 : ℤ)) + (-1 * (𝔠 y + -conj (𝔠 x)) ^ (-3 : ℤ)))‖ := by
        congr 1; ring
      _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ 4 * x 1 * (3 / boxDistSq x y ^ 2) := hb
      _ = _ := by simp; ring

/-- **Chen–Hou I, (C.14), second bound**: `|∂_{xᵢ} K₂ₛ(x, y)| ≤ 12 x_{1-i} / Den²`. -/
theorem abs_partialDeriv_symmetrizedKernel_zero_zero_le (i : Fin 2) (hx₀ : 0 ≤ x 0)
    (hx₁ : 0 ≤ x 1) (hD : 0 < boxDistSq x y) :
    |(PDE.partialDeriv i (fun x' ↦ symmetrizedKernel (hessianKernel 0 0) x' y)) x| ≤
      12 * x (1 - i) / boxDistSq x y ^ 2 := by
  obtain ⟨h0, h1⟩ := rect_nonneg hx₀ hx₁
  obtain ⟨hF, hF₁, -, -, hM₂, -⟩ := rect_hyps (x := x) (y := y) hD
  obtain ⟨m1, m2, m3, m4⟩ := mem_rect_four h0 h1
  set v := 𝔠 (EuclideanSpace.single i (1 : ℝ))
  obtain ⟨d1, d2, d3, d4⟩ := hasDerivAt_four_points (F := fun u ↦ 1 / (2 * (𝔠 y + u) ^ 2))
    (F₁ := fun u ↦ -1 * (𝔠 y + u) ^ (-3 : ℤ)) (X := 𝔠 x) v (hF _ m1) (hF _ m2) (hF _ m3)
    (hF _ m4)
  have hline : HasDerivAt
      (fun t : ℝ ↦ symmetrizedKernel (hessianKernel 0 0) (x + t • EuclideanSpace.single i 1) y)
      (((-1 * (𝔠 y + 𝔠 x) ^ (-3 : ℤ)) * v + (-1 * (𝔠 y + -𝔠 x) ^ (-3 : ℤ)) * -v -
        (-1 * (𝔠 y + conj (𝔠 x)) ^ (-3 : ℤ)) * conj v -
        (-1 * (𝔠 y + -conj (𝔠 x)) ^ (-3 : ℤ)) * -conj v).re) 0 := by
    have h := (((d1.add d2).sub d3).sub d4)
    have h' := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Complex.reCLM_apply]
    rw [symmetrizedKernel_zero_zero_eq, cx_add_smul_single]
  rw [partialDeriv_eq_of_hasDerivAt (differentiableAt_symmetrizedKernel 0 0 hx₀ hx₁ hD) hline]
  fin_cases i
  · have hb := PDE.Analysis.norm_sub_neg_sub_conj_add_neg_conj_le h0 h1 hF₁ hM₂
    simp only [v, Fin.zero_eta, Fin.isValue, orthonormalBasisOneI_repr_symm_single_zero, map_one,
      mul_one, mul_neg] at hb ⊢
    rw [orthonormalBasisOneI_repr_symm_im] at hb
    calc _ ≤ _ := Complex.abs_re_le_norm _
      _ = _ := by congr 1; ring
      _ ≤ 4 * x 1 * (3 / boxDistSq x y ^ 2) := hb
      _ = _ := by simp; ring
  · have hb := PDE.Analysis.norm_sub_neg_add_conj_sub_neg_conj_le h0 h1 hF₁ hM₂
    simp only [v, Fin.mk_one, Fin.isValue, orthonormalBasisOneI_repr_symm_single_one, conj_I,
      mul_neg, neg_neg] at hb ⊢
    rw [orthonormalBasisOneI_repr_symm_re] at hb
    calc _ ≤ _ := Complex.abs_re_le_norm _
      _ = ‖I * ((-1 * (𝔠 y + 𝔠 x) ^ (-3 : ℤ)) - (-1 * (𝔠 y + -𝔠 x) ^ (-3 : ℤ)) +
          (-1 * (𝔠 y + conj (𝔠 x)) ^ (-3 : ℤ)) - (-1 * (𝔠 y + -conj (𝔠 x)) ^ (-3 : ℤ)))‖ := by
        congr 1; ring
      _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ 4 * x 0 * (3 / boxDistSq x y ^ 2) := hb
      _ = _ := by simp; ring

end ComplexForm

/-- For `x, y` in the closed quadrant with `y ≠ 0` and `2|x| ≤ |y|`, the box distance is
positive, so the bounds of (C.13)-(C.14) apply in the regime of Chen–Hou. -/
theorem boxDistSq_pos {x y : ℝ^2} (hx₀ : 0 ≤ x 0) (hx₁ : 0 ≤ x 1) (hy₀ : 0 ≤ y 0)
    (hy₁ : 0 ≤ y 1) (hy : y ≠ 0) (hxy : 2 * ‖x‖ ≤ ‖y‖) : 0 < boxDistSq x y := by
  unfold boxDistSq
  by_contra hlt
  have hle := not_lt.mp hlt
  have h₀ : max (y 0 - x 0) 0 = 0 := by
    have := sq_nonneg (max (y 1 - x 1) 0)
    nlinarith [sq_nonneg (max (y 0 - x 0) 0), le_max_right (y 0 - x 0) 0]
  have h₁ : max (y 1 - x 1) 0 = 0 := by
    have := sq_nonneg (max (y 0 - x 0) 0)
    nlinarith [sq_nonneg (max (y 1 - x 1) 0), le_max_right (y 1 - x 1) 0]
  have hy0 : y 0 ≤ x 0 := by have := le_max_left (y 0 - x 0) 0; linarith
  have hy1 : y 1 ≤ x 1 := by have := le_max_left (y 1 - x 1) 0; linarith
  have hn : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_fin_two, EuclideanSpace.norm_sq_fin_two]
    nlinarith
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  nlinarith [norm_nonneg x]

/-- **`Den(x, y) ≥ |y|²/4` for `|y| ≥ 2|x|`** (Chen–Hou I, after (C.13): `Den ≍ |y|²`): with
`z = (max(yᵢ - xᵢ, 0))ᵢ`, `0 ≤ y ≤ x + z` componentwise gives `|y| ≤ |x| + |z|`. -/
theorem sq_div_four_le_boxDistSq {x y : ℝ^2} (hy₀ : 0 ≤ y 0) (hy₁ : 0 ≤ y 1)
    (hxy : 2 * ‖x‖ ≤ ‖y‖) : ‖y‖ ^ 2 / 4 ≤ boxDistSq x y := by
  set z : ℝ^2 := WithLp.toLp 2 ![max (y 0 - x 0) 0, max (y 1 - x 1) 0]
  have hz0 : z 0 = max (y 0 - x 0) 0 := by simp [z]
  have hz1 : z 1 = max (y 1 - x 1) 0 := by simp [z]
  have hzD : ‖z‖ ^ 2 = boxDistSq x y := by rw [EuclideanSpace.norm_sq_fin_two, hz0, hz1, boxDistSq]
  have hyxz : ‖y‖ ≤ ‖x + z‖ := by
    have h0 : y 0 ≤ x 0 + z 0 := by rw [hz0]; linarith [le_max_left (y 0 - x 0) 0]
    have h1 : y 1 ≤ x 1 + z 1 := by rw [hz1]; linarith [le_max_left (y 1 - x 1) 0]
    have hsq : ‖y‖ ^ 2 ≤ ‖x + z‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_fin_two, EuclideanSpace.norm_sq_fin_two]
      simp only [PiLp.add_apply]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  have hz : ‖y‖ / 2 ≤ ‖z‖ := by linarith [norm_add_le x z]
  rw [← hzD]
  nlinarith [norm_nonneg y]

end GreenFunction
