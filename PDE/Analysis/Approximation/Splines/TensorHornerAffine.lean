/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.TensorHornerDerivatives

/-!
# Physical derivatives of affine tensor Horner polynomials

An inverse affine coordinate contributes its reciprocal scale at each
derivative. The exact mixed derivative table is the existing shifted
falling-factorial table; no new coefficient arithmetic is needed.

## Main definitions

* `tensorHornerAffineValue`: a tensor Horner polynomial evaluated at the local coordinates
  `((x - originX) / scaleX, (y - originY) / scaleY)`.

## Main results

* `iteratedDeriv_comp_sub_div`: the `n`-th derivative of `t ↦ f ((t - origin) / scale)` is
  `scale⁻¹ ^ n` times that of `f` at the local coordinate.
* `contDiff_tensorHornerAffineValue`: the affine tensor polynomial is smooth in `(x, y)`, also
  for a zero scale.
* `mixed_iteratedDeriv_tensorHornerAffineValue`: the mixed derivative of orders `a` in `x` and `b`
  in `y` is `scaleX⁻¹ ^ a * scaleY⁻¹ ^ b` times the value of `tensorDerivativeCoefficients`.
-/

@[expose] public noncomputable section

namespace CAS.Splines

open scoped ContDiff

/-- Iterated differentiation after translation and division by a constant. -/
theorem iteratedDeriv_comp_sub_div {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ n f) (origin scale x : ℝ) :
    iteratedDeriv n (fun t ↦ f ((t - origin) / scale)) x =
      (scale⁻¹) ^ n * iteratedDeriv n f ((x - origin) / scale) := by
  simp only [div_eq_inv_mul]
  rw [iteratedDeriv_comp_sub_const n (fun t ↦ f (scale⁻¹ * t)) origin,
    iteratedDeriv_comp_const_mul hf]

/-- A tensor Horner polynomial evaluated in inverse affine physical coordinates. -/
def tensorHornerAffineValue (nx ny : ℕ) (c : ℕ → ℕ → ℚ)
    (originX scaleX originY scaleY : ℝ) (x y : ℝ) : ℝ :=
  tensorHornerValue (tensorCoefficients nx ny c)
    ((x - originX) / scaleX) ((y - originY) / scaleY)

/-- Affine tensor polynomials are jointly smooth, including constant zero-scale coordinates. -/
theorem contDiff_tensorHornerAffineValue (nx ny : ℕ) (c : ℕ → ℕ → ℚ)
    (originX scaleX originY scaleY : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : ℝ × ℝ ↦
      tensorHornerAffineValue nx ny c originX scaleX originY scaleY p.1 p.2) :=
  (contDiff_tensorHornerValue nx ny c n).comp
    (((contDiff_fst.sub contDiff_const).div_const scaleX).prodMk
      ((contDiff_snd.sub contDiff_const).div_const scaleY))

/-- Physical mixed derivatives retain both reciprocal coordinate scales exactly. -/
theorem mixed_iteratedDeriv_tensorHornerAffineValue (nx ny : ℕ) (c : ℕ → ℕ → ℚ)
    (originX scaleX originY scaleY : ℝ) (a b : ℕ) (x y : ℝ) :
    iteratedDeriv a (fun r ↦ iteratedDeriv b
      (tensorHornerAffineValue nx ny c originX scaleX originY scaleY r) y) x =
      (scaleX⁻¹) ^ a * (scaleY⁻¹) ^ b *
        tensorHornerValue (tensorDerivativeCoefficients nx ny c a b)
          ((x - originX) / scaleX) ((y - originY) / scaleY) := by
  have hinner (r : ℝ) : iteratedDeriv b
      (tensorHornerAffineValue nx ny c originX scaleX originY scaleY r) y =
      (scaleY⁻¹) ^ b * iteratedDeriv b
        (tensorHornerValue (tensorCoefficients nx ny c) ((r - originX) / scaleX))
        ((y - originY) / scaleY) :=
    iteratedDeriv_comp_sub_div
      ((contDiff_tensorHornerValue nx ny c b).comp
        (contDiff_const.prodMk contDiff_id)) originY scaleY y
  simp_rw [hinner]
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_sub_div
      (contDiff_axialJet_tensorHornerValue nx ny c b a ((y - originY) / scaleY)),
    mixed_iteratedDeriv_tensorHornerValue]
  ring

end CAS.Splines
