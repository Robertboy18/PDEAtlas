/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.QuotientBounds

/-!
# Inverse-square Hilbert bounds for even inputs

Differentiating an odd compactly supported function produces an even input
which may jump at the support boundary. The quotient commutator still applies:
integrability and almost-everywhere differentiability suffice. Evenness removes
the origin principal value, so division by the coordinate preserves the Hilbert
pair without an extra constant.

This supplies the derivative norm comparison used with singular Sobolev
multipliers.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis

/-- An even input with an integrable coordinate quotient commutes with division
by the coordinate. The output is identified almost everywhere, so endpoint jumps
of the input are allowed. -/
theorem IsHilbertPair.div_id_of_even {f v : ℝ → ℝ}
    (hp : IsHilbertPair f v) (hf : Integrable f)
    (hd : ∀ᵐ x, DifferentiableAt ℝ f x) (heven : Function.Even f)
    (hq : Integrable (fun x ↦ f x / x))
    (hq2 : MemLp (fun x ↦ f x / x) 2 volume) :
    IsHilbertPair (fun x ↦ f x / x) (fun x ↦ v x / x) := by
  have hvalue := hp.ae_eq_right
    (IsHilbertPair.of_integrable_memLp_ae_differentiableAt hf hp.memLp_left hd)
  have hzero := (hasHilbertPV_zero_of_even heven hf).hilbertPV_eq
  apply (IsHilbertPair.of_integrable_memLp_ae_differentiableAt hq hq2
    (ae_differentiableAt_div_id hd)).congr_right_ae
  filter_upwards [hd, hvalue, (volume : Measure ℝ).ae_ne 0] with x hdx hvx hx
  rw [hvx, hilbertPV_div_id (hasHilbertPV_of_differentiableAt hf hdx) hq hx,
    hzero, sub_zero]

/-- The coordinate quotient of an odd Hilbert output has no larger square
integral on the positive support interval than the even input quotient. -/
theorem IsHilbertPair.integral_div_id_sq_le_of_even {f v : ℝ → ℝ} {L : ℝ}
    (hp : IsHilbertPair f v) (hf : Integrable f)
    (hd : ∀ᵐ x, DifferentiableAt ℝ f x) (heven : Function.Even f)
    (hv : Function.Odd v) (hsupport : ∀ x, L ≤ x → f x = 0)
    (hq : Integrable (fun x ↦ f x / x))
    (hq2 : MemLp (fun x ↦ f x / x) 2 volume) :
    (∫ x in Ioo 0 L, (v x / x) ^ 2) ≤
      ∫ x in Ioo 0 L, (f x / x) ^ 2 := by
  apply (hp.div_id_of_even hf hd heven hq hq2).integral_sq_Ioo_le_of_even_sq
  · intro x
    simp only [heven x, div_neg, neg_sq]
  · intro x
    simp only [hv x, neg_div_neg_eq]
  · intro x hx
    simp only [hsupport x hx, zero_div]

/-- Two Hilbert pairs give the singular weighted comparison. Only the parity of
the squares is needed, so the estimate covers either parity of the input. -/
theorem IsHilbertPair.integral_sq_inv_square_weight_le
    {f v : ℝ → ℝ} {L a b : ℝ}
    (hp : IsHilbertPair f v)
    (hpq : IsHilbertPair (fun x ↦ f x / x) (fun x ↦ v x / x))
    (hf : Function.Even (fun x ↦ f x ^ 2))
    (hv : Function.Even (fun x ↦ v x ^ 2))
    (hsupport : ∀ x, L ≤ x → f x = 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x in Ioo 0 L, v x ^ 2 * (a / x ^ 2 + b)) ≤
      ∫ x in Ioo 0 L, f x ^ 2 * (a / x ^ 2 + b) := by
  rw [integral_sq_mul_inv_square_add (hpq.memLp_right.restrict _)
      (hp.memLp_right.restrict _),
    integral_sq_mul_inv_square_add (hpq.memLp_left.restrict _) (hp.memLp_left.restrict _)]
  have hquot : (∫ x in Ioo 0 L, (v x / x) ^ 2) ≤
      ∫ x in Ioo 0 L, (f x / x) ^ 2 := by
    apply hpq.integral_sq_Ioo_le_of_even_sq
    · intro x
      dsimp only
      have hfx : f (-x) ^ 2 = f x ^ 2 := hf x
      rw [div_pow, div_pow, hfx, neg_sq]
    · intro x
      dsimp only
      have hvx : v (-x) ^ 2 = v x ^ 2 := hv x
      rw [div_pow, div_pow, hvx, neg_sq]
    · intro x hx
      simp only [hsupport x hx, zero_div]
  exact add_le_add (mul_le_mul_of_nonneg_left hquot ha)
    (mul_le_mul_of_nonneg_left (hp.integral_sq_Ioo_le_of_even_sq hf hv hsupport) hb)

end PDE.Analysis
