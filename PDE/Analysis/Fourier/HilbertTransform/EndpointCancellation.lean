/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.WeightedCancellation
import CAS.ExactTactic

/-!
# Endpoint product cancellation for compact Lipschitz vorticity

Translating the origin cancellation to any zero of the input proves the product
Hilbert identity at that point. Odd reflection then gives Chen–Hou–Huang (4.20), the
endpoint term of their weighted `L²` estimate. No derivative is prescribed at
the support endpoints.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.2.2, (4.20). <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped NNReal

noncomputable section

namespace PDE.Analysis

/-- Every coordinate quotient about a zero of compact Lipschitz input belongs to `Lᵖ`.
Translation allows the zero to lie at a support endpoint with a derivative jump. -/
theorem memLp_div_sub_of_lipschitzWith_zero {f : ℝ → ℝ} {K : ℝ≥0} {a : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f a = 0)
    (p : ENNReal) : MemLp (fun x ↦ f x / (x - a)) p (volume : Measure ℝ) := by
  have hg : LipschitzWith K (fun y ↦ f (y + a)) := by
    simpa only [mul_one, Function.comp_def] using hf.comp (isometry_add_right a).lipschitzWith
  have hgc := hc.comp_homeomorph (Homeomorph.addRight a)
  have hgzero : (fun y ↦ f (y + a)) 0 = 0 := by simpa only [zero_add] using hzero
  have hq := memLp_div_id_of_lipschitzWith_zero hg hgc hgzero p
  simpa only [Function.comp_def, sub_add_cancel] using
    hq.comp_measurePreserving (measurePreserving_sub_right volume a)

/-- The first origin cancellation translated to an arbitrary zero of compact Lipschitz input. -/
theorem integral_hilbertPV_sub_value_mul_div_sub {f : ℝ → ℝ} {K : ℝ≥0} {a : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f a = 0) :
    (∫ x, (hilbertPV f x - hilbertPV f a) * f x / (x - a)) =
      Real.pi / 2 * hilbertPV f a ^ 2 := by
  let g : ℝ → ℝ := fun y ↦ f (y + a)
  have hg : LipschitzWith K g := by
    simpa only [g, mul_one, Function.comp_def] using hf.comp (isometry_add_right a).lipschitzWith
  have hgc : HasCompactSupport g := hc.comp_homeomorph (Homeomorph.addRight a)
  have hgzero : g 0 = 0 := by simpa only [g, zero_add] using hzero
  have hshift (x : ℝ) : hilbertPV g x = hilbertPV f (x + a) :=
    (hasHilbertPV_of_lipschitzWith_compactSupport hf hc (x + a)).translate.hilbertPV_eq
  calc
    _ = ∫ y, (hilbertPV f (y + a) - hilbertPV f a) * f (y + a) / y := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun x ↦ (hilbertPV f x - hilbertPV f a) * f x / (x - a)) a).symm
    _ = _ := by
      simpa only [hshift, g, zero_add] using
        integral_hilbertPV_sub_zero_mul_div_id hg hgc hgzero

/-- The uncentered Hilbert kernel of the product is absolutely integrable at a zero
of the vorticity. The Hilbert factor is controlled by its spectral `L²` norm. -/
theorem integrable_hilbertKernel_const_add_mul_of_zero {f : ℝ → ℝ} {K : ℝ≥0} {a : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f a = 0) (c : ℝ) :
    Integrable (fun x ↦ ((c + hilbertPV f x) * f x) / (a - x)) := by
  have hq : Integrable (fun x ↦ f x / (x - a)) := memLp_one_iff_integrable.mp
    (memLp_div_sub_of_lipschitzWith_zero hf hc hzero 1)
  have hprod := (IsHilbertPair.of_lipschitzWith_compactSupport hf hc).memLp_right.integrable_mul
    (memLp_div_sub_of_lipschitzWith_zero hf hc hzero 2)
  apply ((hq.const_mul c).add hprod).neg.congr
  exact Eventually.of_forall fun x ↦ by
    dsimp only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
    rw [← neg_sub x a, div_neg]
    ring

/-- The exact endpoint product integral. Its sign follows the kernel `1/(a-x)`. -/
theorem integral_hilbertKernel_const_add_mul_of_zero {f : ℝ → ℝ} {K : ℝ≥0} {a : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f a = 0) (c : ℝ) :
    (∫ x, ((c + hilbertPV f x) * f x) / (a - x)) =
      Real.pi * c * hilbertPV f a + Real.pi / 2 * hilbertPV f a ^ 2 := by
  let q : ℝ → ℝ := fun x ↦ f x / (x - a)
  have hq : Integrable q := memLp_one_iff_integrable.mp
    (memLp_div_sub_of_lipschitzWith_zero hf hc hzero 1)
  have hprod : Integrable (fun x ↦ hilbertPV f x * q x) :=
    (IsHilbertPair.of_lipschitzWith_compactSupport hf hc).memLp_right.integrable_mul
      (memLp_div_sub_of_lipschitzWith_zero hf hc hzero 2)
  have hmass : (∫ x, q x) = -Real.pi * hilbertPV f a := by
    have hkernel := integrable_hilbertKernel_of_lipschitzWith_zero hf hc hzero
    have hPV := (hasHilbertPV_of_integrable_uncentered hkernel).hilbertPV_eq
    have hneg : (∫ x, f x / (a - x)) = -∫ x, q x := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by dsimp only [q]; rw [← neg_sub x a, div_neg]
    rw [hneg] at hPV
    generalize (∫ x, q x) = m at hPV ⊢
    rw [hPV]
    cas using Real.pi_ne_zero
  have hcancel := integral_hilbertPV_sub_value_mul_div_sub hf hc hzero
  have hexpand : (∫ x, (hilbertPV f x - hilbertPV f a) * f x / (x - a)) =
      (∫ x, hilbertPV f x * q x) - hilbertPV f a * ∫ x, q x := by
    rw [← integral_const_mul, ← integral_sub hprod (hq.const_mul _)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by dsimp only [q]; ring
  have htarget : (∫ x, ((c + hilbertPV f x) * f x) / (a - x)) =
      -(c * (∫ x, q x) + ∫ x, hilbertPV f x * q x) := by
    rw [← integral_const_mul, ← integral_add (hq.const_mul _) hprod, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by
      dsimp only [q]
      rw [← neg_sub x a, div_neg]
      ring
  rw [hexpand, hmass] at hcancel
  rw [htarget, hmass]
  nlinarith

/-- The product Hilbert identity at a zero of the input, including support endpoints.
The existence and value of this PV are proved by an absolutely integrable kernel. -/
theorem hasHilbertPV_const_add_mul_of_zero {f : ℝ → ℝ} {K : ℝ≥0} {a : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f a = 0) (c : ℝ) :
    HasHilbertPV (fun x ↦ (c + hilbertPV f x) * f x) a
      (c * hilbertPV f a + hilbertPV f a ^ 2 / 2) := by
  have h := hasHilbertPV_of_integrable_uncentered
    (integrable_hilbertKernel_const_add_mul_of_zero hf hc hzero c)
  rw [integral_hilbertKernel_const_add_mul_of_zero hf hc hzero c] at h
  convert h using 1
  generalize hilbertPV f a = v
  cas using Real.pi_ne_zero

/-- The endpoint boundary form in (4.20) is absolutely integrable on `(0,L)`.
Reflection of the integrable full-line endpoint kernel proves this directly. -/
theorem integrableOn_Ioo_endpoint_boundary_form {f : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (hL : 0 < L) (hf : LipschitzWith K f) (hc : HasCompactSupport f)
    (hodd : Function.Odd f) (hsupport : ∀ y, L ≤ y → f y = 0) (c : ℝ) :
    IntegrableOn (fun x ↦ ((c + hilbertPV f x) * f x) * (-2 * x / (L ^ 2 - x ^ 2)))
      (Ioo 0 L) := by
  have hkernel := integrable_hilbertKernel_const_add_mul_of_zero hf hc (hsupport L le_rfl) c
  apply (hkernel.add hkernel.comp_neg).fun_neg.integrableOn.congr_fun
    (hs := measurableSet_Ioo)
  intro x hx
  dsimp only [Pi.add_apply, Pi.neg_apply]
  rw [sub_neg_eq_add, hilbertPV_even_of_odd hodd x, hodd x]
  have hminus : L - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  have hplus : L + x ≠ 0 := (add_pos hL hx.1).ne'
  have hden : L ^ 2 - x ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  generalize hilbertPV f x = v, f x = w
  cas using hden

/-- Chen–Hou–Huang (4.20), with exact coefficients and the spectral Hilbert transform.
Compact Lipschitz odd input suffices; its prescribed nonzero endpoint slope is allowed. -/
theorem integral_Ioo_endpoint_boundary_cancellation {f : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (hL : 0 < L) (hf : LipschitzWith K f) (hc : HasCompactSupport f)
    (hodd : Function.Odd f) (hsupport : ∀ y, L ≤ y → f y = 0) (c : ℝ) :
    (∫ x in Ioo 0 L, ((c + hilbertPV f x) * f x) * (-2 * x / (L ^ 2 - x ^ 2))) =
      -Real.pi * c * hilbertPV f L - Real.pi / 2 * hilbertPV f L ^ 2 := by
  let g : ℝ → ℝ := fun x ↦ (c + hilbertPV f x) * f x
  have hgeven : Function.Odd g := by
    intro x
    dsimp only [g]
    rw [hilbertPV_even_of_odd hodd x, hodd x, mul_neg]
  have hgSupport : ∀ y, L ≤ y → g y = 0 := by
    intro y hy
    simp only [g, hsupport y hy, mul_zero]
  have hzero := hsupport L le_rfl
  have hkernel := integrable_hilbertKernel_const_add_mul_of_zero hf hc hzero c
  have hmoment := (hasHilbertPV_right_odd_support hL hgeven hgSupport hkernel).hilbertPV_eq
  have hproduct := (hasHilbertPV_const_add_mul_of_zero hf hc hzero c).hilbertPV_eq
  have hident : (∫ x in Ioo 0 L, g x * (-2 * x / (L ^ 2 - x ^ 2))) =
      -Real.pi * ∫ x in Ioo 0 L, (2 * x / (Real.pi * (L ^ 2 - x ^ 2))) * g x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    have hminus : L - x ≠ 0 := (sub_pos.mpr hx.2).ne'
    have hplus : L + x ≠ 0 := (add_pos hL hx.1).ne'
    have hden : L ^ 2 - x ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero hplus hminus
    dsimp only
    generalize g x = v
    cas using hden
  change (∫ x in Ioo 0 L, g x * (-2 * x / (L ^ 2 - x ^ 2))) = _
  rw [hident, ← hmoment, hproduct]
  ring

end PDE.Analysis
