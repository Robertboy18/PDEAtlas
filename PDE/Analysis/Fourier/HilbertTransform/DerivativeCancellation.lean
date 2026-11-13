/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.MomentCancellation
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.WeakDerivative

/-!
# The derivative Hilbert cancellation of Chen–Hou–Huang (4.41)

The input derivative is even and may jump at the support endpoints. Its PV is
odd only almost everywhere, which suffices for localization. The two zero
pairings are proved from commutators and skew-adjointness. The input mean is
then obtained from the original vorticity's endpoint values by FTC.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.4, (4.41) and the two pairings before it. <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace PDE.Analysis

/-- Localization by almost-everywhere parity, with support stated pointwise.
This avoids imposing a value on a principal value where it fails to exist. -/
theorem integral_eq_two_mul_integral_Ioo_of_ae_even_support
    {f : ℝ → ℝ} {L : ℝ} (heven : ∀ᵐ x, f (-x) = f x)
    (hsupport : ∀ x, L ≤ |x| → f x = 0) :
    (∫ x, f x) = 2 * ∫ x in Ioo 0 L, f x := by
  let g : ℝ → ℝ := fun x ↦ (f x + f (-x)) / 2
  have hg : Function.Even g := by intro x; dsimp only [g]; rw [neg_neg]; ring
  have hgf : g =ᵐ[volume] f := by
    filter_upwards [heven] with x hx
    dsimp only [g]
    rw [hx]
    ring
  have hgs : ∀ x, L ≤ x → g x = 0 := by
    intro x hx
    have ha := hx.trans (le_abs_self x)
    simp only [g, hsupport x ha, hsupport (-x) (by simpa only [abs_neg] using ha),
      add_zero, zero_div]
  rw [← integral_congr_ae hgf, integral_eq_two_mul_integral_Ioo_of_even_support hg hgs,
    integral_congr_ae (ae_restrict_of_ae hgf)]

/-- Both derivative pairings that precede (4.41). The input may be discontinuous on a null
set; its zero mean and quotient membership are the analytic requirements. -/
theorem integral_Ioo_hilbert_even_cancellations
    {f : ℝ → ℝ} {L : ℝ} (hf : Integrable f) (hf2 : MemLp f 2 volume)
    (hd : ∀ᵐ x, DifferentiableAt ℝ f x) (heven : Function.Even f)
    (hsupport : ∀ x, L ≤ x → f x = 0)
    (hq : Integrable (fun x ↦ f x / x)) (hq2 : MemLp (fun x ↦ f x / x) 2 volume)
    (hm : Integrable (fun x ↦ x * f x)) (hm2 : MemLp (fun x ↦ x * f x) 2 volume)
    (hmean : ∫ x, f x = 0) :
    (∫ x in Ioo 0 L, hilbertPV f x * f x / x) = 0 ∧
      (∫ x in Ioo 0 L, hilbertPV f x * f x * x) = 0 := by
  have hparity : ∀ᵐ x, hilbertPV f (-x) = -hilbertPV f x := by
    filter_upwards [hd] with x hx
    exact ((hasHilbertPV_of_differentiableAt hf hx).neg_of_even heven).hilbertPV_eq
  have hs : ∀ x, L ≤ |x| → f x = 0 := by
    intro x hx
    rcases le_total 0 x with hxpos | hxneg
    · exact hsupport x (by simpa only [abs_of_nonneg hxpos] using hx)
    · rw [← heven x]
      exact hsupport (-x) (by simpa only [abs_of_nonpos hxneg] using hx)
  have h0 := integral_hilbertPV_mul_div_id_of_ae_differentiableAt hf hf2 hd hq hq2
  rw [(hasHilbertPV_zero_of_even heven hf).hilbertPV_eq, zero_pow two_ne_zero, mul_zero] at h0
  have h1 := integral_hilbertPV_mul_id_of_integral_eq_zero hf hf2 hd hm hm2 hmean
  have he0 : ∀ᵐ x, hilbertPV f (-x) * f (-x) / (-x) = hilbertPV f x * f x / x := by
    filter_upwards [hparity] with x hx
    rw [hx, heven x, neg_mul, neg_div_neg_eq]
  have he1 : ∀ᵐ x, hilbertPV f (-x) * f (-x) * (-x) = hilbertPV f x * f x * x := by
    filter_upwards [hparity] with x hx
    rw [hx, heven x]
    ring
  rw [integral_eq_two_mul_integral_Ioo_of_ae_even_support he0
    (fun x hx ↦ by rw [hs x hx, mul_zero, zero_div])] at h0
  rw [integral_eq_two_mul_integral_Ioo_of_ae_even_support he1
    (fun x hx ↦ by rw [hs x hx, mul_zero, zero_mul])] at h1
  constructor <;> linarith

/-- The vanishing of `II₁` that gives (4.41), for a spectral derivative pair. The zero mean is
proved by FTC from the vorticity's endpoint values, and both weighted Hilbert
pairings are derived. Endpoint slopes of `omega` may be nonzero. -/
theorem integral_Ioo_derivative_hilbert_weight_eq_zero
    {L : ℝ} {omega f v : ℝ → ℝ}
    (hL : 0 < L) (hpair : IsHilbertPair f v) (hf : Integrable f)
    (hd : ∀ᵐ x, DifferentiableAt ℝ f x) (heven : Function.Even f)
    (hsupport : ∀ x, L ≤ x → f x = 0)
    (hq : Integrable (fun x ↦ f x / x)) (hq2 : MemLp (fun x ↦ f x / x) 2 volume)
    (hm : Integrable (fun x ↦ x * f x)) (hm2 : MemLp (fun x ↦ x * f x) 2 volume)
    (homega : ContinuousOn omega (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt omega (f x) x)
    (hzero : omega 0 = 0) (hzeroL : omega L = 0) :
    (∫ x in Ioo 0 L, v x * f x * (1 / x - x / L ^ 2)) = 0 := by
  have hi : (∫ x in Ioo 0 L, f x) = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL.le homega
      (fun x hx ↦ (hderiv x hx))
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le).mpr hf.integrableOn)
    rw [intervalIntegral.integral_of_le hL.le, integral_Ioc_eq_integral_Ioo, hzero, hzeroL,
      sub_self] at hFTC
    exact hFTC
  have hmean : ∫ x, f x = 0 := by
    rw [integral_eq_two_mul_integral_Ioo_of_even_support heven hsupport, hi, mul_zero]
  obtain ⟨h0, h1⟩ := integral_Ioo_hilbert_even_cancellations hf hpair.memLp_left hd heven
    hsupport hq hq2 hm hm2 hmean
  have hae := hpair.ae_eq_right (IsHilbertPair.of_integrable_memLp_ae_differentiableAt
    hf hpair.memLp_left hd)
  have h0' : (∫ x in Ioo 0 L, v x * f x / x) = 0 := by
    convert h0 using 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hae] with x hx
    rw [hx]
  have h1' : (∫ x in Ioo 0 L, v x * f x * x) = 0 := by
    convert h1 using 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hae] with x hx
    rw [hx]
  have hi0 : IntegrableOn (fun x ↦ v x * f x / x) (Ioo 0 L) := by
    apply (hpair.memLp_right.integrable_mul hq2).integrableOn.congr
    exact Eventually.of_forall fun x ↦ by dsimp; ring
  have hi1 : IntegrableOn (fun x ↦ v x * f x * x) (Ioo 0 L) := by
    apply (hpair.memLp_right.integrable_mul hm2).integrableOn.congr
    exact Eventually.of_forall fun x ↦ by dsimp; ring
  have heq : (∫ x in Ioo 0 L, v x * f x * (1 / x - x / L ^ 2)) =
      (∫ x in Ioo 0 L, v x * f x / x) -
        (L ^ 2)⁻¹ * ∫ x in Ioo 0 L, v x * f x * x := by
    rw [← integral_const_mul, ← integral_sub hi0 (hi1.const_mul _)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by ring
  rw [heq, h0', h1', mul_zero, sub_self]

/-- A weak input derivative and the original Hilbert law construct the derivative
Hilbert pair and its cancellation, with no assumed relation for the output
derivative. -/
theorem IsHilbertPair.exists_weak_derivative_with_weighted_cancellation
    {L : ℝ} {omega f uX : ℝ → ℝ}
    (hL : 0 < L) (hp : IsHilbertPair omega uX) (hf : Integrable f)
    (hf2 : MemLp f 2 volume)
    (hw : Evolution.HasWeakTimeDerivativeOn univ omega f)
    (hd : ∀ᵐ x, DifferentiableAt ℝ f x) (heven : Function.Even f)
    (hsupport : ∀ x, L ≤ x → f x = 0)
    (hq : Integrable (fun x ↦ f x / x)) (hq2 : MemLp (fun x ↦ f x / x) 2 volume)
    (hm : Integrable (fun x ↦ x * f x)) (hm2 : MemLp (fun x ↦ x * f x) 2 volume)
    (homega : ContinuousOn omega (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt omega (f x) x)
    (hzero : omega 0 = 0) (hzeroL : omega L = 0) :
    ∃ v : ℝ → ℝ, IsHilbertPair f v ∧ Evolution.HasWeakTimeDerivativeOn univ uX v ∧
      (∫ x in Ioo 0 L, v x * f x * (1 / x - x / L ^ 2)) = 0 := by
  obtain ⟨v, hpv, hwv⟩ := hp.exists_hasWeakTimeDerivativeOn hf2 hw
  exact ⟨v, hpv, hwv, integral_Ioo_derivative_hilbert_weight_eq_zero hL hpv hf hd heven
    hsupport hq hq2 hm hm2 homega hderiv hzero hzeroL⟩

end PDE.Analysis
