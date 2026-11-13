/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.WeightedCancellation
import CAS.ExactTactic

/-!
# Hilbert cancellations for the refined derivative energy

The coordinate and inverse-coordinate pairings used in Chen–Hou–Huang (4.41)
and (8.15) follow from spectral skew-adjointness and the PV commutators.
The general statements permit jump discontinuities on a null set. In particular,
they do not require the zero extension of a spatial derivative to be continuous.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.4, (4.41); supplementary material (in the same PDF), Section 8, (8.15).
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped NNReal

noncomputable section

namespace PDE.Analysis

/-- The uncentered inverse-coordinate pairing, with no continuity imposed away from
an a.e. differentiability set. The quotient hypotheses control the origin. -/
theorem integral_hilbertPV_mul_div_id_of_ae_differentiableAt
    {f : ℝ → ℝ} (hf : Integrable f) (hf2 : MemLp f 2 volume)
    (hd : ∀ᵐ x, DifferentiableAt ℝ f x)
    (hq : Integrable (fun x ↦ f x / x))
    (hq2 : MemLp (fun x ↦ f x / x) 2 volume) :
    (∫ x, hilbertPV f x * f x / x) = -(Real.pi / 2) * hilbertPV f 0 ^ 2 := by
  have hp := IsHilbertPair.of_integrable_memLp_ae_differentiableAt hf hf2 hd
  have hqp := IsHilbertPair.of_integrable_memLp_ae_differentiableAt hq hq2
    (ae_differentiableAt_div_id hd)
  have hprod : Integrable (fun x ↦ hilbertPV f x * (f x / x)) :=
    hp.memLp_right.integrable_mul hq2
  have hmass := (hasHilbertPV_zero_of_div_id_integrable hq).hilbertPV_eq
  have hmass' : (∫ x, f x / x) = -Real.pi * hilbertPV f 0 := by
    rw [hmass]
    generalize (∫ x, f x / x) = m
    cas using Real.pi_ne_zero
  have hskew := hp.integral_mul_skew hqp
  have hcomm : (∫ x, f x * hilbertPV (fun y ↦ f y / y) x) =
      (∫ x, hilbertPV f x * (f x / x)) -
        hilbertPV f 0 * ∫ x, f x / x := by
    rw [← integral_const_mul, ← integral_sub hprod (hq.const_mul _)]
    apply integral_congr_ae
    filter_upwards [hd, (volume : Measure ℝ).ae_ne 0] with x hx hx0
    rw [hilbertPV_div_id (hasHilbertPV_of_differentiableAt hf hx) hq hx0]
    ring
  rw [hcomm, hmass'] at hskew
  have hrearrange : (∫ x, hilbertPV f x * f x / x) =
      ∫ x, hilbertPV f x * (f x / x) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by ring
  rw [hrearrange]
  nlinarith

/-- The full-line coordinate pairing is zero when the input has zero mean.
First-moment membership is needed only to apply the spectral skew identity. -/
theorem integral_hilbertPV_mul_id_of_integral_eq_zero
    {f : ℝ → ℝ} (hf : Integrable f) (hf2 : MemLp f 2 volume)
    (hd : ∀ᵐ x, DifferentiableAt ℝ f x)
    (hm : Integrable (fun x ↦ x * f x))
    (hm2 : MemLp (fun x ↦ x * f x) 2 volume)
    (hmean : ∫ x, f x = 0) :
    (∫ x, hilbertPV f x * f x * x) = 0 := by
  have hp := IsHilbertPair.of_integrable_memLp_ae_differentiableAt hf hf2 hd
  have hdm : ∀ᵐ x, DifferentiableAt ℝ (fun y ↦ y * f y) x := by
    filter_upwards [hd] with x hx
    exact differentiableAt_id.mul hx
  have hmp := IsHilbertPair.of_integrable_memLp_ae_differentiableAt hm hm2 hdm
  have hskew := hp.integral_mul_skew hmp
  have hleft : (∫ x, hilbertPV f x * (x * f x)) =
      ∫ x, hilbertPV f x * f x * x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by ring
  have hright : (∫ x, f x * hilbertPV (fun y ↦ y * f y) x) =
      ∫ x, hilbertPV f x * f x * x := by
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    rw [(hasHilbertPV_of_differentiableAt hf hx
      |>.mul_id_of_integral_eq_zero hf hmean).hilbertPV_eq]
    ring
  rw [hleft, hright] at hskew
  linarith

/-- The inverse-coordinate cancellation in (8.15), with its negative sign.
Compact Lipschitz odd input supplies all quotient integrability. -/
theorem integral_Ioo_hilbertPV_mul_div_id
    {f : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsupport : ∀ y, L ≤ y → f y = 0) :
    (∫ x in Ioo 0 L, hilbertPV f x * f x / x) =
      -(Real.pi / 4) * hilbertPV f 0 ^ 2 := by
  have hzero : f 0 = 0 := by simpa using hodd.map_zero
  have h := integral_hilbertPV_mul_div_id_of_ae_differentiableAt
    (memLp_one_iff_integrable.mp (hf.continuous.memLp_of_hasCompactSupport hc))
    (hf.continuous.memLp_of_hasCompactSupport hc) hf.ae_differentiableAt_real
    (memLp_one_iff_integrable.mp (memLp_div_id_of_lipschitzWith_zero hf hc hzero 1))
    (memLp_div_id_of_lipschitzWith_zero hf hc hzero 2)
  have heven : Function.Even (fun x ↦ hilbertPV f x * f x / x) := by
    intro x
    dsimp only
    rw [hilbertPV_even_of_odd hodd x, hodd x, mul_neg, neg_div_neg_eq]
  rw [integral_eq_two_mul_integral_Ioo_of_even_support heven
    (fun x hx ↦ by rw [hsupport x hx, mul_zero, zero_div])] at h
  linarith

/-- The coordinate cancellation in (8.15), on the half support `(0, L)`. -/
theorem integral_Ioo_hilbertPV_mul_id
    {f : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsupport : ∀ y, L ≤ y → f y = 0) :
    (∫ x in Ioo 0 L, hilbertPV f x * f x * x) = 0 := by
  have hm : Continuous (fun x ↦ x * f x) := continuous_id.mul hf.continuous
  have hmc : HasCompactSupport (fun x ↦ x * f x) := hc.mul_left
  have h := integral_hilbertPV_mul_id_of_integral_eq_zero
    (memLp_one_iff_integrable.mp (hf.continuous.memLp_of_hasCompactSupport hc))
    (hf.continuous.memLp_of_hasCompactSupport hc) hf.ae_differentiableAt_real
    (memLp_one_iff_integrable.mp (hm.memLp_of_hasCompactSupport hmc))
    (hm.memLp_of_hasCompactSupport hmc) (integral_eq_zero_of_odd hodd)
  have heven : Function.Even (fun x ↦ hilbertPV f x * f x * x) := by
    intro x
    dsimp only
    rw [hilbertPV_even_of_odd hodd x, hodd x]
    ring
  rw [integral_eq_two_mul_integral_Ioo_of_even_support heven
    (fun x hx ↦ by rw [hsupport x hx, mul_zero, zero_mul])] at h
  linarith

/-- The inverse-coordinate moment with the same normalization as the cancellations. -/
theorem integral_Ioo_div_id_eq_hilbertPV_zero
    {f : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsupport : ∀ y, L ≤ y → f y = 0) :
    (∫ x in Ioo 0 L, f x / x) = -(Real.pi / 2) * hilbertPV f 0 := by
  have hzero : f 0 = 0 := by simpa using hodd.map_zero
  have hq := memLp_one_iff_integrable.mp
    (memLp_div_id_of_lipschitzWith_zero hf hc hzero 1)
  have hm := (hasHilbertPV_zero_of_div_id_integrable hq).hilbertPV_eq
  have heven : Function.Even (fun x ↦ f x / x) := by
    intro x
    dsimp only
    rw [hodd x, neg_div_neg_eq]
  rw [integral_eq_two_mul_integral_Ioo_of_even_support heven
    (fun x hx ↦ by rw [hsupport x hx, zero_div])] at hm
  rw [hm]
  generalize (∫ x in Ioo 0 L, f x / x) = m
  cas using Real.pi_ne_zero

end PDE.Analysis
