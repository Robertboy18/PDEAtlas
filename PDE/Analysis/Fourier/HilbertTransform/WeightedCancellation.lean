/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.PrincipalValue
public import PDE.Analysis.Fourier.HilbertTransform.LogPotential.Lipschitz
import CAS.ExactTactic
public import PDE.Analysis.MeasureTheory.Integral.Reflection

/-!
# Singular-weight cancellation from the Hilbert relation

Spectral skew-adjointness and the principal-value coordinate commutator give the
origin cancellations in Chen–Hou–Huang (4.19). Derivative jumps away from the origin
are allowed. The cubic-weight identity assumes integrability of the second quotient.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.2.2, (4.19), and Appendix A.1, Lemma A.3, (A.5)-(A.6).
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped NNReal

noncomputable section

namespace PDE.Analysis

/-- Division by the coordinate preserves a.e. differentiability, since its only new
singularity is the null singleton at zero. -/
theorem ae_differentiableAt_div_id {f : ℝ → ℝ}
    (hf : ∀ᵐ x, DifferentiableAt ℝ f x) :
    ∀ᵐ x, DifferentiableAt ℝ (fun y ↦ f y / y) x := by
  filter_upwards [hf, (volume : Measure ℝ).ae_ne 0] with x hx hx0
  exact hx.div differentiableAt_id hx0

/-- A compact Lipschitz function vanishing at zero has its coordinate quotient in
all `Lᵖ` spaces. This proves the first-quotient hypotheses used in the cancellation. -/
theorem memLp_div_id_of_lipschitzWith_zero {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f 0 = 0)
    (p : ENNReal) : MemLp (fun x ↦ f x / x) p (volume : Measure ℝ) := by
  have hcompact : HasCompactSupport (fun x ↦ f x / x) := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using hc.mul_right (f' := fun x ↦ x⁻¹)
  apply hcompact.memLp_of_bound
    (hf.continuous.measurable.div measurable_id).aestronglyMeasurable (K : ℝ)
  apply Eventually.of_forall
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have h := hf.norm_sub_le x 0
  simp only [hzero, sub_zero] at h
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr h

/-- The full-line `x⁻¹` cancellation in (A.5), specialized to a zero of Lipschitz input.
The value at zero and the two Hilbert transforms are the principal values. -/
theorem integral_hilbertPV_sub_zero_mul_div_id {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    (∫ x, (hilbertPV f x - hilbertPV f 0) * f x / x) =
      Real.pi / 2 * hilbertPV f 0 ^ 2 := by
  let q : ℝ → ℝ := fun x ↦ f x / x
  have hq : Integrable q := memLp_one_iff_integrable.mp
    (memLp_div_id_of_lipschitzWith_zero hf hc hzero 1)
  have hq2 : MemLp q 2 volume := memLp_div_id_of_lipschitzWith_zero hf hc hzero 2
  have hpair := IsHilbertPair.of_lipschitzWith_compactSupport hf hc
  have hqpair := IsHilbertPair.of_integrable_memLp_ae_differentiableAt hq hq2
    (ae_differentiableAt_div_id hf.ae_differentiableAt_real)
  have hcomm : ∀ᵐ x, hilbertPV q x = (hilbertPV f x - hilbertPV f 0) / x := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
    exact hilbertPV_div_id (hasHilbertPV_of_lipschitzWith_compactSupport hf hc x) hq hx
  have hprod : Integrable (fun x ↦ hilbertPV f x * q x) := hpair.memLp_right.integrable_mul hq2
  have hmass := (hasHilbertPV_zero_of_div_id_integrable hq).hilbertPV_eq
  have hskew := hpair.integral_mul_skew hqpair
  have hrewrite : (∫ x, f x * hilbertPV q x) =
      ∫ x, (hilbertPV f x - hilbertPV f 0) * f x / x := by
    apply integral_congr_ae
    filter_upwards [hcomm] with x hx
    rw [hx]
    ring
  rw [hrewrite] at hskew
  have hexpand : (∫ x, (hilbertPV f x - hilbertPV f 0) * f x / x) =
      (∫ x, hilbertPV f x * q x) - hilbertPV f 0 * ∫ x, q x := by
    rw [← integral_const_mul, ← integral_sub hprod (hq.const_mul _)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by dsimp only [q]; ring
  have hpi := Real.pi_ne_zero
  rw [hexpand] at hskew ⊢
  have hmass' : (∫ x, q x) = -Real.pi * hilbertPV f 0 := by
    generalize (∫ x, q x) = m at hmass ⊢
    rw [hmass]
    cas using hpi
  rw [hmass'] at hskew ⊢
  nlinarith

/-- The singular integrand in the first cancellation is absolutely integrable. -/
theorem integrable_hilbertPV_sub_zero_mul_div_id {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    Integrable (fun x ↦ (hilbertPV f x - hilbertPV f 0) * f x / x) := by
  have hq : Integrable (fun x ↦ f x / x) := memLp_one_iff_integrable.mp
    (memLp_div_id_of_lipschitzWith_zero hf hc hzero 1)
  have hprod := (IsHilbertPair.of_lipschitzWith_compactSupport hf hc).memLp_right.integrable_mul
    (memLp_div_id_of_lipschitzWith_zero hf hc hzero 2)
  apply (hprod.sub (hq.const_mul (hilbertPV f 0))).congr
  exact Eventually.of_forall fun x ↦ by dsimp only [Pi.sub_apply, Pi.mul_apply]; ring

/-- The full-line `x⁻³` cancellation in (4.19). The `L²` hypothesis on `f/x²`
excludes a nonzero linear term at the origin, while allowing all support-endpoint corners. -/
theorem integral_hilbertPV_sub_zero_mul_div_cube {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsecondLp : MemLp (fun x ↦ f x / x ^ 2) 2 (volume : Measure ℝ)) :
    (∫ x, (hilbertPV f x - hilbertPV f 0) * f x / x ^ 3) = 0 := by
  have hzero : f 0 = 0 := by simpa using hodd.map_zero
  let q : ℝ → ℝ := fun x ↦ f x / x
  let r : ℝ → ℝ := fun x ↦ q x / x
  have hq : Integrable q := memLp_one_iff_integrable.mp
    (memLp_div_id_of_lipschitzWith_zero hf hc hzero 1)
  have hq2 : MemLp q 2 volume := memLp_div_id_of_lipschitzWith_zero hf hc hzero 2
  have hr2 : MemLp r 2 volume := by simpa only [r, q, div_div, pow_two] using hsecondLp
  have hrc : HasCompactSupport r := by
    simpa only [r, q, div_eq_mul_inv, Pi.mul_def] using
      (hc.mul_right (f' := fun x ↦ x⁻¹)).mul_right (f' := fun x ↦ x⁻¹)
  have hr : Integrable r := memLp_one_iff_integrable.mp
    (hr2.mono_exponent_of_measure_support_ne_top
      (fun _ hx ↦ image_eq_zero_of_notMem_tsupport hx) hrc.measure_lt_top.ne (by norm_num))
  have hdq := ae_differentiableAt_div_id hf.ae_differentiableAt_real
  have hqpair := IsHilbertPair.of_integrable_memLp_ae_differentiableAt hq hq2 hdq
  have hrpair := IsHilbertPair.of_integrable_memLp_ae_differentiableAt hr hr2
    (ae_differentiableAt_div_id hdq)
  have hqeven : Function.Even q := by
    intro x
    dsimp only [q]
    rw [hodd x, neg_div_neg_eq]
  have hqzero : hilbertPV q 0 = 0 := (hasHilbertPV_zero_of_even hqeven hq).hilbertPV_eq
  have hcomm : ∀ᵐ x, hilbertPV q x = (hilbertPV f x - hilbertPV f 0) / x ∧
      hilbertPV r x = hilbertPV q x / x := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
    have hpv := hasHilbertPV_of_lipschitzWith_compactSupport hf hc x
    refine ⟨hilbertPV_div_id hpv hq hx, ?_⟩
    have hh := hilbertPV_div_id (hpv.div_id hq hx) hr hx
    change hilbertPV r x = (hilbertPV q x - hilbertPV q 0) / x at hh
    simpa only [hqzero, sub_zero] using hh
  have hleft : (∫ x, hilbertPV q x * r x) =
      ∫ x, (hilbertPV f x - hilbertPV f 0) * f x / x ^ 3 := by
    apply integral_congr_ae
    filter_upwards [hcomm] with x hx
    rw [hx.1]
    dsimp only [r, q]
    ring
  have hright : (∫ x, q x * hilbertPV r x) =
      ∫ x, (hilbertPV f x - hilbertPV f 0) * f x / x ^ 3 := by
    apply integral_congr_ae
    filter_upwards [hcomm] with x hx
    rw [hx.2, hx.1]
    dsimp only [q]
    ring
  have h := hqpair.integral_mul_skew hrpair
  rw [hleft, hright] at h
  linarith

/-- The cubic-weight cancellation integral is absolutely integrable under its stated
second-quotient hypotheses. This is a product of two `L²` Hilbert-pair factors. The
second-quotient hypothesis forces `f 0 = 0`, since `x⁻⁴` is not integrable at the origin. -/
theorem integrable_hilbertPV_sub_zero_mul_div_cube {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f)
    (hsecondLp : MemLp (fun x ↦ f x / x ^ 2) 2 (volume : Measure ℝ)) :
    Integrable (fun x ↦ (hilbertPV f x - hilbertPV f 0) * f x / x ^ 3) := by
  have hzero : f 0 = 0 := by
    by_contra h0
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.continuous_iff.mp hf.continuous 0 (|f 0| / 2) (by positivity)
    have hc2 : 0 < f 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
    have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (-4 : ℝ)) (Ioo 0 δ) := by
      refine ((hsecondLp.integrable_sq.integrableOn).const_mul (4 / f 0 ^ 2)).mono'
        ((measurable_id.pow_const _).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hd : dist (f x) (f 0) < |f 0| / 2 :=
        hball x (by rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; exact hx.2)
      rw [Real.dist_eq] at hd
      have h1 : |f 0| / 2 ≤ |f x| := by
        have := abs_sub_abs_le_abs_sub (f 0) (f x)
        rw [abs_sub_comm] at this
        linarith
      have hfx : f 0 ^ 2 / 4 ≤ f x ^ 2 := by
        have h3 := mul_le_mul h1 h1 (by positivity) (abs_nonneg _)
        nlinarith [sq_abs (f 0), sq_abs (f x)]
      have hx0 := hx.1
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _), Real.rpow_neg hx0.le,
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (x ^ 4)⁻¹ = f 0 ^ 2 / 4 * (4 / f 0 ^ 2) / x ^ 4 := by field_simp
        _ ≤ f x ^ 2 * (4 / f 0 ^ 2) / x ^ 4 := by gcongr
        _ = 4 / f 0 ^ 2 * (f x / x ^ 2) ^ 2 := by ring
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mp hpow
    norm_num at this
  have hq : Integrable (fun x ↦ f x / x) := memLp_one_iff_integrable.mp
    (memLp_div_id_of_lipschitzWith_zero hf hc hzero 1)
  have hqpair := IsHilbertPair.of_integrable_memLp_ae_differentiableAt hq
    (memLp_div_id_of_lipschitzWith_zero hf hc hzero 2)
    (ae_differentiableAt_div_id hf.ae_differentiableAt_real)
  apply (hqpair.memLp_right.integrable_mul hsecondLp).congr
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  dsimp only [Pi.mul_apply]
  rw [hilbertPV_div_id (hasHilbertPV_of_lipschitzWith_compactSupport hf hc x) hq hx]
  ring

/-- The second equality of Chen–Hou–Huang (4.19), with the exact half-line factor `π/4`.
All PVs and the weighted integral are supplied by compact Lipschitz input. -/
theorem integral_Ioo_hilbertPV_sub_zero_mul_div_id {f : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsupport : ∀ y, L ≤ y → f y = 0) :
    (∫ x in Ioo 0 L, (hilbertPV f x - hilbertPV f 0) * f x / x) =
      Real.pi / 4 * hilbertPV f 0 ^ 2 := by
  have hzero : f 0 = 0 := by simpa using hodd.map_zero
  have heven : Function.Even (fun x ↦ (hilbertPV f x - hilbertPV f 0) * f x / x) := by
    intro x
    dsimp only
    rw [hilbertPV_even_of_odd hodd x, hodd x, mul_neg, neg_div_neg_eq]
  have h := integral_hilbertPV_sub_zero_mul_div_id hf hc hzero
  rw [integral_eq_two_mul_integral_Ioo_of_even_support heven
    (fun y hy ↦ by rw [hsupport y hy, mul_zero, zero_div])] at h
  linarith

/-- The first equality of Chen–Hou–Huang (4.19). The origin assumption is `L²`
control of `f/x²`; compact support supplies `L¹`. No derivative is imposed at the
support endpoints. -/
theorem integral_Ioo_hilbertPV_sub_zero_mul_div_cube {f : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsupport : ∀ y, L ≤ y → f y = 0)
    (hsecondLp : MemLp (fun x ↦ f x / x ^ 2) 2 (volume : Measure ℝ)) :
    (∫ x in Ioo 0 L, (hilbertPV f x - hilbertPV f 0) * f x / x ^ 3) = 0 := by
  have heven : Function.Even (fun x ↦ (hilbertPV f x - hilbertPV f 0) * f x / x ^ 3) := by
    intro x
    dsimp only
    have hpow : (-x) ^ 3 = -(x ^ 3) := by cas
    rw [hilbertPV_even_of_odd hodd x, hodd x, mul_neg, hpow, neg_div_neg_eq]
  have h := integral_hilbertPV_sub_zero_mul_div_cube hf hc hodd hsecondLp
  rw [integral_eq_two_mul_integral_Ioo_of_even_support heven
    (fun y hy ↦ by rw [hsupport y hy, mul_zero, zero_div])] at h
  linarith

end PDE.Analysis
