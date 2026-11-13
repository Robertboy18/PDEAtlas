/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.EndpointCancellation
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import CAS.IntegrationTactic

/-!
# Weighted Hilbert norms in the interior interaction

The quotient commutator identifies both divided differences of the velocity gradient
with spectral Hilbert transforms. Their isometries supply the norm comparisons
in Chen–Hou–Huang (4.13)–(4.16). Compact Lipschitz vorticity is sufficient at the support
endpoints; the second origin quotient is required to belong to `L²`.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.2.1, (4.13)-(4.17), and Section 4.2.2, (4.19). <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

open Filter MeasureTheory Set PDE.Analysis
open scoped NNReal Topology

noncomputable section

namespace PDE.Analysis

/-- The twice-divided origin commutator, using the odd input to remove its middle mode. -/
theorem isHilbertPair_div_sq {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsecond : MemLp (fun x ↦ f x / x ^ 2) 2 (volume : Measure ℝ)) :
    IsHilbertPair (fun x ↦ f x / x ^ 2)
      (fun x ↦ (hilbertPV f x - hilbertPV f 0) / x ^ 2) := by
  let q : ℝ → ℝ := fun x ↦ f x / x
  let r : ℝ → ℝ := fun x ↦ f x / x ^ 2
  have hq : Integrable q := memLp_one_iff_integrable.mp
    (memLp_div_id_of_lipschitzWith_zero hf hc hodd.map_zero 1)
  have hrc : HasCompactSupport r := by
    simpa only [r, div_eq_mul_inv, Pi.mul_def] using
      hc.mul_right (f' := fun x ↦ (x ^ 2)⁻¹)
  have hr2 : MemLp r 2 volume := hsecond
  have hr : Integrable r := memLp_one_iff_integrable.mp
    (hr2.mono_exponent_of_measure_support_ne_top
      (fun _ hx ↦ image_eq_zero_of_notMem_tsupport hx) hrc.measure_lt_top.ne (by norm_num))
  have hd : ∀ᵐ x, DifferentiableAt ℝ r x := by
    simpa only [r, q, div_div, pow_two] using
      ae_differentiableAt_div_id (ae_differentiableAt_div_id hf.ae_differentiableAt_real)
  apply (IsHilbertPair.of_integrable_memLp_ae_differentiableAt hr hsecond hd).congr_right_ae
  have hqeven : Function.Even q := by
    intro x
    simp only [q, hodd x, neg_div_neg_eq]
  have hq0 := (hasHilbertPV_zero_of_even hqeven hq).hilbertPV_eq
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  have hpv := hasHilbertPV_of_lipschitzWith_compactSupport hf hc x
  have hfirst := hilbertPV_div_id hpv hq hx
  have hsecondPV := hilbertPV_div_id (hpv.div_id hq hx)
    (show Integrable (fun y ↦ q y / y) by simpa only [q, div_div, ← pow_two] using hr) hx
  simpa only [q, r, div_div, ← pow_two, hq0, sub_zero, hfirst] using hsecondPV

/-- A translated quotient commutator at any zero, with the principal value. -/
theorem hilbertPV_div_sub_of_lipschitzWith_zero {f : ℝ → ℝ} {K : ℝ≥0} {a x : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f a = 0)
    (hx : x ≠ a) :
    hilbertPV (fun y ↦ f y / (y - a)) x =
      (hilbertPV f x - hilbertPV f a) / (x - a) := by
  let g : ℝ → ℝ := fun y ↦ f (y + a)
  have hg : LipschitzWith K g := by
    simpa only [g, mul_one, Function.comp_def] using
      hf.comp (isometry_add_right a).lipschitzWith
  have hgc : HasCompactSupport g := hc.comp_homeomorph (Homeomorph.addRight a)
  have hgz : g 0 = 0 := by simpa only [g, zero_add] using hzero
  have hq : Integrable (fun y ↦ g y / y) :=
    memLp_one_iff_integrable.mp (memLp_div_id_of_lipschitzWith_zero hg hgc hgz 1)
  have hpv := hasHilbertPV_of_lipschitzWith_compactSupport hg hgc (x - a)
  have hdiv := hpv.div_id hq (sub_ne_zero.mpr hx)
  have hshift := hdiv.translate (a := -a) (x := x)
  have hshiftFn : (fun y ↦ g (y + -a) / (y + -a)) = (fun y ↦ f y / (y - a)) := by
    funext y
    simp only [g, ← sub_eq_add_neg, sub_add_cancel]
  rw [hshiftFn] at hshift
  rw [hshift.hilbertPV_eq]
  have hcomm := hilbertPV_div_id hpv hq (sub_ne_zero.mpr hx)
  have hxPV : hilbertPV g (x - a) = hilbertPV f x := by
    have h := (hasHilbertPV_of_lipschitzWith_compactSupport hf hc x)
    simpa only [sub_add_cancel, g] using
      (show HasHilbertPV g (x - a) (hilbertPV f x) from
        (show HasHilbertPV f ((x - a) + a) (hilbertPV f x) by
          simpa only [sub_add_cancel] using h).translate).hilbertPV_eq
  have h0PV : hilbertPV g 0 = hilbertPV f a := by
    exact (show HasHilbertPV g 0 (hilbertPV f a) from
      (show HasHilbertPV f (0 + a) (hilbertPV f a) by
        simpa only [zero_add] using
          hasHilbertPV_of_lipschitzWith_compactSupport hf hc a).translate).hilbertPV_eq
  rw [← hdiv.hilbertPV_eq, hcomm, hxPV, h0PV]

/-- The right divided difference is a Hilbert pair even at a slope jump. -/
theorem isHilbertPair_div_sub {f : ℝ → ℝ} {K : ℝ≥0} {a : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hzero : f a = 0) :
    IsHilbertPair (fun x ↦ f x / (x - a))
      (fun x ↦ (hilbertPV f x - hilbertPV f a) / (x - a)) := by
  have hd : ∀ᵐ x, DifferentiableAt ℝ (fun y ↦ f y / (y - a)) x := by
    filter_upwards [hf.ae_differentiableAt_real, (volume : Measure ℝ).ae_ne a] with x hx hxa
    exact hx.div (differentiableAt_id.sub_const a) (sub_ne_zero.mpr hxa)
  apply (IsHilbertPair.of_integrable_memLp_ae_differentiableAt
    (memLp_one_iff_integrable.mp (memLp_div_sub_of_lipschitzWith_zero hf hc hzero 1))
    (memLp_div_sub_of_lipschitzWith_zero hf hc hzero 2) hd).congr_right_ae
  filter_upwards [(volume : Measure ℝ).ae_ne a] with x hx
  exact hilbertPV_div_sub_of_lipschitzWith_zero hf hc hzero hx

/-- The origin norm comparison in (4.13), obtained from the twice-divided pair. -/
theorem integral_origin_divided_difference_sq_le {f : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsupport : ∀ y, L ≤ y → f y = 0)
    (hsecond : MemLp (fun x ↦ f x / x ^ 2) 2 (volume : Measure ℝ)) :
    (∫ x in Ioo 0 L, ((hilbertPV f x - hilbertPV f 0) / x ^ 2) ^ 2) ≤
      ∫ x in Ioo 0 L, (f x / x ^ 2) ^ 2 := by
  apply (isHilbertPair_div_sq hf hc hodd hsecond).integral_sq_Ioo_le
  · intro x
    simp only [hodd x, neg_sq, neg_div]
  · intro x
    simp only [hilbertPV_even_of_odd hodd x, neg_sq]
  · intro x hx
    simp only [hsupport x hx, zero_div]

/-- Reflection and support give the exact full-line endpoint input norm in (4.17). -/
theorem integral_div_sub_sq_eq_Ioo {f : ℝ → ℝ} {K : ℝ≥0} {L : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hodd : Function.Odd f)
    (hsupport : ∀ y, L ≤ y → f y = 0) :
    (∫ x, (f x / (x - L)) ^ 2) =
      ∫ x in Ioo 0 L, (f x / (x - L)) ^ 2 + (f x / (x + L)) ^ 2 := by
  have hmem := memLp_div_sub_of_lipschitzWith_zero hf hc (hsupport L le_rfl) 2
  rw [integral_eq_integral_Ioi_add_reflection hmem.integrable_sq]
  have heq (x : ℝ) : (f x / (x - L)) ^ 2 + (f (-x) / (-x - L)) ^ 2 =
      (f x / (x - L)) ^ 2 + (f x / (x + L)) ^ 2 := by
    rw [hodd x, show -x - L = -(x + L) by cas, neg_div_neg_eq]
  simp_rw [heq]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ hx ↦ hx.1)
  intro x hx
  simp only [hsupport x (not_lt.mp fun hlt ↦ hx.2 ⟨hx.1, hlt⟩), zero_div,
    zero_pow (by decide : 2 ≠ 0), add_zero]

/-- The exterior correction in (4.15): Cauchy–Schwarz against `x+L` on `(0,L)`
retains the contribution of the reflected interval `(-L,0)`. -/
theorem integral_right_divided_difference_sq_le {f u : ℝ → ℝ} {K : ℝ≥0} {L c : ℝ}
    (hL : 0 < L) (hf : LipschitzWith K f) (hc : HasCompactSupport f)
    (hodd : Function.Odd f) (hsupport : ∀ y, L ≤ y → f y = 0)
    (hu : ∀ x, HasDerivAt u (hilbertPV f x) x) (hu0 : u 0 = 0) (huL : u L = -c * L) :
    (∫ x in Ioo 0 L, ((hilbertPV f x - hilbertPV f L) / (x - L)) ^ 2) ≤
      (∫ x, (f x / (x - L)) ^ 2) - 3 / (7 * L) * (c + hilbertPV f L) ^ 2 := by
  let v : ℝ → ℝ := fun x ↦ hilbertPV f x - hilbertPV f L
  let q : ℝ → ℝ := fun x ↦ v x / (x - L)
  let r : ℝ → ℝ := fun x ↦ v x / (x + L)
  have hvEven : Function.Even v := by
    intro x
    simp only [v, hilbertPV_even_of_odd hodd x]
  have hp := isHilbertPair_div_sub hf hc (hsupport L le_rfl)
  have hq : MemLp q 2 volume := hp.memLp_right
  have hr : MemLp r 2 volume := by
    apply (hq.comp_measurePreserving (Measure.measurePreserving_neg volume)).neg.ae_eq
    apply Eventually.of_forall
    intro x
    simp only [q, r, Function.comp_def, Pi.neg_apply, hvEven x,
      show -x - L = -(x + L) by cas,
      div_neg, neg_neg]
  have hsum :
      (∫ x in Ioo 0 L, q x ^ 2) + (∫ x in Ioo 0 L, r x ^ 2) ≤
        ∫ x, (f x / (x - L)) ^ 2 := by
    rw [← hp.integral_sq_eq, integral_eq_integral_Ioi_add_reflection hq.integrable_sq,
      ← integral_add hq.integrable_sq.integrableOn hr.integrable_sq.integrableOn]
    have hpoint (x : ℝ) : q x ^ 2 + q (-x) ^ 2 = q x ^ 2 + r x ^ 2 := by
      simp only [q, r, hvEven x, show -x - L = -(x + L) by cas, div_neg, neg_sq]
    simp_rw [hpoint]
    apply setIntegral_mono_set
      (hq.integrable_sq.add hr.integrable_sq).integrableOn
      (Eventually.of_forall fun x ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))
      (Eventually.of_forall fun _ hx ↦ hx.1)
  have hvint : IntegrableOn v (Ioo 0 L) :=
    ((IsHilbertPair.of_lipschitzWith_compactSupport hf hc).memLp_right.restrict _).integrable
      (by norm_num) |>.sub (integrable_const _)
  have hmean : (∫ x in Ioo 0 L, v x) = -L * (c + hilbertPV f L) := by
    have hderiv : ∀ x, HasDerivAt (fun y ↦ u y - hilbertPV f L * y) (v x) x :=
      fun x ↦ (hu x).sub (hasDerivAt_const_mul _)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le).mpr hvint)
    rw [intervalIntegral.integral_of_le hL.le, integral_Ioc_eq_integral_Ioo,
      hu0, huL] at h
    simpa only [mul_zero, sub_zero] using h.trans (by ring)
  have hw : MemLp (fun x : ℝ ↦ x + L) 2 (volume.restrict (Ioo 0 L)) := by
    apply MemLp.of_bound (by fun_prop) (2 * L)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (add_pos hx.1 hL)]
    linarith [hx.2]
  have hweight : (∫ x in Ioo (0 : ℝ) L, (x + L) ^ 2) = 7 / 3 * L ^ 3 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL.le]
    cas
  have hproduct : (∫ x in Ioo 0 L, r x * (x + L)) = -L * (c + hilbertPV f L) := by
    rw [← hmean]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    exact div_mul_cancel₀ (v x) (add_pos hx.1 hL).ne'
  have hcs := (abs_integral_le_integral_abs (μ := volume.restrict (Ioo 0 L))
    (f := fun x ↦ r x * (x + L))).trans
    (integral_abs_mul_le_sqrt_integral_sq (hr.restrict _) hw)
  have hsq := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    |>.mpr hcs
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg _),
    Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg _), hproduct, hweight] at hsq
  have hexterior : 3 / (7 * L) * (c + hilbertPV f L) ^ 2 ≤
      ∫ x in Ioo 0 L, r x ^ 2 := by
    have hpos : 0 < 7 / 3 * L ^ 3 := by positivity
    apply (mul_le_mul_iff_left₀ hpos).mp
    have heq : (3 / (7 * L) * (c + hilbertPV f L) ^ 2) * (7 / 3 * L ^ 3) =
        (-L * (c + hilbertPV f L)) ^ 2 := by
      generalize hilbertPV f L = z
      cas using hL.ne'
    rw [heq]
    exact hsq
  linarith

/-- Local quadratic vanishing and compact Lipschitz regularity put the second
coordinate quotient in every `Lᵖ`. No regularity at the support endpoints is needed. -/
theorem memLp_div_sq_of_lipschitzWith_local_quadratic_bound
    {f : ℝ → ℝ} {K : ℝ≥0} {r B : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hr : 0 < r)
    (hlocal : ∀ x, |x| ≤ r → |f x| ≤ B * x ^ 2) (p : ENNReal) :
    MemLp (fun x ↦ f x / x ^ 2) p (volume : Measure ℝ) := by
  have hzero : f 0 = 0 := by
    have hz := hlocal 0 (by simpa using hr.le)
    apply abs_eq_zero.mp
    exact le_antisymm (by simpa only [zero_pow two_ne_zero, mul_zero] using hz) (abs_nonneg _)
  have hcompact : HasCompactSupport (fun x ↦ f x / x ^ 2) := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using hc.mul_right (f' := fun x ↦ (x ^ 2)⁻¹)
  apply hcompact.memLp_of_bound
    (hf.continuous.measurable.div (measurable_id.pow_const 2)).aestronglyMeasurable
    (max B ((K : ℝ) / r))
  apply Eventually.of_forall
  intro x
  by_cases hx : x = 0
  · simp only [hx, hzero, zero_div, norm_zero]
    exact le_trans (by positivity : 0 ≤ (K : ℝ) / r) (le_max_right _ _)
  have hxabs : 0 < |x| := abs_pos.mpr hx
  by_cases hxr : |x| ≤ r
  · apply le_trans _ (le_max_left _ _)
    rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
    apply (div_le_iff₀ (pow_pos hxabs 2)).mpr
    simpa only [sq_abs] using hlocal x hxr
  · have hnorm : ‖f x‖ ≤ (K : ℝ) * |x| := by
      simpa only [hzero, sub_zero, Real.norm_eq_abs] using hf.norm_sub_le x 0
    have hfirst : ‖f x‖ / |x| ≤ (K : ℝ) := (div_le_iff₀ hxabs).mpr hnorm
    rw [norm_div, norm_pow, Real.norm_eq_abs, pow_two, div_mul_eq_div_div]
    exact ((div_le_div_of_nonneg_right hfirst hxabs.le).trans
      (div_le_div_of_nonneg_left K.coe_nonneg hr (le_of_not_ge hxr))).trans
        (le_max_right _ _)

/-- A perturbation that agrees with an odd cubic near the origin has the second
quotient needed by (4.19) and the sharp Hilbert estimate. This matches differences
of locally odd Hermite cubics whose linear coefficients agree. -/
theorem memLp_div_sq_of_lipschitzWith_locally_cubic
    {f : ℝ → ℝ} {K : ℝ≥0} {r a : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hr : 0 < r)
    (hcubic : ∀ x, |x| ≤ r → f x = a * x ^ 3) (p : ENNReal) :
    MemLp (fun x ↦ f x / x ^ 2) p (volume : Measure ℝ) := by
  apply memLp_div_sq_of_lipschitzWith_local_quadratic_bound hf hc hr
    (B := |a| * r) _ p
  intro x hx
  calc
    |f x| = |a| * |x| ^ 3 := by rw [hcubic x hx, abs_mul, abs_pow]
    _ = (|a| * |x|) * x ^ 2 := by rw [← sq_abs x]; ring
    _ ≤ (|a| * r) * x ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (abs_nonneg a)) (sq_nonneg x)

end PDE.Analysis
