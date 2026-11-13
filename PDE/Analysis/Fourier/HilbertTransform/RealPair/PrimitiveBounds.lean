/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.QuotientBounds
public import PDE.Spaces.Sobolev.Inequalities.Hardy.PrimitiveDomain
import CAS.ExactTactic

/-!
# Velocity remainders in the differentiated equation

For the spectral pair `(q, v_x)`, the principal-value bridge identifies
the continuous gradient. The fundamental theorem of calculus and weighted
Cauchy–Schwarz then give the two endpoint remainders that Chen, Hou and Huang estimate
before (12.5) in their supplementary material (Section 12.1).

The squared estimates keep the exact constants `1/5` and `1/3`. The energy
versions use only the positive weight comparisons and integrability, with no
pointwise bound on the Hilbert output.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  supplementary material (in the same PDF), Section 12.1, the estimates before (12.5), and
  Section 10.1, Lemma 10.1, (10.1). <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

open Filter MeasureTheory Set PDE.Analysis SobolevSpace.Hardy
open scoped NNReal

noncomputable section

namespace PDE.Analysis

/-- The origin remainder of a Hilbert velocity is controlled by the
second vorticity quotient. This applies to the time-differentiated pair. -/
theorem origin_velocity_remainder_sq_le
    {q v vX : ℝ → ℝ} {K : ℝ≥0} {L x : ℝ}
    (hpair : IsHilbertPair q vX) (hvX : Continuous vX)
    (hq : LipschitzWith K q) (hc : HasCompactSupport q) (hodd : Function.Odd q)
    (hsupport : ∀ y, L ≤ y → q y = 0)
    (hsecond : MemLp (fun y ↦ q y / y ^ 2) 2 volume)
    (hv : ∀ y, HasDerivAt v (vX y) y) (hv0 : v 0 = 0)
    (hx : 0 < x) (hxL : x ≤ L) :
    (v x - vX 0 * x) ^ 2 ≤
      x ^ 5 / 5 * ∫ y in Ioo 0 L, (q y / y ^ 2) ^ 2 := by
  have hpv := hpair.eq_hilbertPV_of_lipschitzWith_compactSupport hvX hq hc
  subst vX
  have hp := isHilbertPair_div_sq hq hc hodd hsecond
  have hd : ∀ y, HasDerivAt (fun z ↦ v z - hilbertPV q 0 * z)
      (hilbertPV q y - hilbertPV q 0) y :=
    fun y ↦ (hv y).sub (hasDerivAt_const_mul _)
  have hz : (fun z ↦ v z - hilbertPV q 0 * z) 0 = 0 := by simp [hv0]
  have hb := primitive_sq_div_pow_le_integral 2 hd hz hp.memLp_right hx
  norm_num only at hb
  have hm :
      (∫ y in Ioo 0 x, ((hilbertPV q y - hilbertPV q 0) / y ^ 2) ^ 2) ≤
        ∫ y in Ioo 0 L, ((hilbertPV q y - hilbertPV q 0) / y ^ 2) ^ 2 :=
    setIntegral_mono_set hp.memLp_right.integrable_sq.integrableOn
      (.of_forall fun y ↦ sq_nonneg _) (.of_forall fun _ hy ↦ ⟨hy.1, hy.2.trans_le hxL⟩)
  have hn := hm.trans (integral_origin_divided_difference_sq_le hq hc hodd hsupport hsecond)
  have hs := hb.trans (div_le_div_of_nonneg_right hn (by norm_num : (0 : ℝ) ≤ 5))
  have hm' := (div_le_iff₀ (pow_pos hx 5)).mp hs
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hm'

/-- Reflection about the support endpoint gives the second velocity remainder.
The full quotient isometry retains both reflected input weights. -/
theorem endpoint_velocity_remainder_sq_le
    {q v vX : ℝ → ℝ} {K : ℝ≥0} {L x : ℝ}
    (hpair : IsHilbertPair q vX) (hvX : Continuous vX)
    (hq : LipschitzWith K q) (hc : HasCompactSupport q) (hodd : Function.Odd q)
    (hsupport : ∀ y, L ≤ y → q y = 0)
    (hv : ∀ y, HasDerivAt v (vX y) y) (hxL : x < L) :
    (v x - v L - vX L * (x - L)) ^ 2 ≤
      (L - x) ^ 3 / 3 *
        ∫ y in Ioo 0 L, (q y / (y - L)) ^ 2 + (q y / (y + L)) ^ 2 := by
  have hpv := hpair.eq_hilbertPV_of_lipschitzWith_compactSupport hvX hq hc
  subst vX
  let w : ℝ → ℝ := fun y ↦ v (L - y) - v L + hilbertPV q L * y
  let wX : ℝ → ℝ := fun y ↦ -hilbertPV q (L - y) + hilbertPV q L
  have hw : ∀ y, HasDerivAt w (wX y) y := by
    intro y
    have hd := ((hv (L - y)).comp y ((hasDerivAt_id y).const_sub L)).sub_const (v L)
    simpa only [w, wX, Function.comp_def, mul_neg, mul_one] using
      hd.fun_add (hasDerivAt_const_mul _)
  have hw0 : w 0 = 0 := by simp [w]
  have hp := isHilbertPair_div_sub hq hc (hsupport L le_rfl)
  have hquot (y : ℝ) :
      wX y / y ^ 1 = (hilbertPV q (L - y) - hilbertPV q L) / (L - y - L) := by
    simp only [wX, pow_one, show L - y - L = -y by cas, div_neg]
    rw [show -hilbertPV q (L - y) + hilbertPV q L =
      -(hilbertPV q (L - y) - hilbertPV q L) by
        generalize hilbertPV q (L - y) = r, hilbertPV q L = s
        cas, neg_div]
  have hwq : MemLp (fun y ↦ wX y / y ^ 1) 2 volume := by
    apply (hp.memLp_right.comp_measurePreserving
      (Measure.measurePreserving_sub_left volume L)).ae_eq
    exact Eventually.of_forall fun y ↦ (hquot y).symm
  have hb := primitive_sq_div_pow_le_integral 1 hw hw0 hwq (sub_pos.mpr hxL)
  norm_num only [pow_one] at hb
  have hm :
      (∫ y in Ioo 0 (L - x), (wX y / y) ^ 2) ≤ ∫ y, (wX y / y) ^ 2 :=
    setIntegral_le_integral (by simpa only [pow_one] using hwq.integrable_sq)
      (.of_forall fun y ↦ sq_nonneg _)
  have heq :
      (∫ y, (wX y / y) ^ 2) =
        ∫ y in Ioo 0 L, (q y / (y - L)) ^ 2 + (q y / (y + L)) ^ 2 := by
    simp only [pow_one] at hquot
    simp_rw [hquot]
    rw [integral_sub_left_eq_self
      (fun y ↦ ((hilbertPV q y - hilbertPV q L) / (y - L)) ^ 2) volume L, hp.integral_sq_eq,
      integral_div_sub_sq_eq_Ioo hq hc hodd hsupport]
  rw [heq] at hm
  have hs := hb.trans (div_le_div_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 3))
  have hm' := (div_le_iff₀ (pow_pos (sub_pos.mpr hxL) 3)).mp hs
  have hwx : w (L - x) = v x - v L - hilbertPV q L * (x - L) := by
    dsimp only [w]
    rw [sub_sub_cancel]
    generalize v x = z, v L = zL, hilbertPV q L = r
    cas
  rw [hwx] at hm'
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hm'

/-- The origin factor `κ₁(x) = √(x³/(5a))` follows from a weight floor
`a/x⁴ ≤ φ`. Chen–Hou–Huang take `a = 1.15`. -/
theorem origin_velocity_remainder_le_weighted_energy
    {q v vX φ : ℝ → ℝ} {K : ℝ≥0} {L x a : ℝ}
    (hpair : IsHilbertPair q vX) (hvX : Continuous vX)
    (hq : LipschitzWith K q) (hc : HasCompactSupport q) (hodd : Function.Odd q)
    (hsupport : ∀ y, L ≤ y → q y = 0)
    (hsecond : MemLp (fun y ↦ q y / y ^ 2) 2 volume)
    (hv : ∀ y, HasDerivAt v (vX y) y) (hv0 : v 0 = 0)
    (hx : 0 < x) (hxL : x ≤ L) (ha : 0 < a)
    (hφ : ∀ y ∈ Ioo 0 L, a / y ^ 4 ≤ φ y)
    (henergy : IntegrableOn (fun y ↦ q y ^ 2 * φ y) (Ioo 0 L)) :
    |v x - vX 0 * x| ≤
      x * √(x ^ 3 / (5 * a)) * √(∫ y in Ioo 0 L, q y ^ 2 * φ y) := by
  have hm : a * (∫ y in Ioo 0 L, (q y / y ^ 2) ^ 2) ≤
      ∫ y in Ioo 0 L, q y ^ 2 * φ y := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hsecond.integrable_sq.integrableOn.const_mul a) henergy
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have heq : a * (q y / y ^ 2) ^ 2 = q y ^ 2 * (a / y ^ 4) := by
      generalize q y = z
      cas using hy.1.ne'
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hφ y hy) (sq_nonneg _)
  have hnorm : (∫ y in Ioo 0 L, (q y / y ^ 2) ^ 2) ≤
      (∫ y in Ioo 0 L, q y ^ 2 * φ y) / a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hm)
  have hb := origin_velocity_remainder_sq_le hpair hvX hq hc hodd hsupport hsecond hv hv0 hx hxL
  have hs := hb.trans (mul_le_mul_of_nonneg_left hnorm
    (by positivity : 0 ≤ x ^ 5 / (5 : ℝ)))
  have heq :
      x ^ 5 / 5 * ((∫ y in Ioo 0 L, q y ^ 2 * φ y) / a) =
        (x ^ 5 / (5 * a)) * (∫ y in Ioo 0 L, q y ^ 2 * φ y) := by
    generalize (∫ y in Ioo 0 L, q y ^ 2 * φ y) = E
    cas using ha.ne'
  rw [heq] at hs
  have hsqrt := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (by positivity : 0 ≤ x ^ 5 / (5 * a))] at hsqrt
  have hfactor : √(x ^ 5 / (5 * a)) = x * √(x ^ 3 / (5 * a)) := by
    rw [show x ^ 5 / (5 * a) = x ^ 2 * (x ^ 3 / (5 * a)) by cas using ha.ne',
      Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]
  rwa [hfactor] at hsqrt

/-- The endpoint factor `κ₂(x) = √((L-x)/(3a))` uses the full reflected
endpoint weight. Chen–Hou–Huang take `a = 0.0085`. -/
theorem endpoint_velocity_remainder_le_weighted_energy
    {q v vX φ : ℝ → ℝ} {K : ℝ≥0} {L x a : ℝ}
    (hpair : IsHilbertPair q vX) (hvX : Continuous vX)
    (hq : LipschitzWith K q) (hc : HasCompactSupport q) (hodd : Function.Odd q)
    (hsupport : ∀ y, L ≤ y → q y = 0)
    (hv : ∀ y, HasDerivAt v (vX y) y) (hxL : x < L) (ha : 0 < a)
    (hφ : ∀ y ∈ Ioo 0 L, a / (y - L) ^ 2 + a / (y + L) ^ 2 ≤ φ y)
    (henergy : IntegrableOn (fun y ↦ q y ^ 2 * φ y) (Ioo 0 L)) :
    |v x - v L - vX L * (x - L)| ≤
      (L - x) * √((L - x) / (3 * a)) *
        √(∫ y in Ioo 0 L, q y ^ 2 * φ y) := by
  have hleft := memLp_div_sub_of_lipschitzWith_zero hq hc (hsupport L le_rfl) 2
  have hzero : q (-L) = 0 := by rw [hodd L, hsupport L le_rfl, neg_zero]
  have hright : MemLp (fun y ↦ q y / (y + L)) 2 volume := by
    simpa only [sub_neg_eq_add] using memLp_div_sub_of_lipschitzWith_zero hq hc hzero 2
  have hm : a * (∫ y in Ioo 0 L, (q y / (y - L)) ^ 2 + (q y / (y + L)) ^ 2) ≤
      ∫ y in Ioo 0 L, q y ^ 2 * φ y := by
    rw [← integral_sq_mul_endpoint_weight (hleft.restrict _) (hright.restrict _)]
    apply integral_mono_ae
      (integrable_sq_mul_endpoint_weight (hleft.restrict _) (hright.restrict _) a) henergy
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact mul_le_mul_of_nonneg_left (hφ y hy) (sq_nonneg _)
  have hnorm : (∫ y in Ioo 0 L, (q y / (y - L)) ^ 2 + (q y / (y + L)) ^ 2) ≤
      (∫ y in Ioo 0 L, q y ^ 2 * φ y) / a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hm)
  have hb := endpoint_velocity_remainder_sq_le hpair hvX hq hc hodd hsupport hv hxL
  have hs := hb.trans (mul_le_mul_of_nonneg_left hnorm
    (by positivity : 0 ≤ (L - x) ^ 3 / (3 : ℝ)))
  have heq :
      (L - x) ^ 3 / 3 * ((∫ y in Ioo 0 L, q y ^ 2 * φ y) / a) =
        ((L - x) ^ 3 / (3 * a)) * (∫ y in Ioo 0 L, q y ^ 2 * φ y) := by
    generalize (∫ y in Ioo 0 L, q y ^ 2 * φ y) = E
    cas using ha.ne'
  rw [heq] at hs
  have hsqrt := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (by positivity : 0 ≤ (L - x) ^ 3 / (3 * a))] at hsqrt
  have hfactor :
      √((L - x) ^ 3 / (3 * a)) = (L - x) * √((L - x) / (3 * a)) := by
    rw [show (L - x) ^ 3 / (3 * a) = (L - x) ^ 2 * ((L - x) / (3 * a)) by
      cas using ha.ne', Real.sqrt_mul (sq_nonneg (L - x)), Real.sqrt_sq_eq_abs,
      abs_of_pos (sub_pos.mpr hxL)]
  rwa [hfactor] at hsqrt

end PDE.Analysis
