/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import PDE.Spaces.Sobolev.Inequalities.Hardy.Classical
import CAS.ExactTactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Smooth One-Dimensional Hardy Inequality in `Lᵖ`

The classical one-dimensional Hardy inequality

`∫ x in ε..R, |u x| ^ p * x ^ (-p) ≤ (p / (p - 1)) ^ p * ∫ x in ε..R, |u' x| ^ p`

holds for real `p > 1`, `0 < ε < R`, and `C¹` functions satisfying `u ε = 0`.
Only the left endpoint is fixed: integration by parts produces a nonnegative
boundary term at `R`, which is retained in the exact identity and discarded
only when deriving the inequality.

Compact support inside the positive half-line then supplies such an interval
and gives the half-line inequality on the smooth core. The density extension
to the completed space is `Hardy.FiniteExponentCompletion`.

## Main results

* `hardy_interval_lp_identity`, `hardy_interval_lp`: the identity and the inequality on
  `[ε, R]` with `u ε = 0`, constant `(p/(p-1))^p`.
* `hardy_Ioi_lp_of_support_subset_Ioo`, `hardy_Ioi_lp_of_hasCompactSupport`: the half-line
  inequality for `C¹` functions compactly supported in `(0, ∞)`.

## Implementation notes

The inequality is extracted from the identity by the pointwise Young inequality
`p a^{p-1} b ≤ (p-1) c a^p + c^{-(p-1)} b^p` with `a = |u|/x`, `b = |u'|`, and the scaling
parameter `c = (p-1)/p`. This choice absorbs the left-hand side and produces the constant
`(p/(p-1))^p` directly, without a separate optimization step.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988, Chapter IX, for Hardy's inequality in integral form.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Hardy

open Set MeasureTheory
open scoped ENNReal

/-- The chain rule for `|u|^p`, `p > 1`. -/
private theorem deriv_abs_rpow_comp {u : ℝ → ℝ} {p : ℝ} (hp : 1 < p) (hu : Differentiable ℝ u)
    (x : ℝ) : deriv (fun y ↦ |u y| ^ p) x = p * |u x| ^ (p - 2) * u x * deriv u x := by
  simpa only [Function.comp_def, mul_assoc] using
    ((hasDerivAt_abs_rpow (u x) hp).comp x (hu x).hasDerivAt).deriv

/--
The integration-by-parts identity behind the finite-interval `Lᵖ` Hardy
inequality. The right-endpoint contribution is retained, so only `u ε = 0`
is required.
-/
theorem hardy_interval_lp_identity
    {u : ℝ → ℝ} {ε R p : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hp : 1 < p) (hu : ContDiff ℝ 1 u) (huε : u ε = 0) :
    (p - 1) * (∫ x in ε..R, |u x| ^ p * x ^ (-p)) +
        |u R| ^ p * R ^ (1 - p) =
      p * ∫ x in ε..R,
        (|u x| ^ (p - 2) * u x) * deriv u x * x ^ (1 - p) := by
  have hxpos : ∀ x ∈ uIcc ε R, 0 < x := fun x hx ↦ hε.trans_le (uIcc_of_le hεR.le ▸ hx).1
  have hU : ContDiff ℝ 1 fun x ↦ |u x| ^ p := by simpa [Real.norm_eq_abs] using hu.norm_rpow hp
  have hWeightDeriv (x : ℝ) (hx : x ∈ uIcc ε R) :
      HasDerivAt (fun y : ℝ ↦ y ^ (1 - p)) ((1 - p) * x ^ (-p)) x := by
    have hx0 : 0 < x := hxpos x hx
    cas
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ (hU.differentiable one_ne_zero x).hasDerivAt) hWeightDeriv
    ((hU.continuous_deriv le_rfl).intervalIntegrable _ _)
    (continuousOn_const.mul (continuousOn_id.rpow_const fun x hx ↦
      Or.inl (hxpos x hx).ne')).intervalIntegrable
  have hleft : ∫ x in ε..R, |u x| ^ p * ((1 - p) * x ^ (-p)) =
      (1 - p) * ∫ x in ε..R, |u x| ^ p * x ^ (-p) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with x
    ring
  have hright : ∫ x in ε..R, deriv (fun y ↦ |u y| ^ p) x * x ^ (1 - p) =
      p * ∫ x in ε..R, (|u x| ^ (p - 2) * u x) * deriv u x * x ^ (1 - p) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with x
    rw [deriv_abs_rpow_comp hp (hu.differentiable one_ne_zero)]
    ring
  rw [hleft, hright, huε, abs_zero, Real.zero_rpow (zero_lt_one.trans hp).ne', zero_mul,
    sub_zero] at hparts
  linarith

private theorem scaled_young
    {a b p c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 < p) (hc : 0 < c) :
    p * a ^ (p - 1) * b ≤
      (p - 1) * c * a ^ p + c ^ (-(p - 1)) * b ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  -- weighted AM-GM with weights `(p - 1)/p`, `1/p` at `c a^p` and `c^{-(p-1)} b^p`
  have h := Real.geom_mean_le_arith_mean2_weighted (div_nonneg (sub_pos.2 hp).le hp0.le)
    (one_div_nonneg.2 hp0.le) (by positivity : 0 ≤ c * a ^ p)
    (by positivity : 0 ≤ c ^ (-(p - 1)) * b ^ p) (by field_simp; ring)
  rw [Real.mul_rpow hc.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul ha, ← Real.rpow_mul hb, ← Real.rpow_mul hc.le, mul_mul_mul_comm,
    ← Real.rpow_add hc, show (p - 1) / p + -(p - 1) * (1 / p) = 0 by ring,
    show p * ((p - 1) / p) = p - 1 by field_simp, show p * (1 / p) = 1 by field_simp,
    Real.rpow_zero, Real.rpow_one, one_mul] at h
  calc p * a ^ (p - 1) * b = p * (a ^ (p - 1) * b) := mul_assoc _ _ _
    _ ≤ p * ((p - 1) / p * (c * a ^ p) + 1 / p * (c ^ (-(p - 1)) * b ^ p)) := by gcongr
    _ = _ := by field_simp

private theorem abs_hardy_integrand
    {z v x p : ℝ} (hx : 0 < x) (hp : 1 < p) :
    |(|z| ^ (p - 2) * z) * v * x ^ (1 - p)| =
      (|z| / x) ^ (p - 1) * |v| := by
  have hzpow :
      |z| ^ (p - 2) * |z| = |z| ^ (p - 1) := by
    calc
      |z| ^ (p - 2) * |z| =
          |z| ^ (p - 2) * |z| ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = |z| ^ ((p - 2) + 1) := by
        rw [Real.rpow_add' (abs_nonneg z) (by linarith)]
      _ = |z| ^ (p - 1) := by
        congr 1
        ring_nf
  have hxpow :
      x ^ (1 - p) = (x⁻¹) ^ (p - 1) := by
    convert Real.rpow_neg_eq_inv_rpow x (p - 1) using 1
    ring_nf
  rw [abs_mul, abs_mul, abs_mul]
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) _)]
  rw [abs_of_pos (Real.rpow_pos_of_pos hx _), hzpow, hxpow]
  rw [div_eq_mul_inv, Real.mul_rpow (abs_nonneg z) (inv_nonneg.mpr hx.le)]
  ring_nf

private theorem hardy_interval_lp_scaled
    {u : ℝ → ℝ} {ε R p : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hp : 1 < p) (hu : ContDiff ℝ 1 u) (huε : u ε = 0) :
    (∫ x in ε..R, |u x| ^ p * x ^ (-p)) ≤
      (((p - 1) / p) ^ (-p)) * ∫ x in ε..R, |deriv u x| ^ p := by
  set c := (p - 1) / p with hc_def
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hc : 0 < c := div_pos (sub_pos.2 hp) hp0
  have hxpos : ∀ x ∈ uIcc ε R, 0 < x := fun x hx ↦ hε.trans_le (uIcc_of_le hεR.le ▸ hx).1
  have hrpow (q : ℝ) : ContinuousOn (fun x : ℝ ↦ x ^ q) (uIcc ε R) :=
    continuousOn_id.rpow_const fun x hx ↦ Or.inl (hxpos x hx).ne'
  have hU : ContDiff ℝ 1 fun x ↦ |u x| ^ p := by simpa [Real.norm_eq_abs] using hu.norm_rpow hp
  -- the integrand of `hardy_interval_lp_identity` is `p⁻¹ (|u|^p)' x^{1-p}`, hence continuous
  have hg : (fun x ↦ (|u x| ^ (p - 2) * u x) * deriv u x * x ^ (1 - p)) =
      fun x ↦ p⁻¹ * deriv (fun y ↦ |u y| ^ p) x * x ^ (1 - p) := by
    ext x
    rw [deriv_abs_rpow_comp hp (hu.differentiable one_ne_zero)]
    field_simp
  have hgi : IntervalIntegrable (fun x ↦ (|u x| ^ (p - 2) * u x) * deriv u x * x ^ (1 - p))
      volume ε R := by
    rw [hg]
    exact ((continuous_const.mul (hU.continuous_deriv le_rfl)).continuousOn.mul
      (hrpow _)).intervalIntegrable
  have hFi : IntervalIntegrable (fun x ↦ |u x| ^ p * x ^ (-p)) volume ε R :=
    (hU.continuous.continuousOn.mul (hrpow _)).intervalIntegrable
  have hGi : IntervalIntegrable (fun x ↦ |deriv u x| ^ p) volume ε R :=
    ((hu.continuous_deriv le_rfl).abs.rpow_const fun _ ↦ Or.inr hp0.le).intervalIntegrable _ _
  -- the pointwise Young inequality with `a = |u|/x`, `b = |u'|`
  have hpoint : ∀ x ∈ Icc ε R, p * ((|u x| ^ (p - 2) * u x) * deriv u x * x ^ (1 - p)) ≤
      (p - 1) * c * (|u x| ^ p * x ^ (-p)) + c ^ (-(p - 1)) * |deriv u x| ^ p := fun x hx ↦ by
    have hx := hxpos x (Icc_subset_uIcc hx)
    have hy := scaled_young (div_nonneg (abs_nonneg (u x)) hx.le) (abs_nonneg (deriv u x)) hp hc
    have hratio : (|u x| / x) ^ p = |u x| ^ p * x ^ (-p) := by
      rw [Real.div_rpow (abs_nonneg _) hx.le, Real.rpow_neg hx.le, div_eq_mul_inv]
    rw [hratio] at hy
    calc _ ≤ p * |(|u x| ^ (p - 2) * u x) * deriv u x * x ^ (1 - p)| := by
          gcongr
          exact le_abs_self _
      _ = p * (|u x| / x) ^ (p - 1) * |deriv u x| := by
          rw [abs_hardy_integrand hx hp, mul_assoc]
      _ ≤ _ := hy
  have hint := intervalIntegral.integral_mono_on hεR.le (hgi.const_mul p)
    ((hFi.const_mul _).add (hGi.const_mul _)) hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hFi.const_mul _)
    (hGi.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  have hid := hardy_interval_lp_identity hε hεR hp hu huε
  have hbd : 0 ≤ |u R| ^ p * R ^ (1 - p) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (hε.trans hεR).le _)
  have habsorb : (p - 1) * (1 - c) = c := by
    rw [hc_def]
    cas
  -- absorb the left-hand side: `c ∫ F ≤ c^{-(p-1)} ∫ G`, and `c^{-(p-1)} = c c^{-p}`
  refine le_of_mul_le_mul_left ?_ hc
  rw [← mul_assoc, ← Real.rpow_one_add' hc.le (by linarith), show 1 + -p = -(p - 1) by ring]
  linear_combination hint + hid - (∫ x in ε..R, |u x| ^ p * x ^ (-p)) * habsorb + hbd

/--
The one-dimensional Hardy inequality on a positive finite interval.
Only the left endpoint is fixed; the right-endpoint term in
`hardy_interval_lp_identity` is nonnegative and can be discarded.
-/
theorem hardy_interval_lp
    {u : ℝ → ℝ} {ε R p : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hp : 1 < p) (hu : ContDiff ℝ 1 u) (huε : u ε = 0) :
    (∫ x in ε..R, |u x| ^ p * x ^ (-p)) ≤
      (p / (p - 1)) ^ p * ∫ x in ε..R, |deriv u x| ^ p := by
  simpa only [Real.rpow_neg_eq_inv_rpow, inv_div] using
    hardy_interval_lp_scaled hε hεR hp hu huε

/--
The `Lᵖ` Hardy inequality on the positive half-line for smooth data
supported in one positive compact interval. Derivative support follows from function support,
so both half-line integrals equal the
finite-interval integrals in `hardy_interval_lp`.
-/
theorem hardy_Ioi_lp_of_support_subset_Ioo
    {u : ℝ → ℝ} {ε R p : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hp : 1 < p) (hu : ContDiff ℝ 1 u)
    (hsupp : Function.support u ⊆ Set.Ioo ε R) :
    (∫ x in Set.Ioi (0 : ℝ), |u x| ^ p * x ^ (-p)) ≤
      (p / (p - 1)) ^ p *
        ∫ x in Set.Ioi (0 : ℝ), |deriv u x| ^ p := by
  have huε : u ε = 0 :=
    Function.notMem_support.mp fun hx ↦ (lt_irrefl ε) (hsupp hx).1
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hIntegral (v : ℝ → ℝ) (hv : Function.support v ⊆ Ioo ε R) (w : ℝ → ℝ) :
      (∫ x in Ioi (0 : ℝ), |v x| ^ p * w x) =
        ∫ x in ε..R, |v x| ^ p * w x := by
    rw [intervalIntegral.integral_of_le hεR.le]
    apply setIntegral_Ioi_eq_Ioc_of_support_subset hε.le
    exact ((Function.support_mul_subset_left _ _).trans
      (Function.support_comp_subset (g := fun y : ℝ ↦ |y| ^ p)
        (by simp [Real.zero_rpow hp0]) v)).trans hv
  have hderiv : (∫ x in Ioi (0 : ℝ), |deriv u x| ^ p) =
      ∫ x in ε..R, |deriv u x| ^ p := by
    simpa using hIntegral (deriv u) (PDE.support_deriv_subset_Ioo hsupp) (fun _ ↦ 1)
  rw [hIntegral u hsupp, hderiv]
  exact hardy_interval_lp hε hεR hp hu huε

/--
The half-line `Lᵖ` Hardy inequality on the natural smooth core.
Compact support inside `(0,∞)` supplies the finite interval used by the
integration-by-parts proof and localizes the derivative automatically.
-/
theorem hardy_Ioi_lp_of_hasCompactSupport
    {u : ℝ → ℝ} {p : ℝ} (hp : 1 < p) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    (hpos : tsupport u ⊆ Set.Ioi (0 : ℝ)) :
    (∫ x in Set.Ioi (0 : ℝ), |u x| ^ p * x ^ (-p)) ≤
      (p / (p - 1)) ^ p *
        ∫ x in Set.Ioi (0 : ℝ), |deriv u x| ^ p := by
  obtain ⟨ε, R, hε, hεR, hsuppTop⟩ :=
    exists_Ioo_bounds_tsupport_of_subset_Ioi hcompact hpos
  have hsupp : Function.support u ⊆ Set.Ioo ε R :=
    (subset_tsupport u).trans hsuppTop
  exact hardy_Ioi_lp_of_support_subset_Ioo
    hε hεR hp hu hsupp

end SobolevSpace.Hardy
