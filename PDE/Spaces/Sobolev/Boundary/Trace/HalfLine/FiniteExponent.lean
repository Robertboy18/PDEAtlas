/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Finite-exponent endpoint trace estimate

We prove the one-dimensional endpoint estimate underlying the
`W^{1,p}` trace theorem for `1 ≤ p < ∞`. For a compactly supported `C¹`
real-valued function on the line,

`|f(0)|^p ≤ (p - 1) ∫₀∞ |f|^p + ∫₀∞ |f'|^p`.

At `p = 1`, the estimate follows by integrating `f'` on the positive half-line.
For `p > 1`, the proof differentiates `|f|^p`, applies the fundamental theorem
of calculus, and uses Young's inequality with conjugate exponents.

For functions with values in any real normed space, a norming functional at
`f 0` reduces the endpoint bound to the scalar estimate. This argument does
not differentiate the norm or require the target space to be complete.

Integrated over tangential slices in `Trace.HalfSpace.FiniteExponent`, the estimate gives the
flat-boundary estimate (1) in step 1 of the proof of Evans §5.5, Theorem 1, with explicit
constants. Evans's proof of (1) also differentiates `|u|^p` and applies Young's inequality; we
use Mathlib's `Real.young_inequality_of_nonneg`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, proof of Theorem 1, step 1, estimate (1), p. 272.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Trace.HalfLine

open MeasureTheory Set

private theorem weighted_young
    {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    p * a ^ (p - 1) * b ≤ (p - 1) * a ^ p + b ^ p := by
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hy := Real.young_inequality_of_nonneg
    (Real.rpow_nonneg ha (p - 1)) hb hpq.symm
  have hpow : (a ^ (p - 1)) ^ q = a ^ p := by
    rw [← Real.rpow_mul ha, hpq.sub_one_mul_conj]
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  calc
    p * a ^ (p - 1) * b = p * (a ^ (p - 1) * b) := by ring
    _ ≤ p * ((a ^ (p - 1)) ^ q / q + b ^ p / p) :=
      mul_le_mul_of_nonneg_left hy hp_pos.le
    _ = (p - 1) * a ^ p + b ^ p := by
      rw [hpow, mul_add, mul_div_cancel₀ _ hp_pos.ne']
      rw [show p * (a ^ p / q) = (p / q) * a ^ p by ring]
      rw [hpq.div_conj_eq_sub_one]

private theorem abs_deriv_abs_rpow_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {p : ℝ} (hp : 1 < p) (x : ℝ) :
    |deriv (fun y ↦ |f y| ^ p) x| ≤
      (p - 1) * |f x| ^ p + |deriv f x| ^ p := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hderiv :
      deriv (fun y ↦ |f y| ^ p) x =
        p * |f x| ^ (p - 2) * f x * deriv f x := by
    exact ((hasDerivAt_abs_rpow (f x) hp).comp x
      (hdiff x).hasDerivAt).deriv
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  by_cases hx : f x = 0
  · simp [hderiv, hx, Real.zero_rpow hp_pos.ne',
      Real.rpow_nonneg (abs_nonneg _) p]
  · have habs_pos : 0 < |f x| := abs_pos.mpr hx
    have hrpow :
        |f x| ^ (p - 2) * |f x| = |f x| ^ (p - 1) := by
      rw [← Real.rpow_add_one habs_pos.ne']
      congr 1
      ring
    rw [hderiv, abs_mul, abs_mul, abs_mul, abs_of_pos hp_pos,
      Real.abs_rpow_of_nonneg (abs_nonneg _), abs_abs]
    rw [show p * |f x| ^ (p - 2) * |f x| * |deriv f x| =
      p * (|f x| ^ (p - 2) * |f x|) * |deriv f x| by ring, hrpow]
    exact weighted_young hp (abs_nonneg _) (abs_nonneg _)

/--
Finite-exponent endpoint trace estimate on the positive half-line: for a compactly supported
`C¹` function `f : ℝ → ℝ` and real `p ≥ 1`,

`|f(0)|^p ≤ (p - 1) ∫₀∞ |f|^p + ∫₀∞ |f'|^p`.
-/
theorem endpoint_abs_rpow_le_integral_add_integral
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {p : ℝ} (hp : 1 ≤ p) :
    |f 0| ^ p ≤
      (p - 1) * (∫ x in Ioi (0 : ℝ), |f x| ^ p) +
        (∫ x in Ioi (0 : ℝ), |deriv f x| ^ p) := by
  rcases hp.eq_or_lt with rfl | hp
  · have hftc := HasCompactSupport.integral_Ioi_deriv_eq hf hfc (0 : ℝ)
    simpa [Real.norm_eq_abs, hftc] using
      norm_integral_le_integral_norm
        (μ := volume.restrict (Ioi (0 : ℝ))) (f := deriv f)
  let g : ℝ → ℝ := fun x ↦ |f x| ^ p
  have hgSmooth : ContDiff ℝ 1 g := by
    simpa [g, Real.norm_eq_abs] using hf.norm_rpow hp
  have hp_ne : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hgSupport : HasCompactSupport g := by
    simpa [g] using hfc.abs.rpow_const hp_ne
  have hftc := HasCompactSupport.integral_Ioi_deriv_eq
    (f := g) hgSmooth hgSupport (0 : ℝ)
  have hderivInt : IntegrableOn (deriv g) (Ioi (0 : ℝ)) :=
    (hgSmooth.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
      hgSupport.deriv |>.integrableOn
  have hgInt : IntegrableOn g (Ioi (0 : ℝ)) :=
    hgSmooth.continuous.integrable_of_hasCompactSupport hgSupport |>.integrableOn
  have hdfContinuous : Continuous (fun x ↦ |deriv f x| ^ p) :=
    (hf.continuous_deriv (by norm_num)).abs.rpow_const
      (fun _ ↦ Or.inr (le_trans (by norm_num) hp.le))
  have hdfSupport : HasCompactSupport (fun x ↦ |deriv f x| ^ p) :=
    hfc.deriv.abs.rpow_const hp_ne
  have hdfInt : IntegrableOn (fun x ↦ |deriv f x| ^ p) (Ioi (0 : ℝ)) :=
    hdfContinuous.integrable_of_hasCompactSupport hdfSupport |>.integrableOn
  have hmajorantInt :
      IntegrableOn (fun x ↦ (p - 1) * g x + |deriv f x| ^ p) (Ioi (0 : ℝ)) :=
    hgInt.const_mul (p - 1) |>.add hdfInt
  have hpointwise :
      ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
        |deriv g x| ≤ (p - 1) * g x + |deriv f x| ^ p := by
    filter_upwards with x
    exact abs_deriv_abs_rpow_le hf hp x
  calc
    |f 0| ^ p = -∫ x in Ioi (0 : ℝ), deriv g x := by
      symm
      simpa [g] using congrArg Neg.neg hftc
    _ ≤ |∫ x in Ioi (0 : ℝ), deriv g x| := neg_le_abs _
    _ ≤ ∫ x in Ioi (0 : ℝ), |deriv g x| := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (μ := volume.restrict (Ioi (0 : ℝ))) (f := deriv g)
    _ ≤ ∫ x in Ioi (0 : ℝ),
        ((p - 1) * g x + |deriv f x| ^ p) := by
      exact integral_mono_ae hderivInt.norm hmajorantInt hpointwise
    _ = (p - 1) * (∫ x in Ioi (0 : ℝ), |f x| ^ p) +
        (∫ x in Ioi (0 : ℝ), |deriv f x| ^ p) := by
      rw [integral_add (hgInt.const_mul (p - 1)) hdfInt,
        integral_const_mul]

/-- The bound `‖f 0‖ ^ p ≤ (p - 1) ∫₀∞ ‖f‖^p + ∫₀∞ ‖f'‖^p` for a compactly supported `C¹`
function `f` with values in a real normed space and real `p ≥ 1`. The integrals are
real-valued; no completeness of the target or differentiability of its norm is required. -/
theorem endpoint_norm_rpow_le_integral_add_integral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {p : ℝ} (hp : 1 ≤ p) :
    ‖f 0‖ ^ p ≤
      (p - 1) * (∫ x in Ioi (0 : ℝ), ‖f x‖ ^ p) +
        (∫ x in Ioi (0 : ℝ), ‖deriv f x‖ ^ p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨L, hL, hLf⟩ := exists_dual_vector'' ℝ (f 0)
  have hvalue : L (f 0) = ‖f 0‖ := by simpa using hLf
  have hLnorm (y : F) : ‖L y‖ ≤ ‖y‖ := by
    calc
      ‖L y‖ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  have hfInt : IntegrableOn (fun x ↦ ‖f x‖ ^ p) (Ioi (0 : ℝ)) :=
    (hf.continuous.norm.rpow_const (fun _ ↦ Or.inr hp_pos.le)).integrable_of_hasCompactSupport
      (hfc.norm.rpow_const hp_pos.ne') |>.integrableOn
  have hdfInt : IntegrableOn (fun x ↦ ‖deriv f x‖ ^ p) (Ioi (0 : ℝ)) :=
    ((hf.continuous_deriv (by norm_num)).norm.rpow_const
      (fun _ ↦ Or.inr hp_pos.le)).integrable_of_hasCompactSupport
        (hfc.deriv.norm.rpow_const hp_pos.ne') |>.integrableOn
  have hIntegral (u : ℝ → F)
      (hu : IntegrableOn (fun x ↦ ‖u x‖ ^ p) (Ioi (0 : ℝ))) :
      (∫ x in Ioi (0 : ℝ), |L (u x)| ^ p) ≤
        ∫ x in Ioi (0 : ℝ), ‖u x‖ ^ p := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) hu
    filter_upwards with x
    exact Real.rpow_le_rpow (abs_nonneg _)
      (by simpa only [Real.norm_eq_abs] using hLnorm (u x)) hp_pos.le
  have hderiv : deriv (L ∘ f) = L ∘ deriv f := by
    funext x
    exact (L.hasFDerivAt.comp_hasDerivAt x
      ((hf.differentiable (by norm_num)) x).hasDerivAt).deriv
  -- A single norming functional recovers the endpoint norm exactly.
  have hscalar := endpoint_abs_rpow_le_integral_add_integral
    (L.contDiff.comp hf) (hfc.comp_left L.map_zero) hp
  have hbound : ‖f 0‖ ^ p ≤
      (p - 1) * (∫ x in Ioi (0 : ℝ), |L (f x)| ^ p) +
        (∫ x in Ioi (0 : ℝ), |L (deriv f x)| ^ p) := by
    simpa only [hderiv, Function.comp_apply, hvalue, abs_of_nonneg (norm_nonneg _)]
      using hscalar
  exact hbound.trans (add_le_add
    (mul_le_mul_of_nonneg_left (hIntegral f hfInt) (sub_nonneg.mpr hp))
    (hIntegral (deriv f) hdfInt))

end Trace.HalfLine
end SobolevSpace
