/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import PDE.Spaces.Sobolev.Localization.IntervalSupport
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import CAS.ExactTactic

/-!
# Power-weighted Hardy inequality on a finite interval

Integration by parts against the derivative of `x^(1-2s)`, followed by Cauchy–Schwarz,
gives `(2s-1)² ∫ u² x^(-2s) ≤ 4 ∫ (u')² x^(2-2s)` for `s > 1/2`.
Both endpoint values vanish, and the interval lies strictly to the right of zero.
The classical inequality is the specialization `s = 1`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Hardy

open Set MeasureTheory
open scoped ENNReal

/-- Exact weighted Hardy integration-by-parts identity on `[epsilon,R]`. -/
theorem weighted_hardy_interval_identity
    {u : ℝ → ℝ} {ε R s : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hu : ContDiff ℝ 1 u)
    (huε : u ε = 0) (huR : u R = 0) :
    (2 * s - 1) * (∫ x in ε..R, u x ^ 2 * x ^ (-2 * s)) =
      2 * ∫ x in ε..R,
        (u x * x ^ (-s)) * (deriv u x * x ^ (1 - s)) := by
  have hxpos : ∀ x ∈ Set.uIcc ε R, 0 < x := fun x hx ↦
    hε.trans_le (Set.uIcc_of_le hεR.le ▸ hx).1
  have hWeightDeriv (x : ℝ) (hx : x ∈ Set.uIcc ε R) :
      HasDerivAt (fun y : ℝ ↦ y ^ (1 - 2 * s)) ((1 - 2 * s) * x ^ (-2 * s)) x := by
    cas using hxpos x hx
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ (((hu.differentiable (by norm_num)) x).hasDerivAt.pow 2).congr_deriv
      (show _ = 2 * u x * deriv u x by ring)) hWeightDeriv
    ((continuous_const.mul hu.continuous).mul
      (hu.continuous_deriv (by norm_num))).continuousOn.intervalIntegrable
    (continuousOn_const.mul (continuousOn_id.rpow_const fun x hx ↦
      Or.inl (hxpos x hx).ne')).intervalIntegrable
  have hleft : (∫ x in ε..R, u x ^ 2 * ((1 - 2 * s) * x ^ (-2 * s))) =
      (1 - 2 * s) * ∫ x in ε..R, u x ^ 2 * x ^ (-2 * s) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ ↦ by ring
  have hright : (∫ x in ε..R, (2 * u x * deriv u x) * x ^ (1 - 2 * s)) =
      2 * ∫ x in ε..R, (u x * x ^ (-s)) * (deriv u x * x ^ (1 - s)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [show 1 - 2 * s = -s + (1 - s) by ring, Real.rpow_add (hxpos x hx)]
    ring
  simp only [Pi.pow_apply] at hparts
  rw [hleft, hright, huε, huR] at hparts
  linear_combination -hparts

/-- If `c X = 2 I` with `c > 0` and `|I| ≤ √X √Y`, then `c² X ≤ 4 Y`. -/
private theorem sq_mul_le_of_mul_eq {c X Y I : ℝ} (hc : 0 < c) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hI : c * X = 2 * I) (hIle : |I| ≤ √X * √Y) : c ^ 2 * X ≤ 4 * Y := by
  have hkey : c * √X ≤ 2 * √Y := by
    rcases hX.eq_or_lt with rfl | hXpos
    · rw [Real.sqrt_zero, mul_zero]
      positivity
    refine le_of_mul_le_mul_right ?_ (Real.sqrt_pos.2 hXpos)
    rw [mul_assoc, Real.mul_self_sqrt hX, hI]
    linarith [le_abs_self I]
  calc c ^ 2 * X = (c * √X) ^ 2 := by rw [mul_pow, Real.sq_sqrt hX]
    _ ≤ (2 * √Y) ^ 2 := pow_le_pow_left₀ (mul_nonneg hc.le (Real.sqrt_nonneg _)) hkey 2
    _ = 4 * Y := by rw [mul_pow, Real.sq_sqrt hY]; norm_num

/--
Weighted Hardy inequality on a positive finite interval.  It is stated
multiplied out, without division by `(2s-1)^2`, so that it can be iterated
through the singular radial commutator hierarchy without case splits.
-/
theorem weighted_hardy_interval
    {u : ℝ → ℝ} {ε R s : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hs : 1 / 2 < s) (hu : ContDiff ℝ 1 u)
    (huε : u ε = 0) (huR : u R = 0) :
    (2 * s - 1) ^ 2 * (∫ x in ε..R, u x ^ 2 * x ^ (-2 * s)) ≤
      4 * ∫ x in ε..R, (deriv u x) ^ 2 * x ^ (2 - 2 * s) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc ε R)
  have hxpos : ∀ x ∈ Set.Icc ε R, 0 < x := fun x hx ↦ hε.trans_le hx.1
  have hpowCont (a : ℝ) : ContinuousOn (fun x : ℝ ↦ x ^ a) (Set.Icc ε R) :=
    continuousOn_id.rpow_const fun x hx ↦ Or.inl (hxpos x hx).ne'
  have hLp {H : ℝ → ℝ} (hH : ContinuousOn H (Set.Icc ε R)) : MemLp H 2 μ :=
    (memLp_two_iff_integrable_sq ((hH.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc)).2 ((hH.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  have hsq (v : ℝ → ℝ) {a b : ℝ} (hab : a * 2 = b) :
      (∫ x in ε..R, (v x * x ^ a) ^ 2) = ∫ x in ε..R, v x ^ 2 * x ^ b :=
    intervalIntegral.integral_congr fun x hx ↦ by
      simp only [mul_pow, ← hab, Real.rpow_mul (hxpos x (Set.uIcc_of_le hεR.le ▸ hx)).le,
        Real.rpow_two]
  have hnonneg (v : ℝ → ℝ) (t : ℝ) : 0 ≤ ∫ x in ε..R, v x ^ 2 * x ^ t :=
    intervalIntegral.integral_nonneg hεR.le fun x hx ↦
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hxpos x hx).le _)
  refine sq_mul_le_of_mul_eq (by linarith) (hnonneg _ _) (hnonneg _ _)
    (weighted_hardy_interval_identity hε hεR hu huε huR) ?_
  rw [← hsq u (a := -s) (b := -2 * s) (by ring),
    ← hsq (deriv u) (a := 1 - s) (b := 2 - 2 * s) (by ring)]
  refine (intervalIntegral.abs_integral_le_integral_abs hεR.le).trans ?_
  simpa [μ, intervalIntegral.integral_of_le hεR.le] using
    integral_abs_mul_le_sqrt_integral_sq (hLp (hu.continuous.continuousOn.mul (hpowCont (-s))))
      (hLp ((hu.continuous_deriv (by norm_num)).continuousOn.mul (hpowCont (1 - s))))

/-- Power-weighted Hardy inequality on the positive half-line for a `C¹` function
supported in `(ε,R)`, with `ε > 0`. Its derivative has the same support localization. -/
theorem weighted_hardy_Ioi_of_support_subset_Ioo
    {u : ℝ → ℝ} {ε R s : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hs : 1 / 2 < s) (hu : ContDiff ℝ 1 u)
    (hsupp : Function.support u ⊆ Set.Ioo ε R) :
    (2 * s - 1) ^ 2 *
        (∫ x in Set.Ioi (0 : ℝ), u x ^ 2 * x ^ (-2 * s)) ≤
      4 * ∫ x in Set.Ioi (0 : ℝ),
        (deriv u x) ^ 2 * x ^ (2 - 2 * s) := by
  have huε : u ε = 0 :=
    Function.notMem_support.mp fun hx ↦ (lt_irrefl ε) (hsupp hx).1
  have huR : u R = 0 :=
    Function.notMem_support.mp fun hx ↦ (lt_irrefl R) (hsupp hx).2
  have hIntegral (v : ℝ → ℝ) (hv : Function.support v ⊆ Ioo ε R) (t : ℝ) :
      (∫ x in Ioi (0 : ℝ), v x ^ 2 * x ^ t) =
        ∫ x in ε..R, v x ^ 2 * x ^ t := by
    rw [intervalIntegral.integral_of_le hεR.le]
    apply setIntegral_Ioi_eq_Ioc_of_support_subset hε.le
    exact ((Function.support_mul_subset_left _ _).trans
      (Function.support_comp_subset (g := fun y : ℝ ↦ y ^ 2) (by simp) v)).trans hv
  rw [hIntegral u hsupp, hIntegral (deriv u) (PDE.support_deriv_subset_Ioo hsupp)]
  exact weighted_hardy_interval hε hεR hs hu huε huR

end SobolevSpace.Hardy
