/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.WeakBound
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import PDE.Analysis.MeasureTheory.Lp.Continuous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Pointwise control from a singular derivative energy

If `g` is the weak derivative of a continuous function, write its primitive as
the integral of `(g(y) / y) * y`. Cauchy–Schwarz gives a factor of `x^(3/2)`,
rather than the usual `x^(1/2)`. This extra decay is useful when comparing
profiles that share their value at the origin.

Only the weighted derivative needs to be square integrable near zero.
Classical differentiability at the origin is not required.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

/-- The inverse-square derivative weight gives a cubic bound on squared
increments from the origin. The derivative is interpreted weakly. -/
theorem sq_sub_zero_le_integral_div_sq
    {f g : ℝ → ℝ} {L x : ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f)
    (hx : 0 < x) (hxL : x ≤ L)
    (hg : MemLp (fun y ↦ g y / y) 2 (volume.restrict (Ioo 0 L))) :
    (f x - f 0) ^ 2 ≤
      (x ^ 3 / 3) * ∫ y in Ioo 0 L, (g y / y) ^ 2 := by
  have hsub : Ioo (0 : ℝ) x ⊆ Ioo 0 L :=
    Ioo_subset_Ioo le_rfl hxL
  have hgx : MemLp (fun y ↦ g y / y) 2 (volume.restrict (Ioo 0 x)) :=
    hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hy : MemLp (fun y : ℝ ↦ y) 2 (volume.restrict (Ioo 0 x)) :=
    continuous_id.continuousOn.memLp_of_subset_isCompact isCompact_Icc
      measurableSet_Ioo Ioo_subset_Icc_self
  have hftc : (∫ y in Ioo 0 x, g y) = f x - f 0 := by
    rw [← hweak.intervalIntegral_eq_sub hf 0 x,
      intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo]
  have hprod :
      (∫ y in Ioo 0 x, (g y / y) * y) = f x - f 0 := by
    rw [← hftc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact div_mul_cancel₀ _ hy.1.ne'
  have hcs := integral_abs_mul_le_sqrt_integral_sq hgx hy
  have habs : |f x - f 0| ≤
      √(∫ y in Ioo 0 x, (g y / y) ^ 2) *
        √(∫ y in Ioo 0 x, y ^ 2) := by
    rw [← hprod]
    exact abs_integral_le_integral_abs.trans hcs
  have hmoment : (∫ y in Ioo 0 x, y ^ 2) = x ^ 3 / 3 := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hx.le, integral_pow]
    norm_num
  have henergy : (∫ y in Ioo 0 x, (g y / y) ^ 2) ≤
      ∫ y in Ioo 0 L, (g y / y) ^ 2 :=
    setIntegral_mono_set hg.integrable_sq
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) (Filter.Eventually.of_forall hsub)
  have hsquared := mul_self_le_mul_self (abs_nonneg _) habs
  rw [← sq, ← sq] at hsquared
  rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
    Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _), sq_abs, hmoment] at hsquared
  calc
    (f x - f 0) ^ 2 ≤
        (∫ y in Ioo 0 x, (g y / y) ^ 2) * (x ^ 3 / 3) := hsquared
    _ ≤ (∫ y in Ioo 0 L, (g y / y) ^ 2) * (x ^ 3 / 3) :=
      mul_le_mul_of_nonneg_right henergy (by positivity)
    _ = _ := mul_comm _ _

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
